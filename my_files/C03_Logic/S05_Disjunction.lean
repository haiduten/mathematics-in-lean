import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  cases le_or_gt 0 x
  case inl h =>
    apply le_of_lt_or_eq
    right
    apply symm
    apply abs_of_nonneg h
  case inr h =>
    apply le_of_lt_or_eq
    left
    apply lt_abs.mpr
    right
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  cases le_or_gt 0 x
  case inl h =>
    apply le_abs.mpr
    right
    apply le_of_eq
    norm_num
  case inr h =>
    apply le_abs.mpr
    right
    apply le_of_eq
    norm_num

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases abs_cases x with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · -- x is pos
    rcases abs_cases y with ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩
    · -- y is pos
      rw[h₀, h₂]
      apply abs_le.mpr
      constructor <;> linarith
    · --y is neg
      rw[h₀, h₂]
      apply abs_le.mpr
      constructor <;> linarith
  · -- x is neg
    rcases abs_cases y with ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩
    · -- y is pos
      rw[h₀, h₂]
      apply abs_le.mpr
      constructor <;> linarith
    · --y is neg
      rw[h₀, h₂]
      apply abs_le.mpr
      constructor <;> linarith

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · -- x < |y| → x < y ∨ x < -y
    intro h
    rcases le_or_gt 0 y with hy | hy
    · -- 0 ≤ y
      left
      rw[abs_of_nonneg hy] at h
      exact h
    · -- y < 0
      right
      rw[abs_of_neg hy] at h
      exact h
  · -- x < y ∨ x < -y → x < |y|
    intro h
    rcases abs_cases y with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · -- y is pos
      rw[abs_of_nonneg h₂]
      rcases h with h | h
      · -- x < y
        assumption
      · -- x < -y
        apply lt_of_lt_of_le
        · exact h
        · apply neg_le_self_iff.mpr
          exact h₂
    · -- y is neg
      rw[abs_of_neg h₂]
      rcases h with h | h
      · apply lt_trans h
        apply lt_neg_self_iff.mpr
        exact h₂
      · assumption


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · -- |x| < y → -y < x ∧ x < y
    rcases le_or_gt 0 x with h | h
    · -- x is pos
      rw[abs_of_nonneg h]
      rintro h₁
      constructor
      · -- -y < x
        apply lt_of_lt_of_le
        apply neg_lt_zero.mpr
        apply lt_of_le_of_lt h h₁
        exact h
      · exact h₁
    · -- x is neg
      rw[abs_of_neg h]
      rintro h₁
      constructor
      linarith
      apply lt_trans
      apply lt_neg_self_iff.mpr h
      exact h₁
  · -- -y < x ∧ x < y → |x| < y
    rintro ⟨h₀, h₁⟩
    rcases le_or_gt 0 x with h | h
    · -- x is pos
      rw[abs_of_nonneg h]
      exact h₁
    · -- x is neg
      rw[abs_of_neg h]
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩; repeat have h₀ := pow_two_nonneg x; have h₁:= pow_two_nonneg y; linarith

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h: (x + 1) * (x - 1) = 0 := by linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h
  rcases h with h | h
  · right
    linarith
  · left
    linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h: (x + y) * (x - y) = 0 := by linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h
  rcases h with h | h
  · right
    linarith
  · left
    linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  apply sub_eq_zero.mpr at h
  have hg: x ^ 2 - 1  = (x + 1) * (x - 1) :=  by ring
  rw[hg] at h
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h
  rcases h with h | h
  · -- x + 1 = 0
    right
    apply sub_eq_zero.mp
    rw[sub_neg_eq_add]
    exact h
  · --  x - 1 = 0
    left
    apply sub_eq_zero.mp
    exact h


example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  apply sub_eq_zero.mpr at h
  have hg: x ^ 2 - y ^ 2  = (x + y) * (x - y) :=  by ring
  rw[hg] at h
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h
  rcases h with h | h
  · -- x + 1 = 0
    right
    apply sub_eq_zero.mp
    rw[sub_neg_eq_add]
    exact h
  · --  x - 1 = 0
    left
    apply sub_eq_zero.mp
    exact h
end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h
  by_cases h': P
  · right; exact h h'
  · left; assumption
