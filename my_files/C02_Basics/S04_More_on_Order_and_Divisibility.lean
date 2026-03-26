import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply ge_antisymm
  repeat
    apply max_le
    · apply le_max_right
    · apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · show min (min a b) c ≤ a
      have h₀ := min_le_left a b
      have h₁ := min_le_left (min a b) c
      exact le_trans h₁ h₀
    · show min (min a b) c ≤ min b c
      apply le_min
      · show min (min a b) c ≤ b
        have h₀ := min_le_right a b
        have h₁ := min_le_left (min a b) c
        exact le_trans h₁ h₀
      · exact min_le_right (min a b) c
  · apply le_min
    · apply le_min
      · exact min_le_left a (min b c)
      · show min a (min b c) ≤ b
        have h₀ := min_le_left b c
        have h₁ := min_le_right a (min b c)
        exact le_trans h₁ h₀
    · show min a (min b c) ≤ c
      have h₀ := min_le_right b c
      have h₁ := min_le_right a (min b c)
      exact le_trans h₁ h₀

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · show min a b + c ≤ a + c
    apply add_le_add_right
    exact min_le_left a b
  · show min a b + c ≤ b + c
    apply add_le_add_right
    exact min_le_right a b

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · exact aux a b c
  · show min (a + c) (b + c) ≤ min a b + c
    apply sub_le_iff_le_add.mp
    apply le_min
    · show min (a + c) (b + c) - c ≤ a
      apply sub_le_iff_le_add.mpr
      exact min_le_left (a + c) _
    · show min (a + c) (b + c) - c ≤ b
      apply sub_le_iff_le_add.mpr
      exact min_le_right _ (b + c)

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h1 := abs_add (a - b) b
  rw[sub_add_cancel] at h1
  exact sub_le_iff_le_add.mpr h1
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · show x ∣ y * (x * z) + x ^ 2
    apply dvd_add
    · show x ∣ y * (x * z)
      rw[←mul_assoc]
      apply dvd_mul_of_dvd_left
      apply dvd_mul_left
    · show x ∣ x ^ 2
      exact dvd_mul_left _ _
  · show x ∣ w ^ 2
    rw[(by ring: w^2 = w * w)]
    apply dvd_mul_of_dvd_left
    exact h

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.gcd_eq_iff.mpr
  constructor
  · exact gcd_dvd_right n m
  constructor
  · exact gcd_dvd_left n m
  intro c
  intro h₁
  intro h₂
  apply (dvd_gcd_iff c n m).mpr
  constructor
  exact h₂
  exact h₁
end
