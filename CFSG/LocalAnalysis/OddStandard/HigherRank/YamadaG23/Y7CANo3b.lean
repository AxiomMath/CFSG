module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CANo3a
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

private lemma seven_dvd_of_zpow_central {Γ : Type*} [Group Γ] {K : Subgroup Γ} {y : Γ} {a : ℤ}
    (hnot : ∃ k ∈ K, y * k ≠ k * y)
    (h7 : ∀ k ∈ K, y ^ 7 * k = k * y ^ 7)
    (ha : ∀ k ∈ K, y ^ a * k = k * y ^ a) : 7 ∣ a := by
  have h7mem : y ^ 7 ∈ Subgroup.centralizer (K : Set Γ) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => (h7 k hk).symm
  have hamem : y ^ a ∈ Subgroup.centralizer (K : Set Γ) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => (ha k hk).symm
  have hgcdmem : y ^ (Int.gcd a 7 : ℤ) ∈ Subgroup.centralizer (K : Set Γ) := by
    have hgcd : y ^ (Int.gcd a 7 : ℤ)
        = (y ^ a) ^ Int.gcdA a 7 * (y ^ (7 : ℤ)) ^ Int.gcdB a 7 := by
      simp only [Int.gcd_eq_gcd_ab, zpow_add, zpow_mul]
    rw [hgcd]
    exact mul_mem (Subgroup.zpow_mem _ hamem _)
      (Subgroup.zpow_mem _ (by simpa using h7mem) _)
  have hnotmem : y ∉ Subgroup.centralizer (K : Set Γ) := by
    rintro h
    obtain ⟨k, hk, hne⟩ := hnot
    exact hne (Subgroup.mem_centralizer_iff.mp h k hk).symm
  have hdiv : Int.gcd a 7 ∣ 7 :=
    Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right a 7)
  obtain hg | hg := (Nat.dvd_prime Nat.prime_seven).mp hdiv
  · exact (hnotmem (by simpa [hg] using hgcdmem)).elim
  · have h := Int.gcd_dvd_left a 7
    rw [hg] at h
    exact h

theorem y7c_seven_cube_dvd {Γ A : Type} [Group Γ] [Finite Γ] [Group A] [Finite A] (f : Γ →* A)
    {N K₁ K₂ K₃ : Subgroup Γ} (hK₁ : K₁ ≤ N) (hK₂ : K₂ ≤ N) (hK₃ : K₃ ≤ N)
    (h12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (h13 : ∀ a ∈ K₁, ∀ b ∈ K₃, a * b = b * a)
    (h23 : ∀ a ∈ K₂, ∀ b ∈ K₃, a * b = b * a)
    (hker₁ : ∀ n ∈ N, f n = 1 → ∀ k ∈ K₁, n * k = k * n)
    (hker₂ : ∀ n ∈ N, f n = 1 → ∀ k ∈ K₂, n * k = k * n)
    (hker₃ : ∀ n ∈ N, f n = 1 → ∀ k ∈ K₃, n * k = k * n)
    (hy₁ : ∃ y ∈ K₁, (∃ k ∈ K₁, y * k ≠ k * y) ∧ ∀ k ∈ K₁, y ^ 7 * k = k * y ^ 7)
    (hy₂ : ∃ y ∈ K₂, (∃ k ∈ K₂, y * k ≠ k * y) ∧ ∀ k ∈ K₂, y ^ 7 * k = k * y ^ 7)
    (hy₃ : ∃ y ∈ K₃, (∃ k ∈ K₃, y * k ≠ k * y) ∧ ∀ k ∈ K₃, y ^ 7 * k = k * y ^ 7) :
    7 ^ 3 ∣ Nat.card A := by
  obtain ⟨y₁, hy₁K, hy₁n, hy₁c⟩ := hy₁
  obtain ⟨y₂, hy₂K, hy₂n, hy₂c⟩ := hy₂
  obtain ⟨y₃, hy₃K, hy₃n, hy₃c⟩ := hy₃
  refine y7c_seven_cube_of_indep (u₁ := f y₁) (u₂ := f y₂) (u₃ := f y₃) ?_ ?_ ?_ ?_
  · simp only [← map_mul, h12 y₁ hy₁K y₂ hy₂K]
  · simp only [← map_mul, h13 y₁ hy₁K y₃ hy₃K]
  · simp only [← map_mul, h23 y₂ hy₂K y₃ hy₃K]
  · intro a b c habc
    have hy₁a : y₁ ^ a ∈ K₁ := Subgroup.zpow_mem _ hy₁K a
    have hy₂b : y₂ ^ b ∈ K₂ := Subgroup.zpow_mem _ hy₂K b
    have hz₃c : y₃ ^ c ∈ K₃ := Subgroup.zpow_mem _ hy₃K c
    have hnN : y₁ ^ a * y₂ ^ b * y₃ ^ c ∈ N :=
      mul_mem (mul_mem (hK₁ hy₁a) (hK₂ hy₂b)) (hK₃ hz₃c)
    have hfn : f (y₁ ^ a * y₂ ^ b * y₃ ^ c) = 1 := by
      rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow]
      exact habc
    have hc₁n : y₁ ^ a * y₂ ^ b * y₃ ^ c ∈ Subgroup.centralizer (K₁ : Set Γ) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => (hker₁ _ hnN hfn k hk).symm
    have hc₂n : y₁ ^ a * y₂ ^ b * y₃ ^ c ∈ Subgroup.centralizer (K₂ : Set Γ) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => (hker₂ _ hnN hfn k hk).symm
    have hc₃n : y₁ ^ a * y₂ ^ b * y₃ ^ c ∈ Subgroup.centralizer (K₃ : Set Γ) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => (hker₃ _ hnN hfn k hk).symm
    have hc₁₂ : y₂ ∈ Subgroup.centralizer (K₁ : Set Γ) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => h12 k hk y₂ hy₂K
    have hc₁₃ : y₃ ∈ Subgroup.centralizer (K₁ : Set Γ) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => h13 k hk y₃ hy₃K
    have hc₂₁ : y₁ ∈ Subgroup.centralizer (K₂ : Set Γ) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => (h12 y₁ hy₁K k hk).symm
    have hc₂₃ : y₃ ∈ Subgroup.centralizer (K₂ : Set Γ) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => h23 k hk y₃ hy₃K
    have hc₃₁ : y₁ ∈ Subgroup.centralizer (K₃ : Set Γ) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => (h13 y₁ hy₁K k hk).symm
    have hc₃₂ : y₂ ∈ Subgroup.centralizer (K₃ : Set Γ) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => (h23 y₂ hy₂K k hk).symm
    have hc₁ : y₁ ^ a ∈ Subgroup.centralizer (K₁ : Set Γ) := by
      have hd : y₂ ^ b * y₃ ^ c ∈ Subgroup.centralizer (K₁ : Set Γ) :=
        mul_mem (Subgroup.zpow_mem _ hc₁₂ b) (Subgroup.zpow_mem _ hc₁₃ c)
      have hdecomp : y₁ ^ a = (y₁ ^ a * y₂ ^ b * y₃ ^ c) * (y₂ ^ b * y₃ ^ c)⁻¹ := by
        group
      rw [hdecomp]
      exact mul_mem hc₁n (inv_mem hd)
    have hc₂ : y₂ ^ b ∈ Subgroup.centralizer (K₂ : Set Γ) := by
      have hdecomp : y₂ ^ b = (y₁ ^ a)⁻¹ * (y₁ ^ a * y₂ ^ b * y₃ ^ c) * (y₃ ^ c)⁻¹ := by
        group
      rw [hdecomp]
      exact mul_mem (mul_mem (inv_mem (Subgroup.zpow_mem _ hc₂₁ a)) hc₂n)
        (inv_mem (Subgroup.zpow_mem _ hc₂₃ c))
    have hc₃ : y₃ ^ c ∈ Subgroup.centralizer (K₃ : Set Γ) := by
      have hdecomp : y₃ ^ c = (y₁ ^ a * y₂ ^ b)⁻¹ * (y₁ ^ a * y₂ ^ b * y₃ ^ c) := by
        group
      rw [hdecomp]
      exact mul_mem (inv_mem (mul_mem (Subgroup.zpow_mem _ hc₃₁ a) (Subgroup.zpow_mem _ hc₃₂ b)))
        hc₃n
    exact ⟨seven_dvd_of_zpow_central hy₁n hy₁c
        (fun k hk => (Subgroup.mem_centralizer_iff.mp hc₁ k hk).symm),
      seven_dvd_of_zpow_central hy₂n hy₂c
        (fun k hk => (Subgroup.mem_centralizer_iff.mp hc₂ k hk).symm),
      seven_dvd_of_zpow_central hy₃n hy₃c
        (fun k hk => (Subgroup.mem_centralizer_iff.mp hc₃ k hk).symm)⟩

end CFSG.OddStandard.HigherRank.YamadaG23
