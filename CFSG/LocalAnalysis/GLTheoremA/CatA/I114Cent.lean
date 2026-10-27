module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Grp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

theorem three_dvd_of_centralizes {y : Y} (hy : orderOf y = 3) (L : Subgroup Y)
    (hnc : ∃ z ∈ L, z * y ≠ y * z) (a : ℤ) (ha : ∀ z ∈ L, z * y ^ a = y ^ a * z) :
    (3 : ℤ) ∣ a := by
  by_contra hdiv
  obtain ⟨k, hk⟩ : ∃ k : ℤ, a * k % 3 = 1 := by
    have : a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases this with h1 | h1
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
  have h3 : y ^ (a * k) = y := by
    have := zpow_mod_orderOf y (a * k)
    rw [hy] at this
    have e : a * k % ((3 : ℕ) : ℤ) = 1 := by exact_mod_cast hk
    rw [e, zpow_one] at this
    exact this.symm
  have hyk : (y ^ a) ^ k = y := by
    rw [← zpow_mul]
    exact h3
  obtain ⟨z, hz, hzy⟩ := hnc
  apply hzy
  have h2 : z * (y ^ a) ^ k = (y ^ a) ^ k * z :=
    Commute.zpow_right (show Commute z (y ^ a) from ha z hz) k
  rw [hyk] at h2
  exact h2

theorem mem_sup_of_normalizes {T P : Subgroup Y} (h : ∀ t ∈ T, t ∈ Subgroup.normalizer (P : Set Y)) :
    ∀ s ∈ T ⊔ P, ∃ t ∈ T, ∃ p ∈ P, s = t * p := by
  let Q : Subgroup Y :=
    { carrier := {s | ∃ t ∈ T, ∃ p ∈ P, s = t * p}
      mul_mem' := by
        rintro _ _ ⟨t₁, ht₁, p₁, hp₁, rfl⟩ ⟨t₂, ht₂, p₂, hp₂, rfl⟩
        have hn := h t₂⁻¹ (T.inv_mem ht₂)
        rw [Subgroup.mem_normalizer_iff] at hn
        have h1 : t₂⁻¹ * p₁ * t₂ ∈ P := by
          have := (hn p₁).1 hp₁
          simpa [inv_inv] using this
        refine ⟨t₁ * t₂, T.mul_mem ht₁ ht₂, (t₂⁻¹ * p₁ * t₂) * p₂, P.mul_mem h1 hp₂, ?_⟩
        group
      one_mem' := ⟨1, T.one_mem, 1, P.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨t, ht, p, hp, rfl⟩
        have hn := h t ht
        rw [Subgroup.mem_normalizer_iff] at hn
        refine ⟨t⁻¹, T.inv_mem ht, t * p⁻¹ * t⁻¹, ?_, ?_⟩
        · exact (hn p⁻¹).1 (P.inv_mem hp)
        · group }
  have hle : T ⊔ P ≤ Q :=
    sup_le (fun t ht => ⟨t, ht, 1, P.one_mem, by simp⟩)
      (fun p hp => ⟨1, T.one_mem, p, hp, by simp⟩)
  intro s hs
  exact hle hs

end CFSG.LocalAnalysis.GLTheoremA.I114
