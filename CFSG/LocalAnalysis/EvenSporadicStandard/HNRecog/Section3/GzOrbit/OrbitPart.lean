module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem isConjOrbit_of_partition_compl {G : Type} [Group G] {K : Subgroup G} {N A T : Set G}
    {S : Fin 2 → Set G} (hS : IsOrbitPartition K N S) (h0 : Nat.card ↥(S 0) = 150)
    (h1 : Nat.card ↥(S 1) = 120) (hA : IsConjOrbit K A) (hAN : A ⊆ N) (hAcard : Nat.card ↥A = 120)
    (hT : ∀ k ∈ K, ∀ t ∈ T, k * t * k⁻¹ ∈ T) (hTN : T ⊆ N) (hTA : Disjoint T A)
    (hTne : T.Nonempty) : IsConjOrbit K T ∧ Nat.card ↥T = 150 := by
  obtain ⟨x, hx⟩ := hA.nonempty
  obtain ⟨i, hxi⟩ := hS.cover x (hAN hx)
  have hAeqS : A = S i := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨k, hk, hkxy⟩ := hA.transitive x hx y hy
      have hmem := (hS.orbit i).conj_mem k hk x hxi
      rwa [hkxy] at hmem
    · intro y hy
      obtain ⟨k, hk, hkxy⟩ := (hS.orbit i).transitive x hxi y hy
      have hmem := hA.conj_mem k hk x hx
      rwa [hkxy] at hmem
  have hcardi : Nat.card ↥(S i) = 120 := by rw [← hAeqS]; exact hAcard
  have hi_ne0 : i ≠ 0 := by
    intro h
    rw [h] at hcardi
    omega
  have hi : i = 1 := Fin.eq_one_of_ne_zero i hi_ne0
  have hAeq : A = S 1 := by rw [hAeqS, hi]
  obtain ⟨t₀, ht₀⟩ := hTne
  obtain ⟨j, hj⟩ := hS.cover t₀ (hTN ht₀)
  have hnotA₀ : t₀ ∉ A := (Set.disjoint_left.mp hTA) ht₀
  have hj0 : j = 0 := by
    by_contra hne0
    have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hne0
    exact hnotA₀ (by rw [hAeq, ← hj1]; exact hj)
  have ht₀S0 : t₀ ∈ S 0 := by rw [hj0] at hj; exact hj
  have hTsub : T ⊆ S 0 := by
    intro t ht
    obtain ⟨i', hi'⟩ := hS.cover t (hTN ht)
    have hnotA : t ∉ A := (Set.disjoint_left.mp hTA) ht
    have hi'0 : i' = 0 := by
      by_contra hne0
      have hi'1 : i' = 1 := Fin.eq_one_of_ne_zero i' hne0
      exact hnotA (by rw [hAeq, ← hi'1]; exact hi')
    rwa [hi'0] at hi'
  have hS0sub : S 0 ⊆ T := by
    intro s hs
    obtain ⟨k, hk, hkts⟩ := (hS.orbit 0).transitive t₀ ht₀S0 s hs
    have hmem := hT k hk t₀ ht₀
    rwa [hkts] at hmem
  have hTeq : T = S 0 := Set.Subset.antisymm hTsub hS0sub
  exact ⟨by rw [hTeq]; exact hS.orbit 0, by rw [hTeq]; exact h0⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
