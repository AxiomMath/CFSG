module

public import CFSG.ClassicalInvolution.Asc77.AscT7AEnd

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem le_sigmaStarNorm_of_mem_dstarComp (hΩ : ConjInvariant Ω) {K M : Subgroup G} (hK : K ∈ Ω)
    (hM : M ∈ dstarComp Ω K) : M ≤ sigmaStarNorm Ω K := by
  intro x hx
  have hMΩ : M ∈ Ω := (T3.mem_dstarComp_symm hK hM).1
  have hxM : conjSub x M ∈ dstarComp Ω M := by
    rw [mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hx)]
    exact Relation.ReflTransGen.refl
  have h1 : x ∈ sigmaStarNorm Ω M := T7A.mem_sigmaStarNorm_of_conj hΩ hMΩ hxM
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hM)] at h1

theorem dstarConnected_of_generators (hΩ : ConjInvariant Ω)
    (htrans : ∀ A ∈ Ω, ∀ B ∈ Ω, ∃ g : G, conjSub g A = B) {K : Subgroup G} (hK : K ∈ Ω)
    (hgen : (⨆ M ∈ dstarComp Ω K, M) = ⊤) : T3.DStarConnected Ω := by
  refine T3.dstarConnected_of_pivot hK fun B hB => ?_
  obtain ⟨g, hg⟩ := htrans K hK B hB
  have hle : (⨆ M ∈ dstarComp Ω K, M) ≤ sigmaStarNorm Ω K :=
    iSup₂_le fun M hM => le_sigmaStarNorm_of_mem_dstarComp hΩ hK hM
  have hgN : g ∈ sigmaStarNorm Ω K := hle (by rw [hgen]; exact Subgroup.mem_top g)
  have h1 := (mem_sigmaStarNorm_iff.mp hgN K).mp Relation.ReflTransGen.refl
  rwa [hg] at h1

theorem le_iSup_dstarComp {K : Subgroup G} {S : Set (Subgroup G)} (hS : S ⊆ dstarComp Ω K) :
    (⨆ M ∈ S, M) ≤ ⨆ M ∈ dstarComp Ω K, M :=
  iSup₂_le fun M hM => le_iSup₂_of_le M (hS hM) le_rfl

section Edge

variable [Finite G]

theorem mem_omegaStarNbr_of_cyclic_two (hΩ : HypOmegaMod p f Ω) {K J T : Subgroup G}
    (hJ : J ∈ Ω) (hne : J ≠ K) (hTJ : T ≤ J) (hT2 : IsPGroup 2 T) (hTc : IsCyclic ↥T)
    (hcard : 2 * Nat.card T = 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2)
    (hTN : T ≤ Subgroup.normalizer (K : Set G)) : J ∈ omegaStarNbr Ω K := by
  obtain ⟨R, -, hRJ, hTR⟩ := exists_mem_RSet_ge hJ hT2 hTJ
  have hRcard := hΩ.natCard_isSylow2In hJ hRJ
  have hU : T ∈ USet Ω := mem_USet_of_natCard hJ hRJ hTR hTc (by rw [hRcard, ← hcard])
  exact ⟨hJ, hne, T, hU, hTJ, hTN⟩

theorem dstarAdj_of_cyclic_two (hΩ : HypOmegaMod p f Ω) {K J T : Subgroup G} (hJ : J ∈ Ω)
    (hne : J ≠ K) (hTJ : T ≤ J) (hT2 : IsPGroup 2 T) (hTc : IsCyclic ↥T)
    (hcard : 2 * Nat.card T = 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2)
    (hTN : T ≤ Subgroup.normalizer (K : Set G)) : dstarAdj Ω K J :=
  ⟨hJ, Or.inl (mem_omegaStarNbr_of_cyclic_two hΩ hJ hne hTJ hT2 hTc hcard hTN)⟩

end Edge

end CFSG.ClassicalInvolution.Asc77
