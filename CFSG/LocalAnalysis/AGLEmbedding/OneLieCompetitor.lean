module

import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStarAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Hom

variable {G : Type} [Group G] [Finite G]

theorem exists_competitorHom_of_map_eq {p : ℕ} {H X : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hπJ : ((nclIn H X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K)
    {H' : Subgroup G} (hJH' : nclIn H X ≤ H') :
    ∃ φ : ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) →*
        K, Function.Surjective φ ∧ p.Coprime (Nat.card φ.ker) := by
  have hJH : nclIn H X ≤ H := nclIn_le_self H X
  set ρ := (QuotientGroup.mk' (primeComplementCore (G := H') p)).subgroupMap
    ((nclIn H X).subgroupOf H')
  let θ₀ : (nclIn H X).subgroupOf H' →* H :=
    MonoidHom.codRestrict (H'.subtype.comp ((nclIn H X).subgroupOf H').subtype) H
      (fun a => hJH a.2)
  let θ : (nclIn H X).subgroupOf H' →* H ⧸ primeComplementCore (G := H) p :=
    (QuotientGroup.mk' (primeComplementCore (G := H) p)).comp θ₀
  have hθK : ∀ a, θ a ∈ K := fun a =>
    hπJ ▸ Subgroup.mem_map_of_mem _ (show θ₀ a ∈ (nclIn H X).subgroupOf H from a.2)
  let ψ : (nclIn H X).subgroupOf H' →* K := θ.codRestrict K hθK
  have hψker : ∀ a, a ∈ ψ.ker ↔ ((a : H') : G) ∈ GLBPrimeCore p H := by
    intro a
    rw [MonoidHom.mem_ker, ← OneMemClass.coe_eq_one, MonoidHom.codRestrict_apply]
    exact mk'_primeComplementCore_eq_one_iff p (θ₀ a)
  have hψ : Function.Surjective ψ := by
    intro l
    obtain ⟨j, hj, hjl⟩ : (l : H ⧸ primeComplementCore (G := H) p) ∈
        ((nclIn H X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
      hπJ.symm ▸ l.2
    exact ⟨⟨⟨(j : G), hJH' hj⟩, hj⟩, Subtype.ext hjl⟩
  have hker : ρ.ker ≤ ψ.ker := by
    intro a ha
    have ha' : ((a : H') : G) ∈ GLBPrimeCore p H' := by
      rw [← mk'_primeComplementCore_eq_one_iff]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
    have hN := inf_glbPrimeCore_le_glbPrimeCore p hJH' ⟨a.2, ha'⟩
    rw [glbPrimeCore_nclIn] at hN
    exact (hψker a).mpr hN.2
  obtain ⟨φ, -, hφs, hφker⟩ := exists_surjective_comp_eq ρ
    ((QuotientGroup.mk' _).subgroupMap_surjective _) ψ hψ hker
  refine ⟨φ, hφs, ?_⟩
  have hι : Function.Injective (H'.subtype.comp ((nclIn H X).subgroupOf H').subtype) :=
    H'.subtype_injective.comp (Subgroup.subtype_injective _)
  refine Nat.Coprime.coprime_dvd_right ?_ ((glbPrimeCore_coprime p H).coprime_dvd_right
    (Subgroup.card_dvd_of_le (H := ψ.ker.map (H'.subtype.comp
      ((nclIn H X).subgroupOf H').subtype)) ?_))
  · rw [hφker, Subgroup.card_map_of_injective hι]
    exact Subgroup.card_map_dvd _ _
  · rintro _ ⟨a, ha, rfl⟩
    exact (hψker a).mp ha

end Hom

end CFSG.AGLEmbedding
