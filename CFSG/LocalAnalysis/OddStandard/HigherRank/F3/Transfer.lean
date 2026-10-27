module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Two

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

theorem ClassBShape.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ClassBShape A) : ClassBShape B := by
  obtain ⟨eZ⟩ := ComponentClassification.FooteLit.nonempty_quotient_fusionZStar_equiv e
  obtain ⟨τ, n, hm, hs⟩ := h
  exact ⟨τ, n, ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv eZ hm, hs⟩

theorem partialCentre_iff_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    PartialCentre A ↔ PartialCentre B := by
  obtain ⟨eZ⟩ := ComponentClassification.FooteLit.nonempty_quotient_fusionZStar_equiv e
  have hcard : Nat.card ↥(Open.fusionZStar B) = Nat.card ↥(Open.fusionZStar A) := by
    rw [← ComponentClassification.FooteLit.fusionZStar_map_mulEquiv e,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  have hM : Nat.card (Open.griessHopfMultiplier (B ⧸ Open.fusionZStar B)) =
      Nat.card (Open.griessHopfMultiplier (A ⧸ Open.fusionZStar A)) :=
    (Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eZ).toEquiv).symm
  unfold PartialCentre
  rw [hcard, hM]

theorem IsClassBMember.map_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    {J : Subgroup L} {u : L} (h : IsClassBMember L J u) :
    IsClassBMember L' (J.map e.toMonoidHom) (e u) := by
  have eJ : ↥J ≃* ↥(J.map e.toMonoidHom) := J.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨?_, Subgroup.mem_map_of_mem _ h.mem, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact h.orderOf_eq_two
  · intro hc
    apply h.not_mem_center
    have hc' : e u ∈ (Subgroup.center L).map (e : L →* L') := by
      rwa [Subgroup.map_center_eq e]
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hc'
    rwa [← e.injective hxe]
  · haveI := h.perfect
    exact Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  · have := h.subnormal.map e.toMonoidHom
    rwa [ComponentClassification.GSThmB.OddQuot.map_centralizer_singleton_equiv] at this
  · exact T23.isMTypeSchur_of_mulEquiv eJ h.mtype

@[expose] def HasCleanFullClassBMember (L : Type) [Group L] : Prop :=
  ∃ (J : Subgroup L) (u : L), IsClassBMember L J u ∧ ClassBShape ↥J ∧ ¬ PartialCentre ↥J ∧
    IsQuasisimple ↥J ∧ pPrimeCore 2 ↥J = ⊥

theorem HasCleanFullClassBMember.of_mulEquiv {L L' : Type} [Group L] [Group L']
    (e : L ≃* L') (h : HasCleanFullClassBMember L) : HasCleanFullClassBMember L' := by
  obtain ⟨J, u, hJ, hs, hp, hq, hO⟩ := h
  have eJ : ↥J ≃* ↥(J.map e.toMonoidHom) := J.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨J.map e.toMonoidHom, e u, hJ.map_mulEquiv e, ClassBShape.of_mulEquiv eJ hs, ?_,
    LocalCores.isQuasisimple_of_mulEquiv eJ hq, ?_⟩
  · exact fun h' => hp ((partialCentre_iff_of_mulEquiv eJ).mpr h')
  · have h1 := pPrimeCore_map_iso 2 eJ
    rw [hO, Subgroup.map_bot] at h1
    exact h1.symm

end CFSG.OddStandard.HigherRank.F3
