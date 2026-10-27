module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4T4
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F5T2
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Transport
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIBasic
public import CFSG.Sporadic.HN
public import CFSG.Sporadic.HN.Local.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.HN
  CFSG.Sporadic.HN.Local

theorem isF5Centralizer_map {H H' : Type} [Group H] [Group H'] (f : H ≃* H') {E : Subgroup H}
    (h : TwoHS.IsF5Centralizer H E) : TwoHS.IsF5Centralizer H' (E.map (f : H →* H')) where
  toIsHSCover := h.toIsHSCover.map f
  index_eq_two := by rw [Subgroup.index_map_equiv]; exact h.index_eq_two
  exists_outer_involution := by
    obtain ⟨v, hv, hv2⟩ := h.exists_outer_involution
    refine ⟨f v, fun hm => hv ?_, by rw [← map_pow, hv2, map_one]⟩
    obtain ⟨x, hx, hxv⟩ := Subgroup.mem_map.1 hm
    exact (f.injective hxv) ▸ hx

theorem exists_isF5Centralizer_of_nonempty_mulEquiv {X G : Type} [Group X] [Group G] {z₀ : X}
    {z : G} (hc : Nonempty (centralizer ({z} : Set G) ≃* centralizer ({z₀} : Set X)))
    (h : ∃ E : Subgroup (centralizer ({z₀} : Set X)),
      TwoHS.IsF5Centralizer (centralizer ({z₀} : Set X)) E) :
    ∃ E : Subgroup (centralizer ({z} : Set G)),
      TwoHS.IsF5Centralizer (centralizer ({z} : Set G)) E := by
  obtain ⟨e⟩ := hc
  obtain ⟨E, hE⟩ := h
  exact ⟨_, isF5Centralizer_map e.symm hE⟩

section Conjugate

variable {X : Type} [Group X] {t z : X}

theorem exists_isF5Centralizer_of_isConj (h : IsConj t z)
    (ht : ∃ E : Subgroup (centralizer ({t} : Set X)),
      TwoHS.IsF5Centralizer (centralizer ({t} : Set X)) E) :
    ∃ E : Subgroup (centralizer ({z} : Set X)),
      TwoHS.IsF5Centralizer (centralizer ({z} : Set X)) E := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  obtain ⟨E, hE⟩ := ht
  exact ⟨_, isF5Centralizer_map (TwoHS.centralizerMulEquiv (MulAut.conj c) (by simpa using hc)) hE⟩

theorem not_isComponent_centralizer_of_isConj [Finite X] (h : IsConj t z)
    (ht : IsExtraspecialPlusByA5WrTwo (centralizer ({t} : Set X)))
    (K : Subgroup (centralizer ({z} : Set X))) : ¬ CFSG.IsComponent K := by
  intro hK
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  obtain ⟨Q, hQ, hQ'⟩ := ht
  let e : centralizer ({t} : Set X) ≃* centralizer ({z} : Set X) :=
    TwoHS.centralizerMulEquiv (MulAut.conj c) (by simpa using hc)
  haveI : CFSG.IsExtraspecial 2 ↥Q := hQ'.plus.1
  exact CFSG.ComponentClassification.OutcomeLocal.not_isComponent_of_selfCentralizing (p := 2) hQ
    (CFSG.IsExtraspecial.isPGroup 2 ↥Q) hQ'.centralizer_le (K.map e.symm.toMonoidHom)
    (CFSG.LocalCores.isComponent_map_mulEquiv e.symm hK)

end Conjugate

section Facts

set_option linter.unusedSectionVars false


open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore in
theorem hn_isF5Centralizer_t2 :
    ∃ E : Subgroup (centralizer ({hnT2} : Set (Carrier .HN))),
      TwoHS.IsF5Centralizer (centralizer ({hnT2} : Set (Carrier .HN))) E := by
  have hc : Nonempty (centralizer ({hnEquivJ.symm aJ} : Set NativeSporadic.HN) ≃*
      centralizer ({aJ} : Set JH)) :=
    ⟨@TwoHS.centralizerMulEquiv NativeSporadic.HN JH Units.instGroup (Subgroup.toGroup _)
      hnEquivJ _ _ (hnEquivJ.apply_symm_apply aJ)⟩
  have h6 := @exists_isF5Centralizer_of_nonempty_mulEquiv JH NativeSporadic.HN
    (Subgroup.toGroup _) Units.instGroup aJ (hnEquivJ.symm aJ) hc TwoHS.isF5Centralizer_C6
  exact exists_isF5Centralizer_of_isConj (X := Carrier .HN) isConj_hnT2_hnEquivJ_symm_aJ.symm h6

theorem hn_isExtraspecialPlusByA5WrTwo_t4 :
    IsExtraspecialPlusByA5WrTwo (centralizer ({hnT4} : Set (Carrier .HN))) :=
  SideF4.isExtraspecialPlusByA5WrTwo_centralizer_hnT4

theorem isConj_hnT2_of_component
    (z₀ : Carrier .HN) (hz₀ : orderOf z₀ = 2)
    (hK : ∃ K : Subgroup (centralizer ({z₀} : Set (Carrier .HN))), CFSG.IsComponent K) :
    IsConj (hnT2 : Carrier .HN) z₀ := by
  have hsq : z₀ ^ 2 = 1 := hz₀ ▸ pow_orderOf_eq_one z₀
  have hne : z₀ ≠ 1 := fun h => by simp [h] at hz₀
  haveI : Finite (Carrier .HN) := (fam_hn_simplicity).1
  rcases hn_involution_cover z₀ hsq hne with h | h
  · exact h
  · obtain ⟨K, hK⟩ := hK
    exact absurd hK (not_isComponent_centralizer_of_isConj (X := Carrier .HN) h
      hn_isExtraspecialPlusByA5WrTwo_t4 K)

theorem hn_isF5Centralizer_of_component (z₀ : Carrier .HN) (hz₀ : orderOf z₀ = 2)
    (hK : ∃ K : Subgroup (centralizer ({z₀} : Set (Carrier .HN))), CFSG.IsComponent K) :
    ∃ E : Subgroup (centralizer ({z₀} : Set (Carrier .HN))),
      TwoHS.IsF5Centralizer (centralizer ({z₀} : Set (Carrier .HN))) E :=
  exists_isF5Centralizer_of_isConj (X := Carrier .HN) (isConj_hnT2_of_component z₀ hz₀ hK)
    hn_isF5Centralizer_t2

theorem hn_isF5Type :
    IsF5Type (hnT2 : Carrier .HN) (hnT4 : Carrier .HN) where
  orderOf_a := orderOf_eq_prime hnT2_sq hnT2_ne_one
  orderOf_z := orderOf_eq_prime hnT4_sq hnT4_ne_one
  cent_a := hn_isF5Centralizer_t2
  cent_z := hn_isExtraspecialPlusByA5WrTwo_t4

theorem hn_sideFacts : HNSideFacts where
  finite := (fam_hn_simplicity).1
  isSimpleGroup := (fam_hn_simplicity).2.2
  isF5Type := ⟨hnT2, hnT4, hn_isF5Type⟩
  isF5Centralizer_of_component := hn_isF5Centralizer_of_component

end Facts

end CFSG.EvenSporadicStandard.HNRecog
