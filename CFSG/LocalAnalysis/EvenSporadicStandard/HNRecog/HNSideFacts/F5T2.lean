module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F5Outer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HNFactsProof
public import CFSG.Sporadic.HN.Local.Main
public import CFSG.Sporadic.HNOddCore.InvRow6

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.RankThree.PartOne.HNRed
  CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section C6


theorem isF5Centralizer_C6 : ∃ E : Subgroup C6, IsF5Centralizer C6 E := by
  have hd := coverData_aux t6C t6C_mem_ker t6C_ne_one t6C_central
  have hs := sign_core_aux t6C coe_t6C (MonoidHom.mem_ker.1 t6C_mem_ker) t6C_central
  exact ⟨Dsub.comap phi6,
    (hd.isHSCover hs.2).isF5Centralizer_of_sign hd.index_comap (hd.sign hs.1)⟩

end C6

end CFSG.EvenSporadicStandard.TwoHS

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.HN.Local

theorem card_centralizer_eq_of_isConj' {X : Type} [Group X] {a b : X} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set X)) = Nat.card (centralizer ({b} : Set X)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact Nat.card_congr
    (TwoHS.centralizerMulEquiv (MulAut.conj c) (by simpa using hc)).toEquiv

theorem card_centralizer_of_mulEquiv_apply {G J : Type} [Group G] [Group J] (e : G ≃* J) (z : G)
    (w : J) (h : e z = w) :
    Nat.card (centralizer ({z} : Set G)) = Nat.card (centralizer ({w} : Set J)) :=
  Nat.card_congr (TwoHS.centralizerMulEquiv e h).toEquiv

section Conj


theorem isConj_hnT2_hnEquivJ_symm_aJ :
    IsConj (hnT2 : NativeSporadic.HN) (hnEquivJ.symm aJ) := by
  have hsq : (hnEquivJ.symm aJ) ^ 2 = 1 := by
    rw [← map_pow, aJ_sq, map_one]
  have hne : hnEquivJ.symm aJ ≠ 1 := fun h => aJ_ne_one (by
    have := congrArg hnEquivJ h
    simpa using this)
  rcases hn_involution_cover _ hsq hne with h | h
  · exact h
  · exfalso
    have h1 := card_centralizer_eq_of_isConj' (X := NativeSporadic.HN) h
    have h3 := hn_card_centralizer_t4
    have h2 : Nat.card (centralizer ({hnEquivJ.symm aJ} : Set NativeSporadic.HN)) = 177408000 := by
      rw [@card_centralizer_of_mulEquiv_apply NativeSporadic.HN JH Units.instGroup
        (Subgroup.toGroup _) hnEquivJ _ aJ (hnEquivJ.apply_symm_apply aJ)]
      exact card_CJ_t6
    omega

end Conj

end CFSG.EvenSporadicStandard.HNRecog
