module

public import CFSG.GH74.GLS.C3.Layer1.Th2L626P4

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.GH74.GLS.C3.Layer1.PumpCalc

section Pumpup

variable {G : Type} [Group G] [Finite G]

theorem trivial_of_commute_unb

    (I : L626Inputs) (hG : C3Hyp G) {x y : G} {K : Subgroup G} (hV : IsV2StarTriple x y K)
    (hK5 : HasL2Model (kBar K) (fun q => q = 5)) (hCx : pRank 2 ↥(CxK x K) = 2)
    {t u : G} {J : Subgroup G} (hunb : IsUnbalancingTriple t u J)
    {v : G} (hv2 : orderOf v = 2) (hvC : v ∈ CxK t J) (hvu : v * u = u * v)
    (hrk : pRank 2 ↥(centralizer ({v, u} : Set G)) = 4) {L : Subgroup G}
    (hlt : PumpUpLT 2 t J v L) :
    (t ∈ normalizer (L : Set G) ∧ Nonempty (kBar L ≃* kBar J)) ∧ IsUnbalancingTriple v u L := by
  have h625c1 : B_lemma625c1 :=
    b_lemma625c1_of_thm1 I.h610 I.h720 I.h14 I.h103 I.hL34 I.hL29 I.h102 I.hfm I.hfour
  have hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J := hunb.1.2
  obtain ⟨Λ, hΛ⟩ := exists_isLam hv2 hJc hvC.2
  have hJU2 : InU2 (kBar J) := I.h102 G hG t u J hunb.isLocallyUnbalancing
  obtain ⟨hzH, hdich⟩ := pumpup_class I hG hV hK5 hJU2 hlt hΛ
  have hunb' : IsUnbalancingTriple v u L := unbal_pumpup hunb hlt hvu
  rcases hdich with htriv | hvert
  · exact ⟨⟨hzH, htriv.1⟩, hunb'⟩
  · exfalso
    have hL2 : HasL2Model (kBar L) (fun q => Odd q ∧ IsFM9 q) :=
      h625c1 G hG x y K hV hK5 hCx v u L hunb'.isLocallyUnbalancing hrk
    have hL2' : HasL2Model (kBar L) IsFM9 :=
      C3.Layer1.Back.hasL2Model_mono (fun q hq => hq.2) hL2
    have hs : IsSimpleGroup (kBar L) := isSimple_of_hasL2Model hL2'
    obtain ⟨e⟩ := kBar_equiv_bar hlt.2.1.2.2
    have hs' : IsSimpleGroup ↥(bar v L) := e.symm.isSimpleGroup
    have hc : center ↥(bar v L) = ⊥ :=
      center_eq_bot_of_isSimple hs' (isComponent_bar hlt.2.1.2.2).1
    exact false_of_shape2M12_of_center_bot hvert.2.2.1 hc

end Pumpup

end CFSG.GH74.GLS
