module

public import CFSG.GH74.GLS.C3.Layer1.St1P41Elim
public import CFSG.GH74.GLS.C3.Layer1.Th2L626P4

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1.PumpCalc

section Pumpup

variable {G : Type} [Group G] [Finite G]

theorem not_nontrivial_of_noncommute

    (I : L626Inputs) (hG : C3Hyp G) {x y : G} {K : Subgroup G} (hV : IsV2StarTriple x y K)
    (hK5 : HasL2Model (kBar K) (fun q => q = 5)) {t : G} {J Q : Subgroup G}
    (hJU2 : InU2 (kBar J)) (hQ : IsSylowOf 2 Q (CxK t J)) {y' : G} (hy2 : orderOf y' = 2)
    (hyN : y' ∈ NxK t J) (hyQ : y' ∈ normalizer (Q : Set G)) {v : G} (hvQ : v ∈ Q)
    (hv2 : orderOf v = 2) (hvy : ¬ (v * y' = y' * v)) {L : Subgroup G} (hlt : PumpUpLT 2 t J v L)
    (hnt : ¬ (t ∈ normalizer (L : Set G) ∧ Nonempty (kBar L ≃* kBar J))) : False := by
  have hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J := hlt.1.2.2
  obtain ⟨Λ, hΛ⟩ := exists_isLam hv2 hJc (hlt.2.2.2.1)
  obtain ⟨hzH, hdich⟩ := pumpup_class I hG hV hK5 hJU2 hlt hΛ
  rcases hdich with htriv | hvert
  · exact hnt ⟨hzH, htriv.1⟩
  · exact C3.Layer1.PumpElim.vertConfig_false hG.pRank_eq_four.le hy2 hyN
      ⟨Q, v, L, Λ, hQ, hyQ, hvQ, hv2, hvy, hlt, hΛ, hzH, hvert⟩

end Pumpup

end CFSG.GH74.GLS
