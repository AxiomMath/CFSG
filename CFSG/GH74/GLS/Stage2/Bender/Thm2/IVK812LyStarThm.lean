module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyStar
public import CFSG.GroupTheory.TwoWeightTransport
public import CFSG.Sporadic.Ly.TwoWeightsSpecBase

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.Recognition.LyonsSims

theorem lyThreeInvStar_thm :
    LyThreeInvStar := by
  intro X instX instF hX A hA τ hτA hτ2 hτc W hW hW1 hAW hC
  obtain ⟨eT⟩ := hX
  have hcardX : Nat.card X = 51765179004000000 := by
    rw [Nat.card_congr eT.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly'
  have hfact : (Nat.card X).factorization 2 = 8 := by
    rw [hcardX, show (51765179004000000 : ℕ) = 2 ^ 8 * 202207730484375 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hconj : ∀ u v : X, orderOf u = 2 → orderOf v = 2 → IsConj u v := fun u v hu hv =>
    isConj_of_equiv_of_involutions eT (fun u v hu hv => ly_isConj_of_involutions hu hv) hu hv
  have e1 : X ≃* CFSG.Sporadic.Ly.J := eT.trans CFSG.Sporadic.Ly.lyEquivJ
  have hD := CFSG.Sporadic.Ly.two_weight_rels
  have ha2 := CFSG.Sporadic.Ly.orderOf_a
  have h38 := @CFSG.GroupTheory.TwoWeights.star_of_model X CFSG.Sporadic.Ly.J instX instF
    inferInstance e1 hconj hfact _ _ _ _ _ _ ha2 hD A W hA τ hτA hτ2 hτc hW hW1 hAW hC
  rw [hcardX] at h38
  norm_num at h38

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
