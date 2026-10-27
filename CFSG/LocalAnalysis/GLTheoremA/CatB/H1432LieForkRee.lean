module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkBase
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.HardMathSupport.Lang.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Dickson.Sec6.I923 (FamReeG2 congr_mem_inner_iff_of_equiv
  exists_noncomm_of_center_bot)


private theorem outerSubThree_reeGammaFieldAut_G2 {a b f : ℕ} (hb : 1 ≤ b)
    (hf : 3 * (2 * b + 1) = f) (F : Type) [Field F] [Finite F] [CharP F ReeTag.G2.prime]
    (σ : F ≃+* F) (hk : Nat.card ↥(fixSubfield σ) = 3 ^ (2 * b + 1))
    (hfix : ((ReeTag.G2.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.G2.reeGamma F a).subtype =
        (ReeTag.G2.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype)) :
    OuterSubThree .twistedG2 0 f (fixSubgroup (ReeTag.G2.reeGammaFieldAut F a σ)) := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  haveI : CharP ↥(fixSubfield σ) ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hk
  let C : Subgroup ↥(ReeTag.G2.reeGamma F a) :=
    (ReeTag.G2.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _)
  have hCfix : fixSubgroup (ReeTag.G2.reeGammaFieldAut F a σ) = C :=
    Subgroup.ext fun _ => Iff.rfl
  let eC : ↥(fixSubgroup (ReeTag.G2.reeGammaFieldAut F a σ)) ≃*
      ↥(ReeTag.G2.reeGamma (fixSubfield σ) b) :=
    (MulEquiv.subgroupCongr hCfix).trans
      (((C.equivMapOfInjective (ReeTag.G2.reeGamma F a).subtype
        (Subgroup.subtype_injective _)).trans (MulEquiv.subgroupCongr hfix)).trans
        ((ReeTag.G2.reeGamma (fixSubfield σ) b).equivMapOfInjective _
          (baseChangeGL_injective (τ := ReeTag.G2.tag) (fixSubfield σ).subtype)).symm)
  have hrel : ReeTitsModel ↥(ReeTag.G2.reeGamma (fixSubfield σ) b) .twistedG2 3 (2 * b + 1) :=
    ⟨⟨Nat.prime_three, by omega, rfl, rfl, ⟨b, rfl⟩, by omega⟩, b, rfl,
      (reeTitsRelationModel_iff ReeTag.G2 _ (2 * b + 1) b).2
        ⟨fixSubfield σ, inferInstance, inferInstance, inferInstance, hk,
          ⟨(nonempty_derivedCentralQuotient_reeGamma_G2 hb hk).some.symm⟩⟩⟩
  obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_2g2_simplicity (h := hrel)
  haveI : Nontrivial ↥(ReeTag.G2.reeGamma (fixSubfield σ) b) := hsimp.toNontrivial
  exact outerSubThree_of_fixed_equiv _ eC hsimp
    (exists_noncomm_of_center_bot (ReeTag.center_reeGamma_G2_eq_bot hk))
    (outerLayerThree_of_field (by decide) hf (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hrel⟩))))

private theorem outerSubThree_reeGamma_G2 {a : ℕ} (ha : 1 ≤ a) (F : Type) [Field F] [Finite F]
    [CharP F ReeTag.G2.prime] (hF : Nat.card F = 3 ^ (2 * a + 1))
    (β : MulAut ↥(ReeTag.G2.reeGamma F a)) (hβ3 : β ^ 3 = 1)
    (hβinn : β ∉ inner ↥(ReeTag.G2.reeGamma F a)) :
    OuterSubThree .twistedG2 0 (2 * a + 1) (fixSubgroup β) := by
  obtain ⟨d, hd, hdvd⟩ := small_Ree_outer_fixed_order a ha F hF Nat.prime_three (by norm_num) β
    hβ3 hβinn
  obtain ⟨-, δ, σ, -, hδ, hcard, hfix⟩ :=
    small_Ree_odd_prime_field_descent a ha F hF Nat.prime_three (by norm_num) β hβ3 hβinn
  have hd' : (2 * a + 1) / 3 = d := by omega
  have hdodd : Odd d := (Nat.odd_mul.1 (hd ▸ odd_two_mul_add_one a : Odd (3 * d))).2
  by_cases hd1 : d = 1
  · subst hd1
    rw [show 2 * a + 1 = 3 by omega]
    refine outerSubThree_of_card_dvd _ ?_
    rw [show fixSubgroup β = CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup β
      from Subgroup.ext fun _ => Iff.rfl]
    exact hdvd.trans (by norm_num)
  · obtain ⟨b, hb⟩ := hdodd
    have hb1 : 1 ≤ b := by omega
    refine outerSubThree_of_conj_pow (r := 1) (j := 1) (by simp) (by simpa using hδ) ?_
    rw [hd'] at hcard hfix
    rw [show (d - 1) / 2 = b by omega] at hfix
    exact outerSubThree_reeGammaFieldAut_G2 hb1 (by omega) F σ (by rw [hcard, hb]) hfix

theorem lieOuterThreeAt_reeG2 : LieOuterThreeAt FamReeG2 := by
  intro P _ _ t n f hadm hF hm ψ hψ3 hψ
  obtain rfl : t = .twistedG2 := hF
  obtain ⟨-, -, rfl, -, -, hf3⟩ := hadm
  obtain ⟨-, -, a, rfl, hrel⟩ := hm.reeTitsModel (by decide)
  obtain ⟨F, _, _, _, hF, ⟨e₁⟩⟩ := (reeTitsRelationModel_iff ReeTag.G2 P (2 * a + 1) a).1 hrel
  have ha : 1 ≤ a := by omega
  have hF' : Nat.card F = 3 ^ (2 * a + 1) := hF
  obtain ⟨e₂⟩ := nonempty_derivedCentralQuotient_reeGamma_G2 (K := F) ha hF'
  let e := e₁.trans e₂
  have hβ3 : MulAut.congr e ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr e ψ ∉ inner ↥(ReeTag.G2.reeGamma F a) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv e ψ).mp hin)
  exact outerSubThree_congr e (outerSubThree_reeGamma_G2 ha F hF' _ hβ3 hβinn)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
