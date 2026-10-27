module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoMultiplierRow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakLift

set_option linter.style.haveILetI false

public section

open CFSG.RankThree.PerfectCover CFSG.LieType.Chevalley.C2E6Std
  CFSG.EvenSmallLie.TwoE6 CFSG.LieType.Steinberg.Exceptional

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

theorem hopfMultiplier_sylow_two_card (P : Sylow 2 (hopfMultiplier stdGroup)) :
    Nat.card P = 4 := by
  letI : Finite stdGroup := finite_stdGroup
  letI : Group.IsPerfect stdGroup := isPerfect_stdGroup
  letI : Finite (HopfCover stdGroup) :=
    CFSG.Alternating.Multipliers.finite_hopfCover
  have hfac : (Nat.factorization 12) 2 = 2 := by
    have hle : 2 ≤ (Nat.factorization 12) 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mp (by norm_num)
    have hnle : ¬ 3 ≤ (Nat.factorization 12) 2 := by
      intro h
      have hdvd := (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mpr h
      norm_num at hdvd
    omega
  rw [P.card_eq_multiplicity, card_hopfMultiplier, hfac]
  norm_num

theorem exists_sc_aut_lift (δ : MulAut stdGroup) :
    ∃ β : MulAut (twistedE6Group 2 1),
      ∀ u, isogenyStd (β u) = δ (isogenyStd u) := by
  letI : Finite (twistedE6Group 2 1) := finite_twistedE6Group
  letI : Group.IsPerfect (twistedE6Group 2 1) := isPerfect_twistedE6Group
  letI : Finite stdGroup := finite_stdGroup
  letI : Group.IsPerfect stdGroup := isPerfect_stdGroup
  letI : Finite (HopfCover stdGroup) := CFSG.Alternating.Multipliers.finite_hopfCover
  exact CFSG.AGLEmbedding.KFactProofs.ThreeWeak.exists_mulAut_lift
    isogenyStd isogenyStd_surjective ker_isogenyStd_le_center
    (p := 3) (e := 1) Nat.prime_three (by simpa using card_ker_isogenyStd)
    (le_of_eq card_hopfMultiplier_cube_eq_one) δ

theorem sc_aut_lift_unique {β γ : MulAut (twistedE6Group 2 1)}
    (h : ∀ u, isogenyStd (β u) = isogenyStd (γ u)) : β = γ := by
  have heq := CFSG.RankThree.PartOne.hom_eq_of_div_central
    isPerfect_twistedE6Group β.toMonoidHom γ.toMonoidHom fun u => by
      apply ker_isogenyStd_le_center
      change isogenyStd (β u / γ u) = 1
      rw [map_div, h u, div_self']
  exact MulEquiv.ext (fun u => DFunLike.congr_fun heq u)

noncomputable def scAut (δ : MulAut stdGroup) : MulAut (twistedE6Group 2 1) :=
  Classical.choose (exists_sc_aut_lift δ)

theorem scAut_spec (δ : MulAut stdGroup) (u : twistedE6Group 2 1) :
    isogenyStd (scAut δ u) = δ (isogenyStd u) :=
  Classical.choose_spec (exists_sc_aut_lift δ) u

noncomputable def scAutHom : MulAut stdGroup →* MulAut (twistedE6Group 2 1) where
  toFun := scAut
  map_one' := by
    apply sc_aut_lift_unique
    intro u
    rw [scAut_spec]
    rfl
  map_mul' δ ε := by
    apply sc_aut_lift_unique
    intro u
    change isogenyStd (scAut (δ * ε) u) = isogenyStd (scAut δ (scAut ε u))
    rw [scAut_spec, scAut_spec, scAut_spec]
    rfl

@[simp] theorem scAutHom_apply (δ : MulAut stdGroup) (u : twistedE6Group 2 1) :
    isogenyStd (scAutHom δ u) = δ (isogenyStd u) := scAut_spec δ u

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

end
