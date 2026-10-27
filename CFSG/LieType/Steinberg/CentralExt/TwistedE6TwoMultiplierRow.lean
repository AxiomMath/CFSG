module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoBound
public import CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6Two
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUnique
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.LeviA2DiagInput
public import CFSG.RankThree.PerfectCover.HopfCentralCoversLift
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.Alternating.Multipliers.Main
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.Foundations
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Suz
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

open Subgroup CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Chevalley.C2E6Std
  CFSG.EvenSmallLie.TwoE6 CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.TwoA.Amalgam

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

theorem exists_autCover_eq_of_lift {X : Type} [Group X] [Finite X]
    (ε : X ⧸ center X ≃* stdGroup) (δ : MulAut stdGroup) (α : X →* X)
    (hαs : Function.Surjective α)
    (hα : (quotCover ε).comp α = δ.toMonoidHom.comp (quotCover ε)) :
    ∃ α' : MulAut X, autCover ε α' = δ := by
  refine ⟨MulEquiv.ofBijective α (Finite.surjective_iff_bijective.1 hαs),
    MulEquiv.ext fun s => ?_⟩
  obtain ⟨x, rfl⟩ := (ε.surjective.comp (QuotientGroup.mk'_surjective (center X))) s
  change autCover ε _ (quotCover ε x) = δ (quotCover ε x)
  rw [← quotCover_autCover]
  exact DFunLike.congr_fun hα x

theorem isPerfect_stdGroup : Group.IsPerfect stdGroup :=
  Group.isPerfect_def.2 CFSG.Monster.B.E6.commutator_stdGroup

section Eam


theorem two_dvd_card_hopfMultiplier : 2 ∣ Nat.card (hopfMultiplier stdGroup) := by
  obtain ⟨hEperf, -, hE2, ⟨εE⟩⟩ := derived_Eam_facts
  have := hEperf
  have hX := isDoubleCover_quotCover εE hE2
  rw [← hX.card_ker]
  exact Subgroup.card_dvd_of_surjective
    (hopfMultiplierToKer_surjective (quotCover εE) hX.surjective hX.ker_le_center)

end Eam


theorem finite_stdGroup : Finite stdGroup := by
  have := finite_twistedE6Group
  exact Finite.of_surjective isogenyStd isogenyStd_surjective

theorem three_dvd_card_hopfMultiplier : 3 ∣ Nat.card (hopfMultiplier stdGroup) := by
  have := isPerfect_twistedE6Group
  rw [← card_ker_isogenyStd]
  exact Subgroup.card_dvd_of_surjective
    (hopfMultiplierToKer_surjective isogenyStd isogenyStd_surjective ker_isogenyStd_le_center)


section Bound


theorem hopfMultiplier_bound :
    (∀ m ∈ hopfMultiplier stdGroup, m ^ 6 = 1) ∧ Nat.card (hopfMultiplier stdGroup) ≤ 12 := by
  have := finite_stdGroup
  have := isPerfect_stdGroup
  have : Finite (HopfCover stdGroup) := CFSG.Alternating.Multipliers.finite_hopfCover
  have : Group.IsPerfect (HopfCover stdGroup) := hopfCover_isPerfect
  exact pow_six_and_card_le (π := hopfCoverMap stdGroup) hopfCoverMap_surjective
    hopfMultiplier_le_center

end Bound

section NeSix


theorem card_hopfMultiplier_ne_six : Nat.card (hopfMultiplier stdGroup) ≠ 6 := by
  intro h6
  obtain ⟨e, g, u, he, hrange, hdet, hδ⟩ := leviA2DiagInput
  obtain ⟨hEperf, hEfin, hE2, ⟨εE⟩⟩ := derived_Eam_facts
  have := hEperf
  have := hEfin
  obtain ⟨δ, hδdef⟩ : ∃ δ : MulAut stdGroup, δ = compatDiagAutHom TwistTag.E6 K barHom u :=
    ⟨_, rfl⟩
  have hδ' : ∀ A, δ (isogenyStd (e A)) = isogenyStd (e (conjSLHom g A)) := fun A => by
    rw [hδdef]
    exact hδ A _ rfl
  have hX := isDoubleCover_quotCover εE hE2
  have hX' := hX.twist δ
  have hcard : Nat.card (hopfMultiplier stdGroup) =
      Nat.card (δ.toMonoidHom.comp (quotCover εE)).ker * 3 := by
    rw [hX'.card_ker, h6]
  have h2 : IsPGroup 2 (quotCover εE).ker :=
    IsPGroup.of_card (n := 1) (by rw [hX.card_ker, pow_one])
  obtain ⟨α, hαs, hα⟩ := exists_lift_of_odd_index hEperf hEperf
    (δ.toMonoidHom.comp (quotCover εE)) hX'.surjective hX'.ker_le_center (quotCover εE)
    hX.surjective hX.ker_le_center h2 3 (by decide) hcard
  obtain ⟨α', hα'⟩ := exists_autCover_eq_of_lift εE δ α hαs hα
  exact autCover_ne εE hE2 he hrange hdet hδ' α' hα'

end NeSix


theorem card_hopfMultiplier : Nat.card (hopfMultiplier stdGroup) = 12 := by
  have := finite_stdGroup
  have := isPerfect_stdGroup
  have : Finite (HopfCover stdGroup) := CFSG.Alternating.Multipliers.finite_hopfCover
  have h6 : 6 ∣ Nat.card (hopfMultiplier stdGroup) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) two_dvd_card_hopfMultiplier
      three_dvd_card_hopfMultiplier
  have hle := hopfMultiplier_bound.2
  have hne := card_hopfMultiplier_ne_six
  have hpos : 0 < Nat.card (hopfMultiplier stdGroup) := Nat.card_pos
  obtain ⟨k, hk⟩ := h6
  omega

theorem nonempty_hopfMultiplier_mulEquiv :
    Nonempty (hopfMultiplier stdGroup ≃* Multiplicative (ZMod 3 × ZMod 2 × ZMod 2)) := by
  have := finite_stdGroup
  have := isPerfect_stdGroup
  have : Finite (HopfCover stdGroup) := CFSG.Alternating.Multipliers.finite_hopfCover
  have h12 := card_hopfMultiplier
  have h6 := hopfMultiplier_bound.1
  have hcomm : ∀ a b : hopfMultiplier stdGroup, Commute a b := fun a b =>
    Subtype.ext ((mem_center_iff.1 (hopfMultiplier_le_center b.2) a))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [h12]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (hopfMultiplier stdGroup)) := inferInstance
  have hfac : (Nat.factorization 12) 2 = 2 := by
    have hle : 2 ≤ (Nat.factorization 12) 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mp (by norm_num)
    have hnle : ¬ 3 ≤ (Nat.factorization 12) 2 := by
      intro h
      have hdvd := (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mpr h
      norm_num at hdvd
    omega
  set Q : Subgroup (hopfMultiplier stdGroup) := (P : Subgroup (hopfMultiplier stdGroup)) with hQ
  have hP : Nat.card Q = 4 := by
    rw [hQ, P.card_eq_multiplicity, h12, hfac]
    norm_num
  have hsq : ∀ x : Q, (x : hopfMultiplier stdGroup) ^ 2 = 1 := fun x => by
    have h4 : (x : hopfMultiplier stdGroup) ^ 4 = 1 := by
      have h := pow_card_eq_one' (G := Q) (x := x)
      rw [hP] at h
      exact_mod_cast h
    have h6' : (x : hopfMultiplier stdGroup) ^ 6 = 1 :=
      Subtype.ext (h6 _ (x : hopfMultiplier stdGroup).2)
    calc (x : hopfMultiplier stdGroup) ^ 2 =
        (x : hopfMultiplier stdGroup) ^ 6 * ((x : hopfMultiplier stdGroup) ^ 4)⁻¹ := by group
      _ = 1 := by rw [h4, h6', inv_one, mul_one]
  obtain ⟨x, hx1⟩ : ∃ x : Q, x ≠ 1 := by
    have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.1 (by rw [hP]; norm_num)
    exact exists_ne 1
  obtain ⟨y, hy1, hyx⟩ : ∃ y : Q, y ≠ 1 ∧ y ≠ x := by
    by_contra h
    push Not at h
    have hs : Function.Surjective (fun b : Bool => if b then x else (1 : Q)) := fun y => by
      by_cases hy : y = 1
      · exact ⟨false, by simp [hy]⟩
      · exact ⟨true, by simp [h y hy]⟩
    have h2 := Nat.card_le_card_of_surjective _ hs
    rw [hP, Nat.card_eq_fintype_card, Fintype.card_bool] at h2
    omega
  have hx1' : (x : hopfMultiplier stdGroup) ≠ 1 := fun h => hx1 (by exact_mod_cast h)
  have hy1' : (y : hopfMultiplier stdGroup) ≠ 1 := fun h => hy1 (by exact_mod_cast h)
  have hxy1 : (x : hopfMultiplier stdGroup) * (y : hopfMultiplier stdGroup) ≠ 1 := fun h => by
    have hxinv : (x : hopfMultiplier stdGroup)⁻¹ = x :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq x)
    have hyx' : (y : hopfMultiplier stdGroup) = x := by
      rw [eq_inv_of_mul_eq_one_right h, hxinv]
    exact hyx (Subtype.ext hyx')
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz
    norm_num at hz
  obtain ⟨φ, hφ, -⟩ := CFSG.LieType.Multipliers.exists_injective_three_two_two
    (hcomm x y) (hcomm z x) (hcomm z y) (hsq x) (hsq y) hz3 hx1' hy1' hxy1 hz1
  have hb : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).2 ⟨hφ, by rw [h12]; simp⟩
  exact ⟨(MulEquiv.ofBijective φ hb).symm⟩

theorem card_hopfMultiplier_cube_eq_one :
    Nat.card {m : hopfMultiplier stdGroup // m ^ 3 = 1} = 3 := by
  obtain ⟨e⟩ := nonempty_hopfMultiplier_mulEquiv
  let e3 : {m : hopfMultiplier stdGroup // m ^ 3 = 1} ≃
      {m : Multiplicative (ZMod 3 × ZMod 2 × ZMod 2) // m ^ 3 = 1} :=
    e.toEquiv.subtypeEquiv (fun x => by
      change x ^ 3 = 1 ↔ (e x) ^ 3 = 1
      rw [← map_pow, ← e.map_one, e.injective.eq_iff])
  rw [Nat.card_congr e3, Nat.card_eq_fintype_card]
  decide +kernel


theorem twistedE6TwoMultiplier : GriessTwistedE6Two.TwistedE6TwoMultiplier := by
  intro Y _ hY
  obtain ⟨e⟩ := (lieModel_twistedE6_two_iff Y).1 hY
  have := isPerfect_stdGroup
  have : Group.IsPerfect Y :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  obtain ⟨f⟩ := nonempty_hopfMultiplier_mulEquiv
  exact ⟨(griessHopfMultiplierCongr e).trans ((hopfMultiplierEquivGriess stdGroup).trans f)⟩

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
