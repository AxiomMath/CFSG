module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Spin8
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveConjClass
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE8RestTorus
public import CFSG.HardMathSupport.Lang.AnisoE6.PlaneConjGen
public import CFSG.Mathlib.RingTheory.UnitOrderOf
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignTori
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Four
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TwistedRankE6
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Spin4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Spin5
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4Defs
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FourPlane

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.StandardType CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint CFSG.Open
open scoped Pointwise

theorem orderOf_card_eq_four {F : Type} [Field F] [Finite F] {n p : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hrk : rk2Ord p n = 4) :
    orderOf ((Nat.card F : ℕ) : ZMod p) = 4 := by
  rw [hcard]
  rw [show (((2 ^ n : ℕ) : ZMod p)) = (2 : ZMod p) ^ n by push_cast; rfl]
  exact hrk

theorem dvd_card_sq_add_one_of_rk2Ord_four {F : Type} [Field F] [Finite F] {n p : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hrk : rk2Ord p n = 4) :
    p ∣ Nat.card F ^ 2 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have he := orderOf_card_eq_four hcard hrk
  have h4 : ((Nat.card F : ℕ) : ZMod p) ^ 4 = 1 := by
    have h := pow_orderOf_eq_one ((Nat.card F : ℕ) : ZMod p)
    rwa [he] at h
  have hne : ((Nat.card F : ℕ) : ZMod p) ^ 2 - 1 ≠ 0 := by
    intro h0
    have h2 : ((Nat.card F : ℕ) : ZMod p) ^ 2 = 1 := sub_eq_zero.mp h0
    have hdvd : orderOf ((Nat.card F : ℕ) : ZMod p) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [he] at hdvd
    norm_num at hdvd
  have hfac : (((Nat.card F : ℕ) : ZMod p) ^ 2 - 1) *
      (((Nat.card F : ℕ) : ZMod p) ^ 2 + 1) = 0 := by
    have hsq : ((Nat.card F : ℕ) : ZMod p) ^ 4 =
        (((Nat.card F : ℕ) : ZMod p) ^ 2) ^ 2 := by ring
    rw [hsq] at h4
    linear_combination h4
  have hzero : ((Nat.card F : ℕ) : ZMod p) ^ 2 + 1 = 0 :=
    (mul_eq_zero.mp hfac).resolve_left hne
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  exact hzero

theorem sq_eq_neg_one_of_rk2Ord_four {F : Type} [Field F] [Finite F] {n p : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hrk : rk2Ord p n = 4) :
    ((Nat.card F : ℕ) : ZMod p) ^ 2 = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have he := orderOf_card_eq_four hcard hrk
  have h4 : ((Nat.card F : ℕ) : ZMod p) ^ 4 = 1 := by
    have h := pow_orderOf_eq_one ((Nat.card F : ℕ) : ZMod p)
    rwa [he] at h
  have hne : ((Nat.card F : ℕ) : ZMod p) ^ 2 - 1 ≠ 0 := by
    intro h0
    have h2 : ((Nat.card F : ℕ) : ZMod p) ^ 2 = 1 := sub_eq_zero.mp h0
    have hdvd : orderOf ((Nat.card F : ℕ) : ZMod p) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [he] at hdvd
    norm_num at hdvd
  have hfac : (((Nat.card F : ℕ) : ZMod p) ^ 2 - 1) *
      (((Nat.card F : ℕ) : ZMod p) ^ 2 + 1) = 0 := by
    have hsq : ((Nat.card F : ℕ) : ZMod p) ^ 4 =
        (((Nat.card F : ℕ) : ZMod p) ^ 2) ^ 2 := by ring
    rw [hsq] at h4
    linear_combination h4
  have hzero : ((Nat.card F : ℕ) : ZMod p) ^ 2 + 1 = 0 :=
    (mul_eq_zero.mp hfac).resolve_left hne
  linear_combination hzero

theorem card_ne_zero_zmod_of_rk2Ord_four {F : Type} [Field F] [Finite F] {n p : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hrk : rk2Ord p n = 4) :
    ((Nat.card F : ℕ) : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h0
  have h4 : ((Nat.card F : ℕ) : ZMod p) ^ 4 = 1 := by
    have h := pow_orderOf_eq_one ((Nat.card F : ℕ) : ZMod p)
    rwa [orderOf_card_eq_four hcard hrk] at h
  rw [h0] at h4
  norm_num at h4

theorem exists_lam_of_rk2Ord_four {F : Type} [Field F] [Finite F] {n p : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hrk : rk2Ord p n = 4) :
    ∃ lam : ZMod p, ((Nat.card F : ℕ) : ZMod p) * lam = 1 ∧ lam * lam = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hqne := card_ne_zero_zmod_of_rk2Ord_four hcard hp hrk
  refine ⟨((Nat.card F : ℕ) : ZMod p)⁻¹, mul_inv_cancel₀ hqne, ?_⟩
  show ((Nat.card F : ℕ) : ZMod p)⁻¹ * ((Nat.card F : ℕ) : ZMod p)⁻¹ = -1
  rw [← mul_inv, ← sq, sq_eq_neg_one_of_rk2Ord_four hcard hp hrk, inv_neg, inv_one]

theorem coprime_card_sub_one_of_rk2Ord_four {F : Type} [Field F] [Finite F] {n p : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hrk : rk2Ord p n = 4) :
    Nat.Coprime p (Nat.card F - 1) := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 ?_
  intro hdvd
  have h1 : p ∣ 2 ^ (n * 1) - 1 := by
    simpa [hcard, Nat.mul_one] using hdvd
  have h2 := (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_dvd_iff (p := p) (n := n) 1).2 h1
  rw [hrk] at h2
  norm_num at h2

theorem five_le_of_rk2Ord_four {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 4) : 5 ≤ p := by
  refine hp.five_le_of_ne_two_of_ne_three hp2 ?_
  intro h3
  subst h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2ne : (2 : ZMod 3) ≠ 0 := by
    intro h
    have h' := (ZMod.natCast_eq_zero_iff 2 3).mp h
    norm_num at h'
  have hdvd : rk2Ord 3 n ∣ 3 - 1 :=
    ZMod.orderOf_dvd_card_sub_one (pow_ne_zero n h2ne)
  rw [hrk] at hdvd
  norm_num at hdvd

theorem four_le_pRank_adjoint_e8
    (F : Type) [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (he : orderOf ((Nat.card F : ℕ) : ZMod p) = 4) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E8 F)) := by
  obtain ⟨E, hEa, hEcard⟩ := CFSG.LieType.SeitzGeneration.exists_elemAbelian_E8_four F hp he
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hEa hEcard

theorem pRank_adjoint_e8_four
    (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (h7 : 7 ≤ p) (hpq : ¬ p ∣ Nat.card F)
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = 4) :
    CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E8 F)) = 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hS : CFSG.LieType.SeitzGeneration.SylowTorus (adjointGroup Tag.E8 F) p 4 :=
    CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E8_four F hp h7 hpq (Or.inr (Or.inl he))
  have hle : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E8 F)) ≤ 4 :=
    CFSG.LocalAnalysis.GLTheoremA.pRank_le_of_sylowTorusDatum hS hp
  have hge : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E8 F)) :=
    four_le_pRank_adjoint_e8 F hp he
  omega



end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four
