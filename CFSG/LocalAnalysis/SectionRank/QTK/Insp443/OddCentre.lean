module

public import CFSG.Foundations.Basic
public import CFSG.Open.StatedDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.OddCoversLift
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Quasithin CFSG.Quasithin.B69K.OddCovers CFSG.RankThree.PerfectCover
  CFSG.LieType.Steinberg.CentralExt

theorem center_eq_bot_of_card_multiplier_dvd_four {K X : Type} [Group K] [Finite K] [Group X]
    (hK : CFSG.IsQuasisimple K) (hodd : Odd (Nat.card (Subgroup.center K)))
    (e : K ⧸ Subgroup.center K ≃* X) (hM : Nat.card (CFSG.Open.griessHopfMultiplier X) ∣ 4) :
    Subgroup.center K = ⊥ := by
  have hdvd : Nat.card (Subgroup.center K) ∣ 4 := by
    have h1 : Nat.card (Subgroup.center K) ∣ Nat.card (CFSG.Open.griessHopfMultiplier X) := by
      have h2 := CFSG.Quasithin.B69K.OddCovers.card_center_dvd_hopfMultiplier hK.1 e
      rwa [← Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv] at h2
    exact h1.trans hM
  have hcop : Nat.Coprime (Nat.card (Subgroup.center K)) 4 := by
    have h2 : Nat.Coprime (Nat.card (Subgroup.center K)) 2 :=
      (Nat.coprime_two_left.mpr hodd).symm
    simpa using h2.pow_right 2
  exact Subgroup.card_eq_one.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem center_eq_bot_of_psp4 {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hodd : Odd (Nat.card (Subgroup.center K))) {F : Type} [Field F] [Finite F]
    (hF : 5 ≤ Nat.card F) (e : K ⧸ Subgroup.center K ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) :
    Subgroup.center K = ⊥ := by
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier
      (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F))) ∣ 4 := by
    obtain ⟨eM⟩ := (SpClosed.psp_hopfMultiplier (K := F) (n := 2) (by norm_num) hF).2
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact (Nat.gcd_dvd_left 2 (Nat.card F - 1)).trans (by norm_num)
  exact center_eq_bot_of_card_multiplier_dvd_four hK hodd e hM

theorem center_eq_bot_of_psl4 {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hodd : Odd (Nat.card (Subgroup.center K))) {F : Type} [Field F] [Finite F]
    (hF : 3 ≤ Nat.card F) (e : K ⧸ Subgroup.center K ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 4 F)) :
    Subgroup.center K = ⊥ := by
  haveI : Fintype F := Fintype.ofFinite F
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier
      (CFSG.Open.StatedProj (CFSG.Open.StatedSL 4 F))) ∣ 4 := by
    obtain ⟨eM⟩ := (SLClosed.psl_hopfMultiplier_of_three_le (k := F) (n := 4) (by norm_num)
      (by rwa [Fintype.card_eq_nat_card]) (by omega)).2
    have h1 : Nat.card (CFSG.Open.griessHopfMultiplier
        (CFSG.Open.StatedProj (CFSG.Open.StatedSL 4 F))) =
        Nat.card (CFSG.Open.griessHopfMultiplier
          (Matrix.ProjectiveSpecialLinearGroup (Fin 4) F)) := by
      rw [← Nat.card_congr (griessHopfMultiplierCongr
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 F)).toEquiv]
    rw [h1, Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact (Nat.gcd_dvd_left 4 (Fintype.card F - 1)).trans (by norm_num)
  exact center_eq_bot_of_card_multiplier_dvd_four hK hodd e hM

theorem center_eq_bot_of_psu4_of_prime_pow
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hodd : Odd (Nat.card (Subgroup.center K)))
    {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hq : 4 ≤ p ^ f)
    (e : K ⧸ Subgroup.center K ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU 4 (p ^ f) F)) :
    Subgroup.center K = ⊥ := by
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier
      (CFSG.Open.StatedProj (CFSG.Open.StatedSU 4 (p ^ f) F))) ∣ 4 := by
    obtain ⟨eM⟩ := (SUClosed.psu_hopfMultiplier (F := F) (p := p) (f := f) (n := 4)
      (hF := hF) (by norm_num) (by norm_num) hq).2
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact (Nat.gcd_dvd_left 4 (p ^ f + 1)).trans (by norm_num)
  exact center_eq_bot_of_card_multiplier_dvd_four hK hodd e hM

theorem center_eq_bot_of_psu4
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hodd : Odd (Nat.card (Subgroup.center K))) {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (hq : 4 ≤ q) (hqp : IsPrimePow q)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 4 q F)) :
    Subgroup.center K = ⊥ := by
  obtain ⟨p, f, hp, -, hpf⟩ := (isPrimePow_nat_iff q).mp hqp
  subst hpf
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := p) (f := f) hF
  exact center_eq_bot_of_psu4_of_prime_pow hK hodd hF hq e

end CFSG.SectionRank.QTK.Insp443

end
