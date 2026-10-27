module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitTwistedE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLiftLocal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperTwE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.PartTwo.Census.Exceptional
  CFSG.RankThree.CentralCover CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
open scoped MatrixGroups Pointwise


theorem rk2_split_up_twE6 (hLev : Rk2TwE6LeviRankInputMaximal) {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hK : Rk2IsLabel K lab) (htag : lab.tag = .twE6) (hn : 2 ≤ lab.n)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrq : r ∣ 2 ^ lab.n + 1) :
    CFSG.Open.twoLocalPrimeRank r K ≤ 5 := by
  classical
  obtain ⟨-, -, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n :=
    lieModel_of_markedModel_twE6 htag hM
  have hZk : Nat.card (Subgroup.center K) ∣ Nat.gcd 3 (2 ^ lab.n + 1) :=
    rk2_card_center_dvd_twE6 hK htag hn
  have hZodd : Odd (Nat.card (Subgroup.center K)) :=
    Odd.of_dvd_nat (by decide : Odd 3) (hZk.trans (Nat.gcd_dvd_left 3 _))
  have hZr : ¬ r ∣ Nat.card (Subgroup.center K) := by
    intro h
    have h3 : r ∣ 3 := h.trans (hZk.trans (Nat.gcd_dvd_left 3 _))
    have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3
    omega
  refine (twoLocalPrimeRank_le_of_quotient (N := Subgroup.center K) hZodd hr hZr).trans ?_
  obtain ⟨F, hField, hFin, σ', hcardF, hσ', ⟨eK⟩⟩ :=
    exists_twistedE6RootGroup_of_marked hM'
  letI : Field F := hField
  letI : Finite F := hFin
  have hcongr : CFSG.Open.twoLocalPrimeRank r (K ⧸ Subgroup.center K) =
      CFSG.Open.twoLocalPrimeRank r ↥(twistedE6RootGroup F σ') := by
    have h := CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr
      (p := r) hr.one_lt eK
    exact h.symm
  rw [hcongr]
  exact twoLocalPrimeRank_twistedE6RootGroup_le_five (by omega) σ' hcardF hσ' hLev hr (by omega) hrq


theorem rk2_split_low_twE6_five {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twE6) (hn : 2 ≤ lab.n)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ lab.n + 1) :
    5 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K := by
  have hp2 : p ≠ 2 := by omega
  have h5 : 5 ≤ CFSG.Open.twoLocalPrimeRank p K :=
    (rk2_split_low_twE6_strong hK hp hp2 htag hn hpq).2.1 (by omega)
  have hZk : Nat.card (Subgroup.center K) ∣ Nat.gcd 3 (2 ^ lab.n + 1) :=
    rk2_card_center_dvd_twE6 hK htag hn
  have hZ3 : Nat.card (Subgroup.center K) ∣ 3 := hZk.trans (Nat.gcd_dvd_left 3 _)
  have hz : CFSG.Open.pRank p (Subgroup.center K) = 0 :=
    pRank_eq_zero_of_not_dvd_card hp fun h =>
      absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (h.trans hZ3)) (by omega)
  omega


end CFSG.LocalAnalysis.GLTheoremA
