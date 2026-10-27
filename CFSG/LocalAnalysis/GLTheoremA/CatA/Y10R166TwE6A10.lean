module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A9
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataTwD6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataTwD8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Iso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag


theorem exists_concl166S_twE6_of_center_eq_bot
    {X : Type} [Group X] [Finite X] {lab : GLALabel} {p : ℕ}
    (hX : HasLabel X (fun l => l = lab)) (ht : lab.tag = .twE6) (hn : 2 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpdvd : p ∣ 2 ^ lab.n - 1)
    (hZ : Subgroup.center X = ⊥) :
    ∃ (q : ℕ) (B' : Subgroup X) (x' : X) (J : Subgroup X), Concl166S X p q B' x' J := by
  classical
  obtain ⟨F, hField, hFin, hCharF, σ, hcard, hσ, ⟨eX⟩⟩ :=
    exists_mulEquiv_twE6C_of_isLabel hX ht hn hZ
  letI : Field F := hField
  letI : Finite F := hFin
  letI : CharP F 2 := hCharF
  let Ω := AlgebraicClosure F
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 lab.n
  let C : Subgroup (ModGL Tag.E6 Ω) := ⁅thetaFixed Fr, thetaFixed Fr⁆
  haveI : Finite ↥C := Finite.of_surjective eX eX.surjective
  obtain ⟨q, ζ, i, hq, hq2, hqdvd, hq3, hζq, hζ1⟩ :=
    TwE6A.exists_rootOfUnity_kernelComponent F hcard hn
  obtain ⟨x, J, hxq, hx1, hJx, hJq, hcomp, hJlab, hZJ, hmult⟩ :=
    twE6_exists_x_J (f := lab.n) (K := F) (Ω := Ω) (Fr := Fr) hn hcard hσ
      (fun c => iterateFrobenius_def 2 lab.n c) hq hq2 hqdvd hq3 hζq hζ1 i
  have hlow : 5 ≤ evenRank X := (rk2Lower_holds X lab hX).twe6 ht hn
  have hup : evenRank X ≤ 5 := (rk2Upper_holds.1 X lab hX).2.2.2 ht hn hZ
  have heC : evenRank ↥C = 5 := by
    have h1 : evenRank X = evenRank ↥C := evenRank_eq_of_mulEquiv eX
    omega
  have he : 4 ≤ evenRank ↥C := by omega
  have hZC : Subgroup.center ↥C = ⊥ := (center_eq_bot_congr eX).2 hZ
  have h3C : ¬ 3 ∣ Nat.card (Subgroup.center ↥C) := by
    rw [hZC, Subgroup.card_bot]
    exact Nat.Prime.not_dvd_one Nat.prime_three
  have hlabC : HasLabel ↥C (fun l => l = lab) := (hasLabel_congr eX (fun l => l = lab)).1 hX
  have hshape : ∀ lab' : GLALabel, HasLabel ↥C (fun l => l = lab') →
      JShape lab' (3 ∣ Nat.card (Subgroup.center ↥C)) ⟨.twD, 5, lab.n⟩ := by
    intro lab' hlab'
    have hEq : lab' = lab := by
      rcases label_eq_or_BC (K := ↥C) he hlabC hlab' with h | ⟨h1, -, -, -⟩
      · exact h.symm
      · rw [ht] at h1
        rcases h1 with h1 | h1 <;> exact absurd h1 (by decide)
    rw [hEq]
    refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨ht, h3C, rfl, rfl⟩)))))))⟩
  haveI hJs : IsSimpleGroup ↥J :=
    (MulEquiv.isSimpleGroup_congr
      ((QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot)).mp hJq.2.1
  have hm2low : twoRankLow107 (⟨.twD, 5, lab.n⟩ : GLALabel) = 8 * lab.n := by
    simp only [twoRankLow107]
    omega
  have hleJ := CFSG.LocalAnalysis.GLTheoremA.I107L.twoRankLow_twD_ge4 ↥J
    ⟨.twD, 5, lab.n⟩ hJs hJlab rfl (by norm_num)
  have hm2 : evenRank ↥C + 2 ≤ twoRank ↥J := by
    rw [heC]
    show 5 + 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥J)
    calc 5 + 2 = 7 := by norm_num
      _ ≤ 8 * lab.n := by omega
      _ = twoRankLow107 (⟨.twD, 5, lab.n⟩ : GLALabel) := hm2low.symm
      _ ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥J) := hleJ
  have hpq_dvd : p * q ∣ 2 ^ (2 * lab.n) - 1 := by
    have hfactor : 2 ^ (2 * lab.n) - 1 = (2 ^ lab.n - 1) * (2 ^ lab.n + 1) :=
      CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one lab.n
    have hp_dvd : p ∣ 2 ^ (2 * lab.n) - 1 := by
      rw [hfactor]; exact dvd_mul_of_dvd_left hpdvd _
    have hq_dvd : q ∣ 2 ^ (2 * lab.n) - 1 := by
      rw [hfactor]; exact dvd_mul_of_dvd_right hqdvd _
    have hpq : p ≠ q := by
      intro hpq
      have hd : q ∣ (2 ^ lab.n + 1) - (2 ^ lab.n - 1) :=
        Nat.dvd_sub hqdvd (hpq ▸ hpdvd)
      rw [show 2 ^ lab.n + 1 - (2 ^ lab.n - 1) = 2 by
        have := Nat.one_le_two_pow (n := lab.n); omega] at hd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hd)
    exact (Nat.coprime_primes hp hq).2 hpq |>.mul_dvd_of_dvd_of_dvd hp_dvd hq_dvd
  have hdvdJ : p * q ∣ Nat.card ↥J := dvd_card_of_hasLabel_twD_five hn hJlab hZJ hpq_dvd
  have hdvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    rw [show Nat.card (↥J ⧸ Subgroup.center ↥J) = Nat.card ↥J from
      Nat.card_congr
        ((QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot).toEquiv]
    exact hdvdJ
  have hLayer : LayerData166 ↥J q 4 :=
    layerData166_of_hasLabel_twD_five twDLayerData_holds hn hJlab hZJ hq hq2 hqdvd
  have hLayer' : LayerData166 ↥J q (evenRank ↥C - 1) := by
    rw [heC]
    norm_num
    exact hLayer
  obtain ⟨B', hC⟩ := exists_concl166S_of_layerData_of_comp (K := ↥C) (p := p) (q := q)
    hq hq2 hxq hx1 hZC he hJx hJq hcomp ⟨.twD, 5, lab.n⟩ hJlab hshape hm2 hdvd
    hZJ hmult hLayer'
  have hC' : Concl166S ↥⁅thetaFixed (iterateFrobenius (AlgebraicClosure F) 2 lab.n),
      thetaFixed (iterateFrobenius (AlgebraicClosure F) 2 lab.n)⁆ p q B' x J := hC
  exact exists_concl166S_of_mulEquiv eX ⟨q, B', x, J, hC'⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
