module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116e
public import CFSG.LieType.SeitzGeneration.QuasiHigh3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116c

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex Seitz2310CubeSimple)
open CFSG.LieType.Seitz (seitzHyperGamma)
open CFSG.LieType.SeitzGeneration.QuasiHigh (SeitzSimpleAt SeitzCoverRest SeitzCoverFamExcRest)
open CFSG.AGLEmbeddingD2 (KFactSeitzRankTwo)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open GL83.CompFam

set_option linter.unusedSectionVars false

@[expose] def SeitzQuasiAt (k : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ k →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
        seitzHyperGamma p E = ⊤

theorem seitzQuasiAt_of_rest {k : ℕ} (hk : 1 ≤ k) (hS : SeitzSimpleAt k) (hC : SeitzCoverRest k) :
    SeitzQuasiAt k :=
  fun _ hp hp2 _ _ _ hq d hd hpd hL34 _ hE hcard hex =>
    CFSG.LieType.SeitzGeneration.QuasiHigh.seitzHyperGamma_eq_top_of_simpleAt hk hS hC hp hp2 hq d hd hpd hL34
      hE hcard hex

theorem seitzQuasiAt_two (h2 : KFactSeitzRankTwo) (hC : SeitzCoverRest 2) : SeitzQuasiAt 2 :=
  seitzQuasiAt_of_rest (by norm_num) (CFSG.LieType.SeitzGeneration.QuasiHigh.seitzSimpleAt_two h2) hC

theorem seitzQuasiAt_three (h3 : Seitz2310CubeSimple) (hC : SeitzCoverRest 3) : SeitzQuasiAt 3 :=
  seitzQuasiAt_of_rest (by norm_num) (CFSG.LieType.SeitzGeneration.QuasiHigh.seitzSimpleAt_three h3) hC

theorem seitzHyperGamma_eq_top_of_low (hP : SeitzQuasiAt 2) (hQ : SeitzQuasiAt 3) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (d : TauCeti.ValidLieTypeIndex)
    (hd : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hpd : p ≠ d.1.characteristic) (hL34 : ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hE2 : p ^ 2 ≤ Nat.card E)
    (hE3 : Nat.card E ≤ p ^ 3)
    (hex : ¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) :
    seitzHyperGamma p E = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow hE
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 (by rw [← hk]; exact hE2)
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).1 (by rw [← hk]; exact hE3)
  interval_cases k
  · exact hP p hp hp2 K hq d hd hpd hL34 E hE hk hex
  · exact hQ p hp hp2 K hq d hd hpd hL34 E hE hk hex

@[expose] def SeitzLowRest : Prop :=
  CFSG.LieType.SeitzGeneration.QuasiHigh.SeitzCoverFamExcRest 2 ∧
    CFSG.LieType.SeitzGeneration.QuasiHigh3.SeitzCoverCubeRest3 ∧
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2310CubeSimple

section Narrow

theorem seitzCoverRest_two_of_famExcRest (hGA : GriessMultipliersAllModels)
    (hC : SeitzCoverFamExcRest 2) : SeitzCoverRest 2 :=
  CFSG.LieType.SeitzGeneration.QuasiHigh.seitzCoverRest_of_famRest hGA
    (CFSG.LieType.SeitzGeneration.QuasiHigh.seitzCoverFamRest_of_excRest (by norm_num) hC)

theorem seitzCoverRest_three_of_cubeRest (hGA : GriessMultipliersAllModels)
    (hC : CFSG.LieType.SeitzGeneration.QuasiHigh2.SeitzCoverCubeRest) : SeitzCoverRest 3 :=
  CFSG.LieType.SeitzGeneration.QuasiHigh.seitzCoverRest_of_famRest hGA
    (CFSG.LieType.SeitzGeneration.QuasiHigh.seitzCoverFamRest_of_excRest (by norm_num)
      (CFSG.LieType.SeitzGeneration.QuasiHigh2.seitzCoverFamExcRest_three_of_cubeRest hC))

theorem seitzQuasiAt_two_of_low (h2 : KFactSeitzRankTwo) (hGA : GriessMultipliersAllModels)
    (h : SeitzLowRest) : SeitzQuasiAt 2 :=
  seitzQuasiAt_two h2 (seitzCoverRest_two_of_famExcRest hGA h.1)

theorem seitzQuasiAt_three_of_low (hGA : GriessMultipliersAllModels)
    (h : SeitzLowRest) : SeitzQuasiAt 3 :=
  seitzQuasiAt_three h.2.2
    (seitzCoverRest_three_of_cubeRest hGA (CFSG.LieType.SeitzGeneration.QuasiHigh3.seitzCoverCubeRest_of_rest3 h.2.1))

end Narrow

theorem input23_10Faith_of_seitz (hP : SeitzQuasiAt 2) (hQ : SeitzQuasiAt 3) :
    InputsSeitz.Input23_10Faith := by
  intro p q hp hp5 hq hqp Y _ _ _ K B hK hB hBN hBC hcard hcard3 hlie hexc
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, hdq⟩ := hlie
  have hdq' : d.1.characteristic = q := hdq
  have hpd : p ≠ d.1.characteristic := fun h => hqp (hdq'.symm.trans h.symm)
  have hex : ¬ ExcIndex p d.1 := by
    intro h
    obtain ⟨hp5', hd1⟩ := InputsSeitz3.excIndex_ge_five hp5 h
    apply hexc hp5'
    obtain ⟨e⟩ := hd
    rcases hd1 with h1 | h1 | h1
    · exact Or.inl ⟨d, h1, ⟨e⟩⟩
    · exact Or.inr (Or.inr ⟨d, h1, ⟨e⟩⟩)
    · exact Or.inr (Or.inl ⟨d, h1, ⟨e⟩⟩)
  have hE2 : p ^ 2 ≤ Nat.card (InputsSeitz3.autIm B K) := by
    rw [InputsSeitz3.card_autIm hBN hBC]
    obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow hB
    rw [hk] at hcard ⊢
    have hk1 : 1 < k := (Nat.pow_lt_pow_iff_right hp.one_lt).1 (by rwa [pow_one])
    exact Nat.pow_le_pow_right hp.pos hk1
  have hE3 : Nat.card (InputsSeitz3.autIm B K) ≤ p ^ 3 := by
    rw [InputsSeitz3.card_autIm hBN hBC]
    exact hcard3
  have hgen := seitzHyperGamma_eq_top_of_low hP hQ hp (by omega) hK.2.2 d hd hpd
    (fun h => absurd h.1 (by omega)) (InputsSeitz3.isElemAbelian_autIm hB K) hE2 hE3 (Or.inl hex)
  refine InputsSeitz.isGMinusOne_of_centGenI hp hB hK ?_
  rw [show stab B K = B from inf_eq_left.2 hBN]
  exact InputsSeitz3.le_centGenI_of_autIm hBN hBC hgen

section CertThree

theorem input23_10FaithThree_of_seitz (hP : SeitzQuasiAt 2) (hQ : SeitzQuasiAt 3) :
    Claims1116c.Input23_10FaithThree := by
  intro q hq hq2 hq3 Y _ _ _ K B hK hB hBN hBC hcard hcard3 hlie
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd, hdq⟩ := hlie
  have hdq' : d.1.characteristic = q := hdq
  have hpd : 3 ≠ d.1.characteristic := fun h => hq3 (hdq'.symm.trans h.symm)
  have hex : ¬ ExcIndex 3 d.1 := fun h =>
    hq2 (hdq'.symm.trans (Claims1116e.characteristic_eq_two_of_excIndex_three h))
  have hL34 : ¬ (3 = 3 ∧ IsLThreeFour (↥K ⧸ Subgroup.center ↥K)) := by
    rintro ⟨-, hL⟩
    obtain ⟨e⟩ := hd
    have hc := CFSG.HardMathSupport.Solomon.Coordinator.card_of_isLThreeFour hL
    haveI : Finite (↥K ⧸ Subgroup.center ↥K) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    exact Claims1116c.not_isChevSimple_of_card_bound (p := 3) hc (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)
      q hq hq2 hq3 (Or.inl ⟨TauCeti.CFSGIndex.lie d, hdq', ⟨e⟩⟩)
  have hE2 : 3 ^ 2 ≤ Nat.card (InputsSeitz3.autIm B K) := by
    rw [InputsSeitz3.card_autIm hBN hBC]
    obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow hB
    rw [hk] at hcard ⊢
    have hk1 : 1 < k := (Nat.pow_lt_pow_iff_right Nat.prime_three.one_lt).1 (by rwa [pow_one])
    exact Nat.pow_le_pow_right (by norm_num) hk1
  have hE3 : Nat.card (InputsSeitz3.autIm B K) ≤ 3 ^ 3 := by
    rw [InputsSeitz3.card_autIm hBN hBC]
    exact hcard3
  have hgen := seitzHyperGamma_eq_top_of_low hP hQ Nat.prime_three (by norm_num) hK.2.2 d hd hpd hL34
    (InputsSeitz3.isElemAbelian_autIm hB K) hE2 hE3 (Or.inl hex)
  refine InputsSeitz.isGMinusOne_of_centGenI Nat.prime_three hB hK ?_
  rw [show stab B K = B from inf_eq_left.2 hBN]
  exact InputsSeitz3.le_centGenI_of_autIm hBN hBC hgen

end CertThree

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz6

end
