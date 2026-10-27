module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperShared
public import CFSG.RankThree.PartOne.S15K.FamilyBlock
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.RankThree.PartOne.KF.ClsPSLSmall
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLevi
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.RankThree.PartOne.KFU CFSG.LieType.BorelTits
open CFSG.Assembly.RankThreeEven (localRank)


theorem twoLocalPrimeRank_statedSp_le {K : Type} [Field K] [Finite K] [CharP K 2] {ℓ p : ℕ}
    (hℓ : 1 ≤ ℓ) (hp : p.Prime) (hp2 : p ≠ 2) (h1 : ¬ p ∣ Nat.card K - 1) :
    localRank p (StatedSp ℓ K) ≤ ℓ - 1 := by
  refine twoLocalPrimeRank_le_of_card_le hp ?_
  intro R E hR hR2 hER hE
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_ne_two (K := K) hp hp2
  have hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  have hexp : ∀ g ∈ E, g ^ p = 1 := by
    haveI : CFSG.IsElementaryAbelian p E := hE.isElementaryAbelian
    exact fun g hg => CFSG.elemPow_eq_one_of_isElementaryAbelian g hg
  obtain ⟨a, ha1, ha2, hcard⟩ :=
    CFSG.RankThree.PartOne.KFU.card_le_of_normalizes (spForm ℓ K) (natRep (StatedSp ℓ K))
      (isIsometric_natRep_statedSp (n := ℓ) (K := K)) (natRep_injective _) hp hp2 hpK
      (d := 2) (by norm_num)
      (fun i hi hid => by
        obtain rfl : i = 1 := by omega
        simpa using h1) hR2 hR hER hcomm hexp
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
    show Fintype.card (Fin ℓ) + Fintype.card (Fin ℓ) = 2 * ℓ by
      rw [Fintype.card_fin]; omega] at ha2 hcard
  have harith : a / 2 + (2 * ℓ - 2 * a) / 2 ≤ ℓ - 1 := by
    have h2a : 2 * a ≤ 2 * ℓ := by omega
    rw [show 2 * ℓ - 2 * a = 2 * (ℓ - a) by omega,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    have h1' : a / 2 ≤ a - 1 := by omega
    omega
  calc Nat.card E ≤ p ^ (a / 2) * p ^ ((2 * ℓ - 2 * a) / 2) := hcard
    _ = p ^ (a / 2 + (2 * ℓ - 2 * a) / 2) := (pow_add _ _ _).symm
    _ ≤ p ^ (ℓ - 1) := Nat.pow_le_pow_right hp.pos harith

theorem twoLocalPrimeRank_statedProj_statedOmegaPlus_le {K : Type} [Field K] [Finite K]
    [CharP K 2] {ℓ p : ℕ} (hℓ : 1 ≤ ℓ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h1 : ¬ p ∣ Nat.card K - 1) :
    localRank p (StatedProj (StatedOmega (StatedQuadPlus ℓ K))) ≤ ℓ - 1 := by
  refine (localRank_statedProj_statedOmega_quadPlus_le (K := K) hℓ hp).trans ?_
  exact twoLocalPrimeRank_statedSp_le hℓ hp hp2 h1

theorem twoLocalPrimeRank_statedProj_statedSL_four_le_two {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1) :
    localRank p (StatedProj (StatedSL 4 K)) ≤ 2 := by
  have hp4 : ¬ p ∣ 4 := by
    intro h
    have h2 : p ∣ 2 := by
      have h' : p ∣ 2 ^ 2 := by norm_num at h ⊢; exact h
      exact hp.dvd_of_dvd_pow h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  refine localRank_statedProj_le (n := 4) hp hp2 hp4 ?_
  intro E _ hcomm hexp
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_ne_two (K := K) hp hp2
  have hEel : CFSG.Open.IsElemAbelian p E :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hexp⟩
  have hb := CFSG.StandardType.F4Rest.card_le_pow_of_injective_GL
    (G := GL (Fin 4) K) (ι := Fin 4) (K := K) hp hpK
    (φ := MonoidHom.id (GL (Fin 4) K)) Function.injective_id hEel
  have hd : 2 ≤ CFSG.StandardType.OrdPNS.ordQ K p :=
    CFSG.StandardType.F4Rest.two_le_ordQ hp hpK hpq
  have h4 : Fintype.card (Fin 4) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 2 := by
    rw [Fintype.card_fin]
    have hq : 4 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 4 / 2 :=
      Nat.div_le_div_left (a := 4) hd (by norm_num)
    omega
  exact hb.trans (Nat.pow_le_pow_right hp.pos h4)

theorem rk2_up_BD {K : Type} [Group K] [Finite K] {lab : GLALabel} (hK : Rk2IsLabel K lab)
    (ht : lab.tag = .B ∨ lab.tag = .D) (hn : 2 ≤ lab.n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ lab.n + 1) : GLATwoLocalRank p K < rk2LieRank lab := by
  classical
  obtain ⟨t, ℓ, n⟩ := lab
  change t = .B ∨ t = .D at ht
  change 2 ≤ n at hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, hlab, hM⟩ := rk2_model_of_isLabel hK
  rcases ht with ht | ht
  ·
    subst ht
    have hZ : Subgroup.center K = ⊥ := rk2_center_eq_bot_of_large hK (Or.inl rfl) hn
    have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSp ℓ 2 n := by
      simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
        CFSG.StandardType.markRank, CFSG.StandardType.markChar,
        CFSG.StandardType.markDeg] using hM
    have hl : 2 ≤ ℓ := hlab.2.1
    obtain ⟨-, F, hF, hFin, hFcard, ⟨φ⟩⟩ :=
      hM'.statedClassicalModel (by decide : StatedLieTag.PSp ∈ classicalTags)
    letI : Field F := hF
    letI : Finite F := hFin
    haveI : CharP F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (k := n) hn1 hFcard
    have hdF : p ∣ Nat.card F + 1 := by rw [hFcard]; exact hd
    have hpq : ¬ p ∣ Nat.card F - 1 :=
      CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos (by have := hp.two_le; omega) hdF
    let eZ : K ⧸ Subgroup.center K ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    let eK : K ≃* StatedProj (StatedSp ℓ F) := eZ.symm.trans φ
    have he : GLATwoLocalRank p (StatedProj (StatedSp ℓ F)) = GLATwoLocalRank p K :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr hp.one_lt eK
    rw [← he]
    have hb : localRank p (StatedProj (StatedSp ℓ F)) ≤ ℓ - 1 := by
      rw [localRank_statedProj_eq (by omega) hp]
      exact twoLocalPrimeRank_statedSp_le (by omega) hp hp2 hpq
    have hrank : rk2LieRank ⟨.B, ℓ, n⟩ = ℓ := rfl
    rw [hrank]
    exact lt_of_le_of_lt hb (by omega)
  ·
    subst ht
    have hZ : Subgroup.center K = ⊥ :=
      rk2_center_eq_bot_of_large hK (Or.inr (Or.inl rfl)) hn
    have hl3 : 3 ≤ ℓ := hlab.2
    by_cases h3 : ℓ = 3
    ·
      obtain rfl : ℓ = 3 := h3
      have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL 4 2 n := by
        simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
          CFSG.StandardType.markRank, CFSG.StandardType.markChar,
          CFSG.StandardType.markDeg] using hM
      obtain ⟨-, F, hF, hFin, hFcard, ⟨φ⟩⟩ :=
        hM'.statedClassicalModel (by decide : StatedLieTag.PSL ∈ classicalTags)
      letI : Field F := hF
      letI : Finite F := hFin
      haveI : CharP F 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (k := n) hn1 hFcard
      have hdF : p ∣ Nat.card F + 1 := by rw [hFcard]; exact hd
      have hpq : ¬ p ∣ Nat.card F - 1 :=
        CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos (by have := hp.two_le; omega) hdF
      let eZ : K ⧸ Subgroup.center K ≃* K :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      let eK : K ≃* StatedProj (StatedSL 4 F) := eZ.symm.trans φ
      have he : GLATwoLocalRank p (StatedProj (StatedSL 4 F)) = GLATwoLocalRank p K :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr hp.one_lt eK
      rw [← he]
      have hb : localRank p (StatedProj (StatedSL 4 F)) ≤ 2 :=
        twoLocalPrimeRank_statedProj_statedSL_four_le_two hp hp2 hpq
      have hrank : rk2LieRank ⟨.D, 3, n⟩ = 3 := rfl
      rw [hrank]
      exact lt_of_le_of_lt hb (by norm_num)
    ·
      have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaPlus ℓ 2 n := by
        simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
          CFSG.StandardType.markRank, CFSG.StandardType.markChar,
          CFSG.StandardType.markDeg, h3] using hM
      obtain ⟨-, F, hF, hFin, hFcard, ⟨φ⟩⟩ :=
        hM'.statedClassicalModel (by decide : StatedLieTag.POmegaPlus ∈ classicalTags)
      letI : Field F := hF
      letI : Finite F := hFin
      haveI : CharP F 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (k := n) hn1 hFcard
      have hdF : p ∣ Nat.card F + 1 := by rw [hFcard]; exact hd
      have hpq : ¬ p ∣ Nat.card F - 1 :=
        CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos (by have := hp.two_le; omega) hdF
      let eZ : K ⧸ Subgroup.center K ≃* K :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      let eK : K ≃* StatedProj (StatedOmega (StatedQuadPlus ℓ F)) := eZ.symm.trans φ
      have he : GLATwoLocalRank p (StatedProj (StatedOmega (StatedQuadPlus ℓ F))) =
          GLATwoLocalRank p K :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr hp.one_lt eK
      rw [← he]
      have hb : localRank p (StatedProj (StatedOmega (StatedQuadPlus ℓ F))) ≤ ℓ - 1 :=
        twoLocalPrimeRank_statedProj_statedOmegaPlus_le (by omega) hp hp2 hpq
      have hrank : rk2LieRank ⟨.D, ℓ, n⟩ = ℓ := rfl
      rw [hrank]
      exact lt_of_le_of_lt hb (by omega)

end CFSG.LocalAnalysis.GLTheoremA
