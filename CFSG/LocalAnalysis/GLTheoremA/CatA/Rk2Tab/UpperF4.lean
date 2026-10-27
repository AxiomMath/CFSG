module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperShared
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLevi
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly


theorem rk2_up_F4 {K : Type} [Group K] [Finite K] {lab : GLALabel} (hK : Rk2IsLabel K lab)
    (ht : lab.tag = .F4) (hn : 2 ≤ lab.n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ lab.n + 1) : GLATwoLocalRank p K < rk2LieRank lab := by
  classical
  obtain ⟨t, l, n⟩ := lab
  change t = .F4 at ht
  change 2 ≤ n at hn
  subst ht
  have hZ : Subgroup.center K = ⊥ :=
    rk2_center_eq_bot_of_large hK (Or.inr (Or.inr (Or.inl rfl))) hn
  obtain ⟨-, -, hM⟩ := rk2_model_of_isLabel hK
  have hM' : LieModel (K ⧸ Subgroup.center K) .F4 0 2 n := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] using hM
  have hCE := hM'.chevalleyExceptionalModel
    (by decide : (.F4 : StatedLieTag) ∈ CFSG.Blueprint.chevalleyExceptionalTags)
  simp only [CFSG.Blueprint.ChevalleyExceptionalModel,
    CFSG.Blueprint.UntwistedChevalleyModel] at hCE
  obtain ⟨F, hF, hFin, hcardF, ⟨e0⟩⟩ := hCE.2
  letI : Field F := hF
  letI : Finite F := hFin
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (k := n) (by omega) hcardF
  haveI : Finite (adjointGroup .F4 F) := CFSG.LieType.Chevalley.generated_group_finite .F4 F
  have hpq : ¬ p ∣ Nat.card F - 1 := by
    intro hd1
    rw [hcardF] at hd1
    have hd' : p ∣ 2 ^ n + 1 := hd
    have hsub : p ∣ 2 := by
      have h := Nat.dvd_sub hd' hd1
      rwa [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by
        have h1 : 0 < 2 ^ n := pow_pos (by norm_num) n
        omega] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hsub)
  have hL : CFSG.StandardType.F4Rest.GGF4LeviRankInput F p :=
    CFSG.StandardType.F4Rest.ggF4LeviRankInput_holds (K := F) hp hp2 hpq
  have hle : GLATwoLocalRank p (adjointGroup .F4 F) ≤ 3 := by
    refine glaTwoLocalRank_le_of_card_le hp ?_
    intro R E hR hR2 hER hE
    exact CFSG.StandardType.F4Rest.twoLocal_card_le_of_levi (K := F) hp hp2 hpq hL hR hR2 hER hE
  let χ : CFSG.Blueprint.AdjointQuotient .F4 F ≃* adjointGroup .F4 F :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := F))).trans
        QuotientGroup.quotientBot
  let e1 : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let eK : K ≃* adjointGroup .F4 F := e1.symm.trans (e0.trans χ)
  have heq : GLATwoLocalRank p K = GLATwoLocalRank p (adjointGroup .F4 F) :=
    (CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr hp.one_lt eK).symm
  have h4 : rk2LieRank ⟨.F4, l, n⟩ = 4 := rfl
  rw [heq, h4]
  exact lt_of_le_of_lt hle (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA
