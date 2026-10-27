module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcE6
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6SimpleBound

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b


private theorem rk2Mult_E6_le_four (m : ℕ) (hm : 2 ≤ m) :
    rk2Mult (⟨.E6, 0, 2⟩ : GLALabel) m ≤ 4 :=
  rk2Cnt_E6_le_four hm

theorem rk2_up_e6_two {K : Type} [Group K] [Finite K] {lab : GLALabel} (hK : Rk2IsLabel K lab)
    (hlab : lab = ⟨.E6, 0, 2⟩) (hc : Subgroup.center K = ⊥) : evenRank K ≤ 5 := by
  classical
  subst hlab
  obtain ⟨-, -, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 2 := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] using hM
  obtain ⟨-, F, hF, hFin, hFcard, ⟨e0⟩⟩ := hM'.chevalleyExceptionalModel
    (by decide : StatedLieTag.E6 ∈ chevalleyExceptionalTags)
  letI : Field F := hF
  letI : Finite F := hFin
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (k := 2) (by norm_num) (by simpa using hFcard)
  haveI : Finite (adjointGroup Tag.E6 F) := CFSG.LieType.Chevalley.generated_group_finite Tag.E6 F
  let χ : AdjointQuotient .E6 F ≃* adjointGroup Tag.E6 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := Tag.E6) (K := F))).trans
      QuotientGroup.quotientBot
  let eK : K ≃* adjointGroup Tag.E6 F :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans
      (e0.trans χ)
  have h3F : 3 ∣ Nat.card F - 1 := by rw [hFcard]; norm_num
  have h9F : ¬ 9 ∣ Nat.card F - 1 := by rw [hFcard]; norm_num
  have hp3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 5 := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eK]
    exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.pRank_three_adjointGroup_E6_le_five
      (K := F) h3F h9F
  have hpK : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 4 := by
    intro p hp hp2 hp3'
    have h := rk2_pRank_le_E6 K ⟨.E6, 0, 2⟩ p hK (Or.inl rfl) hp hp2 (Or.inl hp3')
    have hm2 : 2 ≤ rk2Ord p 2 := by
      have hpos := rk2Ord_pos hp hp2 2
      have hne : rk2Ord p 2 ≠ 1 := by
        intro hd
        rw [rk2Ord_eq_one_iff] at hd
        rcases (Nat.dvd_prime Nat.prime_three).1 (by simpa using hd) with h | h
        · exact hp.ne_one h
        · exact hp3' h
      omega
    calc CFSG.Open.pRank p (⊤ : Subgroup K)
        ≤ rk2Mult ⟨.E6, 0, 2⟩ (rk2Ord p 2) := h
      _ ≤ 4 := rk2Mult_E6_le_four _ hm2
  show sSup {k | ∃ (q : ℕ) (H : Subgroup K), q.Prime ∧ q ≠ 2 ∧ IsTwoLocal H ∧
    CFSG.Open.pRank q H = k} ≤ 5
  refine csSup_le' ?_
  rintro k ⟨q, H, hq, hq2, -, rfl⟩
  have h1 : CFSG.Open.pRank q H ≤ CFSG.Open.pRank q (⊤ : Subgroup K) :=
    CFSG.SectionRank.pRank_mono hq.one_lt le_top
  by_cases hq3 : q = 3
  · subst hq3
    exact h1.trans hp3
  · exact h1.trans ((hpK q hq hq2 hq3).trans (by norm_num))

end CFSG.LocalAnalysis.GLTheoremA
