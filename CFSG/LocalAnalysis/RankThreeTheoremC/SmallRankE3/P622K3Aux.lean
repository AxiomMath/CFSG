module

public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open scoped MatrixGroups

theorem nonempty_psl_two_seven_equiv_psl_three_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 7) : Nonempty (PSL(2, F) ≃* PSL(3, ZMod 2)) := by
  have h7 : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hF]
  let φ : F ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hcard
  let e₁ : PSL(2, F) ≃* PSL(2, ZMod 7) :=
    CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2)
  let e₂ : PSL(3, ZMod 2) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  obtain ⟨e₄⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  exact ⟨e₁.trans ((e₂.trans e₃).trans e₄).symm⟩

theorem nonempty_psl_three_galoisField_two_one_equiv :
    Nonempty (PSL(3, GaloisField 2 1) ≃* PSL(3, ZMod 2)) :=
  ⟨CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
    (GaloisField.equivZmodP 2).toRingEquiv (Fin 3)⟩

theorem one_le_pRank_of_orderOf_eq_prime {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x : G) (hx : orderOf x = p) : 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hxp : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hEab : CFSG.Open.IsElemAbelian p (Subgroup.zpowers x) := by
    unfold CFSG.Open.IsElemAbelian
    refine ⟨inferInstance, ?_⟩
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hcard : Nat.card (Subgroup.zpowers x) = p ^ 1 := by
    rw [pow_one, Nat.card_zpowers, hx]
  have hmem : (1 : ℕ) ∈ {k | ∃ E : Subgroup G, E ≤ (⊤ : Subgroup G) ∧
      CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
    show ∃ E : Subgroup G, E ≤ (⊤ : Subgroup G) ∧
      CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 1
    exact ⟨Subgroup.zpowers x, le_top, hEab, hcard⟩
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ (⊤ : Subgroup G) ∧
      CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨F, -, -, hF⟩
    have h1 : p ^ k ≤ Nat.card G := by
      rw [← hF]
      exact F.card_le_card_group
    exact (Nat.lt_pow_self hp1 : k < p ^ k).le.trans h1
  unfold CFSG.Open.pRank
  exact le_csSup hbdd hmem

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
