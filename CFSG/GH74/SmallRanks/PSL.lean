module

public import CFSG.GH74.SmallRanks.Basic
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructure

public section

namespace CFSG.GH74.SmallRanks

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter Matrix

theorem twoRank_psl2_le_two (K : Type) [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) : twoRank (PSL2 K) ≤ 2 := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (PSL2 K)))
  obtain ⟨m, -, ⟨eS⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hodd S
  have hc : orderOf ((eS.symm (DihedralGroup.r 1) : ↥S) : PSL2 K) = 2 ^ m := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hS : Nat.card (S : Subgroup (PSL2 K)) = 2 ^ ((Nat.card (PSL2 K)).factorization 2) :=
    S.card_eq_multiplicity
  have hS2 : Nat.card (S : Subgroup (PSL2 K)) = 2 ^ (m + 1) := by
    rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  have hv : (Nat.card (PSL2 K)).factorization 2 = m + 1 :=
    Nat.pow_right_injective le_rfl (hS.symm.trans hS2)
  exact twoRank_le_two_of_orderOf _ m hc hv

theorem twoRank_le_two_of_statedClassicalModel_PSL_two_odd {G : Type} [Group G] [Finite G]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : StatedClassicalModel G .PSL 2 p f) :
    twoRank G ≤ 2 := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have hodd : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hadm.2.1, hK⟩
  have e' : G ≃* PSL2 K := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have : Finite (PSL2 K) := Finite.of_equiv G e'.toEquiv
  rw [twoRank_eq_of_mulEquiv e']
  exact twoRank_psl2_le_two K hodd

theorem twoRank_eq_of_statedClassicalModel_PSL_two_two {G : Type} [Group G] [Finite G] {f : ℕ}
    (h : StatedClassicalModel G .PSL 2 2 f) : twoRank G = f := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : G ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have : Finite (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K) :=
    Finite.of_equiv G e'.toEquiv
  rw [twoRank_eq_of_mulEquiv e']
  exact CFSG.ShultStronglyClosedTI.LinearModel.twoRank_eq hK

@[expose] def sl3Elt : SpecialLinearGroup (Fin 3) (ZMod 3) :=
  ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 2], by rw [Matrix.det_fin_three]; decide⟩

theorem orderOf_sl3Elt : orderOf sl3Elt = 2 ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (n := 2)
  · decide
  · decide

theorem card_sl3 : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 3)) = 5616 := by
  rw [Matrix.card_SL_field 3, ZMod.card, Fin.prod_univ_three]
  norm_num

theorem factorization_two_card_sl3 :
    (Nat.card (SpecialLinearGroup (Fin 3) (ZMod 3))).factorization 2 = 4 := by
  rw [card_sl3, show (5616 : ℕ) = 2 ^ 4 * 351 by norm_num]
  exact factorization_two_pow_mul_odd (by decide)

theorem center_sl3 : Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod 3)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Subgroup.mem_bot]
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have key : ∀ r : ZMod 3, r ^ Fintype.card (Fin 3) = 1 → r = 1 := by decide
  have hr1 : r = 1 := key r hr
  subst hr1
  apply Subtype.ext
  rw [← hA']
  simp

@[expose] noncomputable def pslEquivSl3 :
    ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3) ≃* SpecialLinearGroup (Fin 3) (ZMod 3) :=
  (QuotientGroup.quotientMulEquivOfEq center_sl3).trans QuotientGroup.quotientBot

theorem twoRank_le_two_of_statedClassicalModel_PSL_three_three {G : Type} [Group G] [Finite G]
    (h : StatedClassicalModel G .PSL 3 3 1) : twoRank G ≤ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]; norm_num
  let φ : K ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
  have e1 : G ≃* SpecialLinearGroup (Fin 3) (ZMod 3) :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 3)).trans pslEquivSl3))
  have : Finite (SpecialLinearGroup (Fin 3) (ZMod 3)) := Finite.of_equiv G e1.toEquiv
  rw [twoRank_eq_of_mulEquiv e1]
  exact twoRank_le_two_of_orderOf sl3Elt 3 orderOf_sl3Elt factorization_two_card_sl3

end CFSG.GH74.SmallRanks
