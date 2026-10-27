module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LieType.SteinbergBR.GL2Three

open Matrix

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

abbrev G23 : Type := GL (Fin 2) (ZMod 3)

theorem mkOfDetNeZero_val' (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) (h : A.det ≠ 0) :
    ((GeneralLinearGroup.mkOfDetNeZero A h : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = A :=
  rfl

@[expose] def qList : List (Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  [1, -1, !![0, 2; 1, 0], !![0, 1; 2, 0], !![1, 1; 1, 2], !![2, 2; 2, 1], !![2, 1; 1, 1],
    !![1, 2; 2, 2]]

theorem qList_mul : ∀ a ∈ qList, ∀ b ∈ qList, a * b ∈ qList := by
  decide +kernel

theorem qList_cube : ∀ a ∈ qList, a ^ 3 ∈ qList := by
  decide +kernel

theorem qList_pow_four : ∀ a ∈ qList, a ^ 4 = 1 := by
  decide +kernel

theorem qList_det : ∀ a ∈ qList, a.det = 1 := by
  decide +kernel

theorem mem_qList_of : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 3), M.det = 1 → M ^ 4 = 1 →
    M ∈ qList := by
  decide +kernel

theorem qList_involution : ∀ a ∈ qList, (a ^ 2 = 1 ∧ a ≠ 1) ↔ a = -1 := by
  decide +kernel

theorem card_qList : (Finset.univ.filter fun M : Matrix (Fin 2) (Fin 2) (ZMod 3) =>
    M ∈ qList).card = 8 := by
  decide +kernel

theorem card_two_elements : (Finset.univ.filter fun M : Matrix (Fin 2) (Fin 2) (ZMod 3) =>
    M.det ≠ 0 ∧ M ^ 16 = 1).card = 32 := by
  decide +kernel

@[expose] def quatQ : Subgroup G23 where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) ∈ qList}
  one_mem' := by
    change (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) ∈ qList
    exact List.mem_cons_self
  mul_mem' {a b} ha hb := qList_mul _ ha _ hb
  inv_mem' {a} ha := by
    change ((a⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) ∈ qList
    have h1 : (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) * ((a⁻¹ : G23) : Matrix _ _ (ZMod 3)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h4 := qList_pow_four _ ha
    have : ((a⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 3 := by
      calc ((a⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3))
          = (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 4 * ((a⁻¹ : G23) : Matrix _ _ (ZMod 3)) := by
            rw [h4, Matrix.one_mul]
        _ = (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 3 *
            ((a : Matrix (Fin 2) (Fin 2) (ZMod 3)) * ((a⁻¹ : G23) : Matrix _ _ (ZMod 3))) := by
            rw [pow_succ, Matrix.mul_assoc]
        _ = (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 3 := by rw [h1, Matrix.mul_one]
    rw [this]
    exact qList_cube _ ha

theorem mem_quatQ {g : G23} : g ∈ quatQ ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) ∈ qList :=
  Iff.rfl

theorem mem_quatQ_iff {g : G23} :
    g ∈ quatQ ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 ∧ g ^ 4 = 1 := by
  rw [mem_quatQ]
  constructor
  · intro h
    refine ⟨qList_det _ h, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact qList_pow_four _ h
  · rintro ⟨hdet, h4⟩
    refine mem_qList_of _ hdet ?_
    rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]

theorem quatQ_normal : quatQ.Normal := by
  constructor
  intro g hg c
  rw [mem_quatQ_iff] at hg ⊢
  obtain ⟨hdet, h4⟩ := hg
  refine ⟨?_, by rw [conj_pow, h4, mul_one, mul_inv_cancel]⟩
  have hc : ((c : Matrix (Fin 2) (Fin 2) (ZMod 3))).det *
      ((c⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one, hc]

theorem quatQ_isPGroup : IsPGroup 2 quatQ := fun g => ⟨2, Subtype.ext ((mem_quatQ_iff.1 g.2).2)⟩

theorem card_quatQ : Nat.card quatQ = 8 := by
  have e : quatQ ≃ {M : Matrix (Fin 2) (Fin 2) (ZMod 3) // M ∈ qList} :=
    { toFun := fun g => ⟨(g : G23).val, g.2⟩
      invFun := fun M => ⟨GeneralLinearGroup.mkOfDetNeZero M.1 (by
        rw [qList_det _ M.2]
        exact one_ne_zero), by
          rw [mem_quatQ, mkOfDetNeZero_val']
          exact M.2⟩
      left_inv := fun g => Subtype.ext (Units.ext rfl)
      right_inv := fun M => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, card_qList]

theorem mem_quatQ_orderOf {g : G23} (hg : g ∈ quatQ) : orderOf g = 2 ↔ g = -1 := by
  rw [orderOf_eq_prime_iff]
  have h := qList_involution _ hg
  constructor
  · rintro ⟨h2, h1⟩
    refine Units.ext ((h.1 ⟨?_, ?_⟩).trans ?_)
    · rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    · exact fun e => h1 (Units.ext e)
    · rfl
  · rintro rfl
    obtain ⟨h2, h1⟩ := h.2 rfl
    exact ⟨Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h2),
      fun e => h1 (congrArg Units.val e)⟩

theorem card_G23 : Nat.card G23 = 48 := by
  show Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = 48
  rw [Matrix.card_GL_field (𝔽 := ZMod 3) 2, ZMod.card]
  decide

theorem pCore_two_eq : CFSG.pCore 2 G23 = quatQ := by
  have hQ : quatQ ≤ CFSG.pCore 2 G23 := le_sSup ⟨quatQ_normal, quatQ_isPGroup⟩
  refine le_antisymm ?_ hQ
  by_contra hne
  set O := CFSG.pCore 2 G23
  have hOp : IsPGroup 2 O := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := hOp.exists_card_eq
  have hdvd : Nat.card O ∣ 48 := card_G23 ▸ Subgroup.card_subgroup_dvd_card O
  have h8 : 8 ∣ Nat.card O := card_quatQ ▸ Subgroup.card_dvd_of_le hQ
  have hne8 : Nat.card O ≠ 8 := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge hQ (by rw [h, card_quatQ])).ge
  have hk4 : k = 4 := by
    rw [hk] at hdvd h8 hne8
    have hk5 : k < 5 := by
      by_contra h
      have := (pow_dvd_pow 2 (not_lt.1 h)).trans hdvd
      norm_num at this
    have hk3 : 3 ≤ k := by
      by_contra h
      have := Nat.le_of_dvd (pow_pos two_pos _) h8
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right two_pos (by omega)
      omega
    interval_cases k
    · exact absurd rfl hne8
    · rfl
  have hfac : (Nat.card G23).factorization 2 = 4 := by
    rw [card_G23, show (48 : ℕ) = 2 ^ 4 * 3 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  let S : Sylow 2 G23 := Sylow.ofCard O (by rw [hk, hk4, hfac])
  have hmem : ∀ g : G23, g ^ 16 = 1 → g ∈ O := by
    intro g hg
    have hgp : IsPGroup 2 (Subgroup.zpowers g) :=
      IsPGroup.of_card (n := (Nat.card (Subgroup.zpowers g)).factorization 2) (by
        rw [Nat.card_zpowers]
        have hdvd : orderOf g ∣ 2 ^ 4 := orderOf_dvd_of_pow_eq_one hg
        obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
        rw [hm, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same])
    obtain ⟨P, hP⟩ := hgp.exists_le_sylow
    have hPS : P = S := by
      have : Subsingleton (Sylow 2 G23) :=
        (Sylow.unique_of_normal S (CFSG.pCore_normal (p := 2) (G := G23))).instSubsingleton
      exact Subsingleton.elim _ _
    have := hP (Subgroup.mem_zpowers g)
    rw [hPS] at this
    exact this
  have hle : (Finset.univ.filter fun M : Matrix (Fin 2) (Fin 2) (ZMod 3) =>
      M.det ≠ 0 ∧ M ^ 16 = 1).card ≤ Nat.card O := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_injective
      (fun M => (⟨GeneralLinearGroup.mkOfDetNeZero M.1 M.2.1,
        hmem _ (Units.ext (by
          rw [Units.val_pow_eq_pow_val, Units.val_one, mkOfDetNeZero_val']
          exact M.2.2))⟩ : O)) ?_
    intro M N hMN
    have := congrArg (fun g : O => ((g : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3))) hMN
    simp only [mkOfDetNeZero_val'] at this
    exact Subtype.ext this
  rw [card_two_elements, hk, hk4] at hle
  exact absurd hle (by norm_num)

end CFSG.LieType.SteinbergBR.GL2Three
