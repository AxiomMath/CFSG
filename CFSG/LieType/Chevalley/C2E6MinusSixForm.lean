module

public import CFSG.LieType.Chevalley.C2E6MinusSixPoints
public import CFSG.LieType.Universal.Spin.Forms

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem polarQ_comm (x y : X) : polarQ x y = polarQ y x := by
  simp only [polarQ]
  ring

theorem polarQ_self (x : X) : polarQ x x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp only [polarQ]
  linear_combination (x 0 * x 2 + x 1 * x 3 + x 4 * x 5) * h2

theorem polarQ_add_left (x x' y : X) : polarQ (x + x') y = polarQ x y + polarQ x' y := by
  simp only [polarQ, Pi.add_apply]
  ring

theorem polarQ_add_right (x y y' : X) : polarQ x (y + y') = polarQ x y + polarQ x y' := by
  simp only [polarQ, Pi.add_apply]
  ring

theorem polarQ_smul_left (c : ZMod 2) (x y : X) : polarQ (c • x) y = c * polarQ x y := by
  simp only [polarQ, Pi.smul_apply, smul_eq_mul]
  ring

theorem polarQ_smul_right (c : ZMod 2) (x y : X) : polarQ x (c • y) = c * polarQ x y := by
  simp only [polarQ, Pi.smul_apply, smul_eq_mul]
  ring

theorem Q_add (x y : X) : Q (x + y) = Q x + Q y + polarQ x y := by
  rw [← polar_Q]
  exact QuadraticMap.map_add Q x y

theorem Q_smul (c : ZMod 2) (x : X) : Q (c • x) = c * c * Q x := by
  rw [QuadraticMap.map_smul, smul_eq_mul]

theorem polarQ_eq_zero_of_isTotallySingular {U : Submodule (ZMod 2) X}
    (hU : IsTotallySingular U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) : polarQ x y = 0 := by
  have h := Q_add x y
  rw [hU _ (U.add_mem hx hy), hU x hx, hU y hy, zero_add, zero_add] at h
  exact h.symm

theorem polarQ_nondeg (x : X) (hx : ∀ y, polarQ x y = 0) : x = 0 := by
  have h0 := hx ![0, 0, 1, 0, 0, 0]
  have h1 := hx ![0, 0, 0, 1, 0, 0]
  have h2 := hx ![1, 0, 0, 0, 0, 0]
  have h3 := hx ![0, 1, 0, 0, 0, 0]
  have h4 := hx ![0, 0, 0, 0, 0, 1]
  have h5 := hx ![0, 0, 0, 0, 1, 0]
  simp only [polarQ, Matrix.cons_val, mul_zero, mul_one, add_zero, zero_add] at h0 h1 h2 h3 h4 h5
  funext i
  fin_cases i <;> assumption

theorem nondegenerate_polarBilin_Q : (QuadraticMap.polarBilin Q).Nondegenerate :=
  CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv =>
    polarQ_nondeg v fun w => by rw [← polar_Q]; exact hv w

theorem nondegenerate_Q : Q.Nondegenerate :=
  CFSG.LieType.Universal.Spin.nondegenerate_of_nondegenerate_polarBilin nondegenerate_polarBilin_Q

theorem tail_anisotropic : ∀ t u : ZMod 2, t ^ 2 + t * u + u ^ 2 = 0 → t = 0 ∧ u = 0 := by
  decide

@[expose] def minusCoords : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) ≃ Fin 6 where
  toFun
    | .inl i => ⟨i, by omega⟩
    | .inr (.inl i) => ⟨i + 2, by omega⟩
    | .inr (.inr j) => ⟨j + 4, by omega⟩
  invFun := ![.inl 0, .inl 1, .inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1)]
  left_inv := by decide
  right_inv := by decide

@[expose] def isometryEquivQuadMinus :
    QuadraticMap.IsometryEquiv Q (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1) :=
  ⟨LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) minusCoords, fun x => by
    change CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1 (x ∘ minusCoords) = Q x
    rw [CFSG.LieType.Universal.Spin.quadMinus_apply, Q_apply, Fin.sum_univ_two]
    simp only [Function.comp_apply, minusCoords, Equiv.coe_fn_mk, one_mul]
    rfl⟩

theorem three_orthogonal : ∀ i k m : Fin 27, i ≠ k → polarQ (ptVec i) (ptVec k) = 0 →
    polarQ (ptVec i) (ptVec m) = 0 → polarQ (ptVec k) (ptVec m) = 0 →
      ptVec m = ptVec i ∨ ptVec m = ptVec k ∨ ptVec m = ptVec i + ptVec k := by
  decide +kernel

theorem mem_span_of_orthogonal {a b c : X} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hQa : Q a = 0) (hQb : Q b = 0) (hQc : Q c = 0) (h1 : polarQ a b = 0) (h2 : polarQ a c = 0)
    (h3 : polarQ b c = 0) : c ∈ Submodule.span (ZMod 2) {a, b} := by
  rw [mem_span_pair_zmod_two]
  by_cases hc : c = 0
  · exact Or.inl hc
  obtain ⟨i, rfl⟩ := exists_ptVec_eq ha hQa
  obtain ⟨k, rfl⟩ := exists_ptVec_eq hb hQb
  obtain ⟨m, rfl⟩ := exists_ptVec_eq hc hQc
  exact Or.inr (three_orthogonal i k m (fun h => hab (h ▸ rfl)) h1 h2 h3)

theorem exists_pair_of_two_le_finrank {U : Submodule (ZMod 2) X}
    (hU : 2 ≤ finrank (ZMod 2) U) : ∃ a ∈ U, ∃ b ∈ U, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  have hne : U ≠ ⊥ := by
    rintro rfl
    simp at hU
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hlt : (ZMod 2) ∙ a < U := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem a U).mpr ha) fun h => ?_
    have := finrank_span_singleton (K := ZMod 2) ha0
    rw [h] at this
    omega
  obtain ⟨b, hb, hba⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨a, ha, b, hb, ha0, fun h => hba (h ▸ Submodule.zero_mem _), fun h => hba ?_⟩
  rw [← h]
  exact Submodule.mem_span_singleton_self a

theorem finrank_le_two_of_isTotallySingular {U : Submodule (ZMod 2) X}
    (hU : IsTotallySingular U) : finrank (ZMod 2) U ≤ 2 := by
  refine Nat.le_of_not_lt fun hlt => ?_
  obtain ⟨a, ha, b, hb, ha0, hb0, hab⟩ := exists_pair_of_two_le_finrank (U := U) (by omega)
  have hle : Submodule.span (ZMod 2) {a, b} ≤ U := by
    rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨ha, hb⟩
  have hlt' : Submodule.span (ZMod 2) {a, b} < U := by
    refine lt_of_le_of_ne hle fun h => ?_
    rw [← h, finrank_span_pair_zmod_two ha0 hb0 hab] at hlt
    omega
  obtain ⟨c, hc, hcab⟩ := IsConcreteLE.exists_of_lt hlt'
  exact hcab (mem_span_of_orthogonal ha0 hb0 hab (hU a ha) (hU b hb) (hU c hc)
    (polarQ_eq_zero_of_isTotallySingular hU ha hb) (polarQ_eq_zero_of_isTotallySingular hU ha hc)
    (polarQ_eq_zero_of_isTotallySingular hU hb hc))

theorem wittIndex_two :
    (∃ U : Submodule (ZMod 2) X, IsTotallySingular U ∧ finrank (ZMod 2) U = 2) ∧
      ∀ U : Submodule (ZMod 2) X, IsTotallySingular U → finrank (ZMod 2) U ≤ 2 :=
  ⟨⟨lnSub 0, isTotallySingular_lnSub 0, finrank_lnSub 0⟩,
    fun _ hU => finrank_le_two_of_isTotallySingular hU⟩

end CFSG.LieType.Chevalley.C2E6Overlap
