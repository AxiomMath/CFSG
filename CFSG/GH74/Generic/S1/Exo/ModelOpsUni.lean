module

public import CFSG.GH74.Generic.S1.Exo.ModelOps
public import CFSG.GH74.Generic.S1.TPairFacts

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

section Uni

variable {q : ℕ} {F : Type} [Field F] [Finite F]

theorem uniModelOps_two_ne_zero (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) : (2 : F) ≠ 0 :=
  two_ne_zero_of_odd_card (by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : q % 2 = 1)).pow)

theorem uniModelOps_yGL_mem (hF : Nat.card F = q ^ 2) : yGL F ∈ StatedSU 4 q F := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  exact (ModelData.uni hF).yGL_mem_K4

theorem uniModelOps_xGL_mem (hF : Nat.card F = q ^ 2) : xGL F ∈ StatedSU 4 q F := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  exact (ModelData.uni hF).xGL_mem_K4

theorem uniModelOps_swapGL_mem (hF : Nat.card F = q ^ 2) : swapGL F ∈ StatedSU 4 q F := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  exact (ModelData.uni hF).swapGL_mem_K4

theorem uniModelOps_mem_blk_iff (hF : Nat.card F = q ^ 2) {a b : Fin 4} {g : ↥(StatedSU 4 q F)} :
    g ∈ SymBlocksUni.uniBlk F q a b ↔
      SymBlocksUni.IdOut a b ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  exact SymBlocksUni.mem_uniBlk_iff hF

theorem uniModelOps_mem_center_iff (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1)
    (g : ↥(StatedSU 4 q F)) :
    g ∈ Subgroup.center ↥(StatedSU 4 q F) ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  exact mem_center_statedSU_four_iff hF hq g

omit [Finite F] in
theorem uniModelOps_yGL_ne_one (h2 : (2 : F) ≠ 0) : yGL F ≠ 1 := by
  intro h
  have h0 := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F) 0 0) h
  simp only [yGL_matrix, Units.val_one, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h0
  exact h2 (by simp at h0; linear_combination (-1 : F) * h0)

omit [Finite F] in
theorem uniModelOps_idOut_yGL :
    SymBlocksUni.IdOut 0 1 ((yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rw [yGL_matrix]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢

omit [Finite F] in
theorem uniModelOps_comm_yGL {M : Matrix (Fin 4) (Fin 4) F} (hM : SymBlocksUni.IdOut 0 1 M) :
    M * Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F) =
      Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F) * M := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : (i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1)
  · rcases hij with ⟨hi | hi, hj | hj⟩ <;> subst hi <;> subst hj <;> simp
  · rw [hM i j hij]
    by_cases h : i = j
    · subst h
      simp [mul_comm]
    · simp [h]

omit [Finite F] in
theorem uniModelOps_xGL_matrix : ((xGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1 := by
  rw [xGL_eq_neg_one]
  simp

omit [Finite F] in
theorem uniModelOps_xGL_mul_yGL : xGL F * yGL F = xyGL F :=
  calc xGL F * yGL F = yGL F * xyGL F * yGL F := by rw [← xGL_eq_yGL_mul_xyGL]
    _ = xyGL F * yGL F * yGL F := by rw [yGL_mul_xyGL_comm]
    _ = xyGL F := by rw [mul_assoc, yGL_mul_self, mul_one]

theorem uniModelOps_blk_model (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) (a b : Fin 4) (hab : a ≠ b) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = q ∧
      Nonempty (SL(2, F₀) ≃* ↥((uniBlockOps hF hq).blk a b)) := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  obtain ⟨e₁⟩ := nonempty_sl2_equiv_uni_H2 hF
  obtain ⟨e₂⟩ := uni_blk_equiv hF hq rfl a b hab
  exact ⟨↥(CFSG.LieType.Steinberg.fixedSubfield F p f), inferInstance, inferInstance,
    CFSG.LieType.Steinberg.card_fixedSubfield hF,
    ⟨(e₁.trans (MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 2)).symm).trans e₂⟩⟩

@[expose] noncomputable def uniModelOps (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) :
    ModelOps (StatedSU 4 q F) where
  ops := uniBlockOps hF hq
  pf := uniPairFacts hF hq
  blkq a b hab := by
    obtain ⟨p, f, h, rfl, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨h.prime⟩
    have : CharP F p := h.charP
    have hq5 : 5 ≤ p ^ f := by
      have := h.one_lt_pow
      omega
    obtain ⟨e⟩ := uni_blk_equiv hF hq rfl a b hab
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_su2_of_five_le hF hq5)
  qM := q
  qM_odd := Nat.odd_iff.2 (by omega)
  blk_model := uniModelOps_blk_model hF hq
  z0 := ⟨yGL F, uniModelOps_yGL_mem hF⟩
  z0_mem := by
    rw [uniBlockOps_blk, uniModelOps_mem_blk_iff hF]
    exact uniModelOps_idOut_yGL
  z0_sq := Subtype.ext yGL_mul_self
  z0_ne := fun h =>
    uniModelOps_yGL_ne_one (uniModelOps_two_ne_zero hF hq) (congrArg Subtype.val h)
  z0_cent g hg := by
    have hid : SymBlocksUni.IdOut 0 1 ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := hg.1
    apply Subtype.ext
    apply Units.ext
    change ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ((g : GL (Fin 4) F) : Matrix _ _ F)
    rw [yGL_matrix]
    exact uniModelOps_comm_yGL hid
  neg := ⟨xGL F, uniModelOps_xGL_mem hF⟩
  neg_center g := by
    rw [uniModelOps_mem_center_iff hF hq, Subtype.ext_iff, Subtype.ext_iff]
    rfl
  neg_sq := Subtype.ext xGL_mul_self
  neg_ne := fun h => xGL_ne_one (uniModelOps_two_ne_zero hF hq) (congrArg Subtype.val h)
  norm s hs2 hs1 hsn := by
    obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
    have h2 := uniModelOps_two_ne_zero hF hq
    have hT : ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
      have := congrArg (fun x : ↥(StatedSU 4 (p ^ f) F) =>
        ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hs2
      simpa using this
    have h1 : ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ 1 := fun h =>
      hs1 (Subtype.ext (Units.ext (by simpa using h)))
    have hm1 : ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ -1 := fun h =>
      hsn (Subtype.ext (Units.ext (by rw [h]; exact uniModelOps_xGL_matrix.symm)))
    obtain ⟨g, hg, hTP⟩ := hmat_uni hF h2 s hT h1 hm1
    obtain ⟨k, hk⟩ := exists_conj_yK_of_matrix (ModelData.uni hF) s g hg hTP
    exact ⟨k, hk⟩
  swap := ⟨⟨swapGL F, uniModelOps_swapGL_mem hF⟩, Subtype.ext (by
    change swapGL F * yGL F * (swapGL F)⁻¹ = xGL F * yGL F
    rw [swapGL_mul_yGL_mul_inv, uniModelOps_xGL_mul_yGL])⟩

end Uni

end CFSG.GH74.Generic.S1.Exo
