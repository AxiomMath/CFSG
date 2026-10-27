module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5Bar

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K]

abbrev spJ (L : Type) [Field L] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) L :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem spJ_mul_self (L : Type) [Field L] : spJ L * spJ L = -1 := by
  rw [spJ, Matrix.fromBlocks_multiply]
  simp
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem map_spJ {L L' : Type} [Field L] [Field L'] (φ : L →+* L') :
    (spJ L).map φ = spJ L' := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [spJ, Matrix.one_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem spJ_spec (L : Type) [Field L] (x : ↥(StatedSp 2 L)) :
    ((x : GL (Fin 2 ⊕ Fin 2) L) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) L)ᵀ * spJ L *
        ((x : GL (Fin 2 ⊕ Fin 2) L) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) L) = spJ L ∧
      ((x : GL (Fin 2 ⊕ Fin 2) L) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) L).det = 1 := by
  have hM : ((x : GL (Fin 2 ⊕ Fin 2) L) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) L) ∈
      symplecticGroup (Fin 2) L :=
    TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp
      ((CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := L)).le x.2)
  exact ⟨(CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup _).mpr hM,
    SymplecticGroup.det_eq_one hM⟩

@[expose] noncomputable def spInclMat (h : UnitaryFieldData p f K) :
    ↥(StatedSp 2 h.fixedField) →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  (RingHom.mapMatrix h.fixedField.subtype).toMonoidHom.comp
    ((Units.coeHom (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField)).comp
      (StatedSp 2 h.fixedField).subtype)

theorem spInclMat_apply (h : UnitaryFieldData p f K) (x : ↥(StatedSp 2 h.fixedField)) :
    spInclMat h x = ((x : GL (Fin 2 ⊕ Fin 2) h.fixedField) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField).map h.fixedField.subtype := rfl

theorem map_bar_spInclMat (h : UnitaryFieldData p f K) (x : ↥(StatedSp 2 h.fixedField)) :
    (spInclMat h x).map h.bar = spInclMat h x := by
  rw [spInclMat_apply, Matrix.map_map]
  congr 1
  funext c
  exact h.mem_fixedField.mp c.2

theorem det_spInclMat (h : UnitaryFieldData p f K) (x : ↥(StatedSp 2 h.fixedField)) :
    (spInclMat h x).det = 1 := by
  rw [spInclMat_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, (spJ_spec _ x).2, map_one]

theorem spInclMat_spec (h : UnitaryFieldData p f K) (x : ↥(StatedSp 2 h.fixedField)) :
    (spInclMat h x)ᵀ * spJ K * spInclMat h x = spJ K := by
  have h1 := congrArg (fun M => Matrix.map M h.fixedField.subtype) (spJ_spec _ x).1
  simp only [Matrix.map_mul, Matrix.transpose_map, map_spJ] at h1
  rw [spInclMat_apply]
  exact h1


theorem mem_statedScalars_of_spInclMat (h : UnitaryFieldData p f K) {x : ↥(StatedSp 2 h.fixedField)}
    {c' : K} (hx : spInclMat h x = c' • 1) :
    (x : GL (Fin 2 ⊕ Fin 2) h.fixedField) ∈ StatedScalars (Fin 2 ⊕ Fin 2) h.fixedField := by
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField :=
    ((x : GL (Fin 2 ⊕ Fin 2) h.fixedField) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField)
    with hM
  set c₀ : h.fixedField := M (Sum.inl 0) (Sum.inl 0) with hc₀
  have hMs : M = c₀ • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) := by
    have hc'₀ : c' = (c₀ : K) := by
      have e0 := congrFun (congrFun hx (Sum.inl 0)) (Sum.inl 0)
      rw [spInclMat_apply, Matrix.map_apply] at e0
      simpa using e0.symm
    ext i j
    have e1 := congrFun (congrFun hx i) j
    rw [spInclMat_apply, Matrix.map_apply] at e1
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e1 ⊢
      rw [← hc'₀]
      exact e1
    · simp only [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero] at e1 ⊢
      exact e1
  have hc0 : c₀ ≠ 0 := by
    intro h0
    have h1 := (spJ_spec _ x).2
    rw [← hM, hMs, h0, zero_smul] at h1
    simp at h1
  refine ⟨Units.mk0 c₀ hc0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  exact hMs.symm

theorem exists_sp4_comm_of_bar (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    {A : GL (HypIndex 2 0) K} (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = (-1 : K) • 1) :
    ∃ ψ : ↥(StatedSp 2 h.fixedField) →* hypSU h 2 0,
      (∀ x, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
          ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
            (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) ∧
      ∀ x, hypProj h 2 0 (ψ x) = 1 →
        (x : GL (Fin 2 ⊕ Fin 2) h.fixedField) ∈ StatedScalars (Fin 2 ⊕ Fin 2) h.fixedField := by
  have := h.finite
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have hn1 : 1 ≤ finrank K (HypIndex 2 0 → K) := by
    rw [finrank_hypIndex_fun]
    omega
  have hc : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hμ : ∀ v, conjOp h (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      (conjOp h (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) v) =
        ((Units.mk0 (-1 : K) hc : Kˣ) : K) • v := conjOp_conjOp hAA
  obtain ⟨-, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd hn1 (hypForm_isSymm h) (hypForm_separatingLeft h) _ (conjOp_bijective hc hAA)
    (hypForm_conjOp hA) (Units.mk0 (-1 : K) hc) hμ
  obtain ⟨-, hfin, -, -, halt⟩ := hall b t hb ht
  rw [finrank_hypIndex_fun] at hfin
  have hfix : ∀ w ∈ conjFixed h ((b : K) • conjOp h (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)),
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ (fun a => h.bar (w a)) =
        ((b : K))⁻¹ • w := fun w hw => by
    have h1 : (b : K) • ((A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
        fun a => h.bar (w a)) = w := mem_conjFixed.mp hw
    rw [← h1, smul_smul, inv_mul_cancel₀ b.ne_zero, one_smul, h1]
  obtain ⟨B, hBH, hBalt, hBnd, -, -⟩ := halt (Units.ext (by simp))
  obtain ⟨m, bW, hm, hb1, hb2, hb3⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_blueprint_symplectic_basis B
      hBalt hBnd
  have hm2 : m = 2 := by omega
  subst hm2
  have hBval : ∀ i j, ((B (bW i) (bW j) : h.fixedField) : K) = spJ K i j := by
    rintro (i | i) (j | j)
    · rw [hb1]
      simp [spJ]
    · rw [hb3]
      by_cases hij : i = j
      · subst hij
        simp [spJ]
      · simp [spJ, hij]
    · rw [← hBalt.neg_eq, hb3]
      by_cases hij : j = i
      · subst hij
        simp [spJ]
      · simp [spJ, hij, Ne.symm hij]
    · rw [hb2]
      simp [spJ]
  have hG : ((colMat (fun i => (bW i : HypIndex 2 0 → K))).map h.bar)ᵀ * hypGram 2 0 K *
      colMat (fun i => (bW i : HypIndex 2 0 → K)) = (t : K) • spJ K := by
    rw [gram_colMat_eq_hypForm]
    ext i j
    rw [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ← hBval i j, hBH (bW i) (bW j),
      ← mul_assoc, mul_inv_cancel₀ t.ne_zero, one_mul]
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  obtain ⟨ψ, hψc, hψs⟩ := exists_comm_conj_of_cols' h hA hc hAA
    (fun i => (bW i : HypIndex 2 0 → K)) (fun i => hfix _ (bW i).2)
    (Gi := (-((t : K)⁻¹)) • spJ K)
    (by
      rw [hG, smul_mul_smul_comm, spJ_mul_self, neg_mul, inv_mul_cancel₀ ht0, neg_smul, one_smul,
        neg_neg])
    (by
      rw [hG, smul_mul_smul_comm, spJ_mul_self, mul_neg, mul_inv_cancel₀ ht0, neg_smul, one_smul,
        neg_neg])
    (by
      rw [hG, Matrix.map_smul' _ _ _ (map_mul h.bar), ht, map_spJ, smul_smul, neg_one_mul])
    (spInclMat h) (map_bar_spInclMat h)
    (fun x => by
      rw [hG, map_bar_spInclMat h x, Matrix.mul_smul, Matrix.smul_mul, spInclMat_spec h x])
    (det_spInclMat h)
  refine ⟨ψ, hψc, fun x hx => ?_⟩
  rw [← MonoidHom.mem_ker, ker_hypProj] at hx
  obtain ⟨c', hc'⟩ := exists_eq_smul_one_of_mem_hypScalars hx
  exact mem_statedScalars_of_spInclMat h (hψs x c' hc')

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
