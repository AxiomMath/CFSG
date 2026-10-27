module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUb

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.LinearGroups
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def toSesqU {A : GL (Fin 4) K} (hA : A ∈ uMat h 4) :
    sesqUnitaryGroup (stdHermForm h 4) :=
  ⟨Matrix.GeneralLinearGroup.toLin A, fun x y => by
    change stdHermForm h 4 ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ x)
      ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ y) = stdHermForm h 4 x y
    rw [stdHermForm_eq_gramForm, gramForm_mulVec, Matrix.mul_one, (mem_uMat h).1 hA]⟩

theorem toSesqU_apply {A : GL (Fin 4) K} (hA : A ∈ uMat h 4) (v : Fin 4 → K) :
    unitaryOp (toSesqU h hA) v = (A : Matrix (Fin 4) (Fin 4) K) *ᵥ v := rfl

theorem unitaryOp_mul' (X Y : sesqUnitaryGroup (stdHermForm h 4)) :
    unitaryOp (X * Y) = unitaryOp X * unitaryOp Y := rfl

theorem toSesq_conj {A : GL (Fin 4) K} (hA : A ∈ uMat h 4) (g g' : unitarySU p f K 4)
    (hg : (g' : GL (Fin 4) K) = A * g * A⁻¹) :
    toSesq h 4 g' = toSesqU h hA * toSesq h 4 g * (toSesqU h hA)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  refine LinearMap.ext fun v => ?_
  change ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v =
    unitaryOp (toSesqU h hA * toSesq h 4 g * (toSesqU h hA)⁻¹) v
  have hinv : ∀ w, unitaryOp ((toSesqU h hA)⁻¹) w =
      ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ w := by
    intro w
    have e : (toSesqU h hA)⁻¹ = toSesqU h (inv_mem hA) := by
      rw [inv_eq_iff_mul_eq_one]
      apply Subtype.ext
      apply Units.ext
      refine LinearMap.ext fun z => ?_
      change (A : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [e]
    rfl
  rw [unitaryOp_mul' h, unitaryOp_mul' h, Module.End.mul_apply, Module.End.mul_apply, hinv]
  change _ = (A : Matrix (Fin 4) (Fin 4) K) *ᵥ (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
    (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v))
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg, Units.val_mul, Units.val_mul]

theorem mem_normOne_of_eq_smul {X : sesqUnitaryGroup (stdHermForm h 4)} {c : K}
    (hX : ∀ v, unitaryOp X v = c • v) (hc : h.norm c = 1) : X ∈ sesqNormOneScalars h _ :=
  ⟨c, hc, LinearMap.ext fun v => by rw [hX]; rfl⟩

theorem orderOf_mk_toSesqU (hp2 : p ≠ 2) {A : GL (Fin 4) K}
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hα : IsCU h A α) (hα1 : α ≠ 1)
    (hα2 : α ^ 2 = 1) :
    orderOf (QuotientGroup.mk (toSesqU h hα.1) : sesqProjUnitary h (stdHermForm h 4)) = 2 := by
  classical
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have hAA : IsCU h (A * A) 1 := by rw [← hα2, sq]; exact hα.mul h hα
    obtain ⟨c, hc⟩ := eq_smul_one_of_isCU_one h hp2 hAA
    refine mem_normOne_of_eq_smul h (c := c) (fun v => ?_) ?_
    · rw [sq, unitaryOp_mul' h, Module.End.mul_apply, toSesqU_apply,
        toSesqU_apply, Matrix.mulVec_mulVec, ← Units.val_mul, hc, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    · have hU : A * A ∈ uMat h 4 := mul_mem hα.1 hα.1
      rw [mem_uMat, hc] at hU
      have e := congrFun (congrFun hU 0) 0
      simp [Matrix.mul_apply, Fin.sum_univ_four] at e
      rw [UnitaryFieldData.norm, mul_comm]
      exact e
  · intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨d, -, hd⟩ := h1
    apply hα1
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := thU_surjective x
    rw [hα.apply h, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    have hAd : ∀ v, (A : Matrix (Fin 4) (Fin 4) K) *ᵥ v = d • v := fun v => by
      have := congrArg (fun T : Module.End K (Fin 4 → K) => T v) hd
      simp only [LinearMap.smul_apply, Module.End.one_apply] at this
      exact this
    have hd0 : d ≠ 0 := by
      intro h0
      have := hAd (Pi.single 0 1)
      rw [h0, zero_smul] at this
      have h2 := congrArg (fun w => (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ w) 0)
        this
      simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec, Matrix.mulVec_zero] at h2
      simp at h2
    have hAm : (A : Matrix (Fin 4) (Fin 4) K) = d • 1 := by
      ext i j
      have := congrFun (hAd (Pi.single j 1)) i
      rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      simpa [Matrix.mulVec_single, Pi.single_apply] using this
    have hAc : A ∈ Subgroup.center (GL (Fin 4) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨Units.mk0 d hd0, Units.ext (by
        rw [GeneralLinearGroup.coe_scalar, hAm, Units.val_mk0, Matrix.scalar_apply,
          Matrix.smul_one_eq_diagonal])⟩
    change A * (g : GL (Fin 4) K) * A⁻¹ = g
    rw [(Subgroup.mem_center_iff.mp hAc g).symm, mul_assoc, mul_inv_cancel, mul_one]

end DiagU

end CFSG.ComponentClassification.CatFactsL4U4
