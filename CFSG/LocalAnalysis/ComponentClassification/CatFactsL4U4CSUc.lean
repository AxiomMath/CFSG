module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUf

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace CSU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem thU_eq_one_of_val {g : unitarySU p f K 4} {c : K}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = c • 1) : thU p f K g = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hg
    have e := congrArg (fun M => M * (((g : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) hg
    simp only [Matrix.zero_mul] at e
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at e
    exact one_ne_zero e
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact ⟨Units.mk0 c hc0, Units.ext (by
    rw [GeneralLinearGroup.coe_scalar, hg, Units.val_mk0, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal])⟩

include h in
theorem conj_injective_U (hp2 : p ≠ 2) :
    Function.Injective (MulAut.conj : StatedProj (StatedSU 4 (p ^ f) K) →* _) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, rfl⟩ := thU_surjective x
  have h1 : IsCU h (g : GL (Fin 4) K) 1 := hx ▸ isCU_conj h g
  obtain ⟨c, hc⟩ := eq_smul_one_of_isCU_one h hp2 h1
  exact thU_eq_one_of_val hc

omit h in
theorem blk_eq_smul (x : K) : blk x 0 0 x = x • (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem unitaryConjHom_eq_inv_of_bar (P : GL (Fin 4) K) {B : GL (Fin 4) K} {φ : K ≃+* K}
    (hφ : ∀ c, φ c = h.bar c)
    {hB : ∀ g : unitarySU p f K 4, B * glAut φ (g : GL (Fin 4) K) * B⁻¹ ∈ unitarySU p f K 4}
    {b e : K}
    (hBP : ((P⁻¹ * B * glAut φ P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = blk 0 b e 0)
    (U : unitarySU p f K 4) {x y : K} (hU : cP P U = blk x 0 0 y) (hxy : h.bar x * y = 1) :
    ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom B φ hB U = U⁻¹ := by
  set A'' := P⁻¹ * B * glAut φ P with hA''
  set V : GL (Fin 4) K := P⁻¹ * (U : GL (Fin 4) K) * P with hV
  have hVm : (V : Matrix (Fin 4) (Fin 4) K) = blk x 0 0 y := by
    rw [← hU, hV, cP, Units.val_mul, Units.val_mul]
  have hyx : h.bar y * x = 1 := by
    have := congrArg h.bar hxy
    rw [map_mul, h.bar_bar, map_one] at this
    rw [mul_comm]
    exact this
  have key : A'' * glAut φ V * A''⁻¹ * V = 1 := by
    apply Units.ext
    have hW : ((glAut φ V : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        blk (h.bar x) 0 0 (h.bar y) := by
      rw [UnitaryHigher.coe_glAut, hVm]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [blk, hφ]
    have hAA : (A'' : Matrix (Fin 4) (Fin 4) K) * ((A''⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hW, hVm, hBP, blk_swap,
      Matrix.mul_assoc (blk (h.bar y) 0 0 (h.bar x)), ← hBP, hAA, Matrix.mul_one, blk_mul_blk,
      hyx, hxy, blk_one, Units.val_one]
  apply Subtype.ext
  change B * glAut φ (U : GL (Fin 4) K) * B⁻¹ = ((U⁻¹ : unitarySU p f K 4) : GL (Fin 4) K)
  rw [Subgroup.coe_inv]
  have hBeq : B = P * A'' * (glAut φ P)⁻¹ := by rw [hA'']; group
  have hUeq : (U : GL (Fin 4) K) = P * V * P⁻¹ := by rw [hV]; group
  have hVi : V⁻¹ = A'' * glAut φ V * A''⁻¹ := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv]
    exact key
  rw [hBeq, hUeq, map_mul, map_mul, map_inv, ← hUeq]
  calc P * A'' * (glAut φ P)⁻¹ * (glAut φ P * glAut φ V * (glAut φ P)⁻¹) *
      (P * A'' * (glAut φ P)⁻¹)⁻¹ = P * (A'' * glAut φ V * A''⁻¹) * P⁻¹ := by group
    _ = P * V⁻¹ * P⁻¹ := by rw [hVi]
    _ = (P * V * P⁻¹)⁻¹ := by group
    _ = (U : GL (Fin 4) K)⁻¹ := by rw [← hUeq]

@[expose] noncomputable def sU (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG) :
    unitarySU p f K 4 :=
  hypSU h P hP (blk 0 1 1 0) (unitary_swap h) det_swap

theorem conj_swap_inv (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {B : GL (Fin 4) K} {a : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hB : IsCU h B a)
    {x y : K} (hBP : ((P⁻¹ * B * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = blk x 0 0 y) :
    MulAut.conj (thU p f K (sU h P hP)) * a * (MulAut.conj (thU p f K (sU h P hP)))⁻¹ = a⁻¹ := by
  set s := sU h P hP with hs
  have hsC := isCU_conj h s
  have h1 : IsCU h ((s : GL (Fin 4) K) * B * (s : GL (Fin 4) K)⁻¹)
      (MulAut.conj (thU p f K s) * a * (MulAut.conj (thU p f K s))⁻¹) :=
    (hsC.mul h hB).mul h hsC.inv
  set W₀ : GL (Fin 4) K := toGL (blk 0 1 1 0) det_swap with hW₀
  have hsW : (s : GL (Fin 4) K) = P * W₀ * P⁻¹ := rfl
  set Bm := P⁻¹ * B * P with hBm
  have hBeq : B = P * Bm * P⁻¹ := by rw [hBm]; group
  have hmat : (((s : GL (Fin 4) K) * B * (s : GL (Fin 4) K)⁻¹ * B : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = (x * y) • 1 := by
    have e : (s : GL (Fin 4) K) * B * (s : GL (Fin 4) K)⁻¹ * B =
        P * (W₀ * Bm * W₀⁻¹ * Bm) * P⁻¹ := by rw [hsW, hBeq]; group
    have hWW : (W₀ : Matrix (Fin 4) (Fin 4) K) * ((W₀⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hW₀m : (W₀ : Matrix (Fin 4) (Fin 4) K) = blk 0 1 1 0 := coe_toGL _ _
    have hinner : ((W₀ * Bm * W₀⁻¹ * Bm : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (x * y) • 1 := by
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hBP, hW₀m, blk_swap,
        Matrix.mul_assoc (blk y 0 0 x), ← hW₀m, hWW, Matrix.mul_one, blk_mul_blk, mul_comm y x,
        blk_eq_smul]
    have hPP : (P : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [e, Units.val_mul, Units.val_mul, hinner, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hPP]
  have hsB : (((s : GL (Fin 4) K) * B * (s : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = (x * y) • ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    have e2 := congrArg (fun M => M * ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hmat
    rw [Units.val_mul ((s : GL (Fin 4) K) * B * (s : GL (Fin 4) K)⁻¹) B, Matrix.mul_assoc,
      ← Units.val_mul B, mul_inv_cancel, Units.val_one, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul] at e2
    exact e2
  have h2 : IsCU h ((s : GL (Fin 4) K) * B * (s : GL (Fin 4) K)⁻¹) a⁻¹ :=
    (hB.inv h).of_eq_smul h h1.1 hsB
  exact h1.unique h h2

end CSU

end CFSG.ComponentClassification.CatFactsL4U4
