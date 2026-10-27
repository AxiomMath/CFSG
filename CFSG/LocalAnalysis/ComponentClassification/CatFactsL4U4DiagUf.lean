module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUb
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def CAU (J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))) :
    Subgroup (MulAut (StatedProj (StatedSU 4 (p ^ f) K))) where
  carrier := {g | ∀ x ∈ J', g x = x}
  mul_mem' := fun {a b} ha hb x hx => by rw [MulAut.mul_apply, hb x hx, ha x hx]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {a} ha x hx => by
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact (ha x hx).symm

theorem glAut_refl (X : GL (Fin 4) K) : glAut (RingEquiv.refl K) X = X := by
  change glAut 1 X = X
  rw [map_one]
  rfl

theorem IsCU.of_eq_smul {A B : GL (Fin 4) K} {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hα : IsCU h A α) (hB : B ∈ uMat h 4) {c : K}
    (hBA : (B : Matrix (Fin 4) (Fin 4) K) = c • (A : Matrix (Fin 4) (Fin 4) K)) : IsCU h B α := by
  have hc : c ≠ 0 := by
    rintro rfl
    have h1 : (B : Matrix (Fin 4) (Fin 4) K) * (B⁻¹ : GL (Fin 4) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hBA, zero_smul, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  have hB' : B = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 c hc) * A := Units.ext (by
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hBA, Units.val_mk0, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul])
  have hcen : GeneralLinearGroup.scalar (Fin 4) (Units.mk0 c hc) ∈
      Subgroup.center (GL (Fin 4) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  refine ⟨hB, fun g g' hg => hα.2 g g' ?_⟩
  set s := GeneralLinearGroup.scalar (Fin 4) (Units.mk0 c hc)
  rw [hg, hB', _root_.mul_inv_rev]
  calc s * A * (g : GL (Fin 4) K) * (A⁻¹ * s⁻¹) = s * (A * g * A⁻¹) * s⁻¹ := by group
    _ = (A * g * A⁻¹) * s * s⁻¹ := by rw [← Subgroup.mem_center_iff.mp hcen (A * g * A⁻¹)]
    _ = A * g * A⁻¹ := by group

theorem isCU_one_of_eq_smul {B : GL (Fin 4) K} (hB : B ∈ uMat h 4) {c : K}
    (hBc : (B : Matrix (Fin 4) (Fin 4) K) = c • 1) : IsCU h B 1 :=
  (isCU_one h).of_eq_smul h hB (c := c) (by rw [hBc, Units.val_one])

theorem blk_of_mem_AU (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJU : ∀ c : K, thU p f K (uU h P hP c) ∈ J') (hJL : ∀ c : K, thU p f K (uL h P hP c) ∈ J')
    {B : GL (Fin 4) K} {a : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hB : IsCU h B a)
    (ha : a ∈ CAU J') :
    ∃ x y : K, ((P⁻¹ * B * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = blk x 0 0 y ∧
      h.bar x * y = 1 := by
  classical
  have : Finite K := h.finite
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨hA, hlift⟩ := lift_of_isCU h hB
  obtain ⟨x, b, e, y, hblk, hun, hcase⟩ := blk_of_fix h hp2 P hP hμ ((mem_uMat h).1 hB.1) hlift
    (ha _ (hJU 1)) (ha _ (hJL 1)) (ha _ (hJU μ))
  rw [glAut_refl] at hblk
  rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hb, -, -⟩
  · refine ⟨x, y, hblk, ?_⟩
    rw [map_zero, mul_zero, zero_add] at hun
    exact hun
  · exfalso
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    exact hc (hb c).symm

theorem val_eq_of_conj (P M : GL (Fin 4) K) :
    (M : Matrix (Fin 4) (Fin 4) K) = (P : Matrix (Fin 4) (Fin 4) K) *
      ((P⁻¹ * M * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  group

theorem blk_eq_smul_one (x : K) : blk x 0 0 x = x • (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem blk_neg_eq_smul_X1 {l : K} (hl : l ≠ 0) (x : K) : blk x 0 0 (-x) = (x / l) • X1 l := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, X1] <;> field_simp

theorem blk_sq (x y : K) : blk x 0 0 y * blk x 0 0 y = blk (x * x) 0 0 (y * y) :=
  blk_mul_blk x y x y

theorem eq_one_or_eq_of_sq_AU (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl0 : l ≠ 0) {A : GL (Fin 4) K} {z : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hz : IsCU h A z) (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJU : ∀ c : K, thU p f K (uU h P hP c) ∈ J') (hJL : ∀ c : K, thU p f K (uL h P hP c) ∈ J')
    {a : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (ha : a ∈ CAU J' ⊓ InnU p f K h)
    (h2 : a ^ 2 = 1) : a = 1 ∨ a = z := by
  obtain ⟨haC, B, hB⟩ := Subgroup.mem_inf.1 ha
  obtain ⟨x, y, hblk, -⟩ := blk_of_mem_AU h hp2 P hP hJU hJL hB haC
  have hBB : IsCU h (B * B) 1 := by rw [← h2, sq]; exact hB.mul h hB
  obtain ⟨c, hc⟩ := eq_smul_one_of_isCU_one h hp2 hBB
  have hsq : blk (x * x) 0 0 (y * y) = c • 1 := by
    rw [← blk_sq, ← hblk, ← Units.val_mul]
    have e : P⁻¹ * B * P * (P⁻¹ * B * P) = P⁻¹ * (B * B) * P := by group
    rw [e, Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e0 := congrFun (congrFun hsq 0) 0
  have e2 := congrFun (congrFun hsq 2) 2
  simp [blk] at e0 e2
  have hxy : (x - y) * (x + y) = 0 := by linear_combination e0 - e2
  rcases mul_eq_zero.1 hxy with h0 | h0
  · left
    have hyx : y = x := (sub_eq_zero.1 h0).symm
    rw [hyx, blk_eq_smul_one] at hblk
    have hBs : (B : Matrix (Fin 4) (Fin 4) K) = x • 1 := by
      rw [val_eq_of_conj P B, hblk, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        ← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact hB.unique h (isCU_one_of_eq_smul h hB.1 hBs)
  · right
    have hyx : y = -x := by linear_combination h0
    rw [hyx, blk_neg_eq_smul_X1 hl0] at hblk
    have hAm : (A : Matrix (Fin 4) (Fin 4) K) =
        (P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
      rw [← hAP, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one]
    have hBs : (B : Matrix (Fin 4) (Fin 4) K) = (x / l) • (A : Matrix (Fin 4) (Fin 4) K) := by
      rw [val_eq_of_conj P B, hblk, Matrix.mul_smul, Matrix.smul_mul, hAm]
    exact hB.unique h (hz.of_eq_smul h hB.1 hBs)

end DiagU

end CFSG.ComponentClassification.CatFactsL4U4
