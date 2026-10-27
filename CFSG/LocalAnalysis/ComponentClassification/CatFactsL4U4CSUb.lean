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

omit h in
theorem mem_C_iff (P : GL (Fin 4) K) {l : K} {A : GL (Fin 4) K}
    (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l) (g : unitarySU p f K 4) :
    g ∈ (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype ↔
      cP P g * X1 l = X1 l * cP P g := by
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPP' : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAm : (A : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    rw [← hAP, Matrix.mul_assoc, hPP, Matrix.mul_one]
  rw [Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have e := congrArg (fun X : GL (Fin 4) K => (X : Matrix (Fin 4) (Fin 4) K)) hg
    simp only [Units.val_mul] at e
    rw [hAm] at e
    have e' := congrArg (fun M => (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * M *
      (P : Matrix (Fin 4) (Fin 4) K)) e
    simp only [Matrix.mul_assoc, hPP', Matrix.mul_one] at e'
    simp only [← Matrix.mul_assoc, hPP', Matrix.one_mul] at e'
    simpa only [cP, Matrix.mul_assoc] using e'
  · intro hg
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hAm, val_eq_cP P g]
    have e1 : (P : Matrix (Fin 4) (Fin 4) K) * cP P g * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
        ((P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
        (P : Matrix (Fin 4) (Fin 4) K) * (cP P g * X1 l) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) (P : Matrix (Fin 4) (Fin 4) K),
        hPP', Matrix.one_mul]
    have e2 : (P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
        ((P : Matrix (Fin 4) (Fin 4) K) * cP P g * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
        (P : Matrix (Fin 4) (Fin 4) K) * (X1 l * cP P g) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) (P : Matrix (Fin 4) (Fin 4) K),
        hPP', Matrix.one_mul]
    rw [e1, e2, hg]

include h in
theorem comm_of_mem_C (hp2 : p ≠ 2) (P : GL (Fin 4) K) {l : K} (hl0 : l ≠ 0) {A : GL (Fin 4) K}
    (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l) {U : unitarySU p f K 4} {x y : K}
    (hU : cP P U = blk x 0 0 y) {g : unitarySU p f K 4}
    (hg : g ∈ (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype) : U * g = g * U := by
  have hBD := isBD_of_comm_X1 (two_ne_zero_of_odd h hp2) hl0 ((mem_C_iff P hAP g).1 hg)
  apply eq_of_cP_eq P
  rw [cP_mul, cP_mul, hU, blk_comm_of_isBD hBD]

include h in
theorem conj_mem_CAU_of_blk (hp2 : p ≠ 2) (P : GL (Fin 4) K) {l : K} (hl0 : l ≠ 0)
    {A : GL (Fin 4) K} (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJeq : J' = (⁅(Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype,
      (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype⁆ :
        Subgroup (unitarySU p f K 4)).map (thU p f K))
    {U : unitarySU p f K 4} {x y : K} (hU : cP P U = blk x 0 0 y) :
    MulAut.conj (thU p f K U) ∈ CAU J' := by
  intro z hz
  rw [hJeq] at hz
  obtain ⟨g, hg, rfl⟩ := hz
  have hgC : g ∈ (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype :=
    (Subgroup.commutator_le.2 fun a ha b hb =>
      mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hg
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, comm_of_mem_C h hp2 P hl0 hAP hU hgC,
    mul_inv_cancel_right]

theorem conj_mem_C_of_comm (hp2 : p ≠ 2) {A : GL (Fin 4) K}
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hα : IsCU h A α) (Z : unitarySU p f K 4)
    (hZ : MulAut.conj (thU p f K Z) * α = α * MulAut.conj (thU p f K Z)) {g : unitarySU p f K 4}
    (hg : g ∈ (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype) :
    Z * g * Z⁻¹ ∈ (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype := by
  set Zg : GL (Fin 4) K := (Z : GL (Fin 4) K) with hZg
  have hZu := isCU_conj h Z
  have h1 : IsCU h (A⁻¹ * (Zg * A * Zg⁻¹)) 1 := by
    have e : (1 : MulAut (StatedProj (StatedSU 4 (p ^ f) K))) =
        α⁻¹ * (MulAut.conj (thU p f K Z) * α * (MulAut.conj (thU p f K Z))⁻¹) := by
      rw [hZ, mul_inv_cancel_right, inv_mul_cancel]
    rw [e]
    exact hα.inv h |>.mul h ((hZu.mul h hα).mul h hZu.inv)
  obtain ⟨c, hc⟩ := eq_smul_one_of_isCU_one h hp2 h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    have e := congrArg (fun M => M * (((A⁻¹ * (Zg * A * Zg⁻¹))⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) hc
    simp only [Matrix.zero_mul] at e
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at e
    exact one_ne_zero e
  set cu : Kˣ := Units.mk0 c hc0 with hcu
  have hscal : A⁻¹ * (Zg * A * Zg⁻¹) = GeneralLinearGroup.scalar (Fin 4) cu := by
    apply Units.ext
    rw [hc, GeneralLinearGroup.coe_scalar, hcu, Units.val_mk0, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hcen : GeneralLinearGroup.scalar (Fin 4) cu ∈ Subgroup.center (GL (Fin 4) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨cu, rfl⟩
  set S := GeneralLinearGroup.scalar (Fin 4) cu with hS
  have hZA : Zg * A * Zg⁻¹ = A * S := by rw [← hscal]; group
  rw [Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hZg]
  have hAS : A = Zg * A * Zg⁻¹ * S⁻¹ := by rw [hZA]; group
  calc Zg * g * Zg⁻¹ * A = Zg * g * Zg⁻¹ * (Zg * A * Zg⁻¹ * S⁻¹) := by rw [← hAS]
    _ = Zg * ((g : GL (Fin 4) K) * A) * Zg⁻¹ * S⁻¹ := by group
    _ = Zg * (A * g) * Zg⁻¹ * S⁻¹ := by rw [hg]
    _ = (Zg * A * Zg⁻¹) * (Zg * g * Zg⁻¹) * S⁻¹ := by group
    _ = A * S * (Zg * g * Zg⁻¹) * S⁻¹ := by rw [hZA]
    _ = A * (Zg * g * Zg⁻¹) * (S * S⁻¹) := by
        rw [mul_assoc A S, ← Subgroup.mem_center_iff.mp hcen (Zg * g * Zg⁻¹)]; group
    _ = A * (Zg * g * Zg⁻¹) := by rw [mul_inv_cancel, mul_one]

theorem normalizes_of_comm (hp2 : p ≠ 2) {A : GL (Fin 4) K}
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hα : IsCU h A α)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJeq : J' = (⁅(Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype,
      (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype⁆ :
        Subgroup (unitarySU p f K 4)).map (thU p f K))
    {z : StatedProj (StatedSU 4 (p ^ f) K)} (hz : MulAut.conj z * α = α * MulAut.conj z)
    (y : StatedProj (StatedSU 4 (p ^ f) K)) : y ∈ J' ↔ z * y * z⁻¹ ∈ J' := by
  set C := (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype with hC
  obtain ⟨Z, rfl⟩ := thU_surjective z
  have hZi : MulAut.conj (thU p f K Z⁻¹) * α = α * MulAut.conj (thU p f K Z⁻¹) := by
    rw [map_inv, map_inv]
    calc (MulAut.conj (thU p f K Z))⁻¹ * α =
        (MulAut.conj (thU p f K Z))⁻¹ * (α * MulAut.conj (thU p f K Z)) *
          (MulAut.conj (thU p f K Z))⁻¹ := by group
      _ = (MulAut.conj (thU p f K Z))⁻¹ * (MulAut.conj (thU p f K Z) * α) *
          (MulAut.conj (thU p f K Z))⁻¹ := by rw [hz]
      _ = α * (MulAut.conj (thU p f K Z))⁻¹ := by group
  have hle : ∀ W : unitarySU p f K 4,
      MulAut.conj (thU p f K W) * α = α * MulAut.conj (thU p f K W) →
      ∀ g ∈ ⁅C, C⁆, W * g * W⁻¹ ∈ ⁅C, C⁆ := by
    intro W hW g hg
    have h1 : (⁅C, C⁆ : Subgroup (unitarySU p f K 4)).map (MulAut.conj W).toMonoidHom ≤ ⁅C, C⁆ := by
      rw [Subgroup.map_commutator]
      apply Subgroup.commutator_mono <;>
      · rintro _ ⟨c, hc, rfl⟩
        exact conj_mem_C_of_comm h hp2 hα W hW hc
    exact h1 ⟨g, hg, rfl⟩
  rw [hJeq]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨Z * g * Z⁻¹, hle Z hz g hg, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨g, hg, hgy⟩
    refine ⟨Z⁻¹ * g * Z⁻¹⁻¹, hle Z⁻¹ hZi g hg, ?_⟩
    rw [inv_inv, map_mul, map_mul, map_inv, hgy]
    group

end CSU

end CFSG.ComponentClassification.CatFactsL4U4
