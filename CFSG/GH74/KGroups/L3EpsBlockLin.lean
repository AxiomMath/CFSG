module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.GH74.KGroups.L3Eps

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

section SL2

theorem sl2c_center_scalar {A : SL(2, F)} (hA : A ∈ center SL(2, F)) :
    ∃ r : F, r ^ 2 = 1 ∧ (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) r := by
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  exact ⟨r, by simpa using hr, hA'.symm⟩

theorem sl2c_scalar_eq {A : SL(2, F)} {r : F} (hr : r ^ 2 = 1)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) r) : A = 1 ∨ A = -1 := by
  have h : r * r = 1 := by rw [← sq]; exact hr
  rcases mul_self_eq_one_iff.1 h with rfl | rfl
  · left
    apply Subtype.ext
    rw [hA]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  · right
    apply Subtype.ext
    rw [hA]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

theorem sl2c_center_eq {A : SL(2, F)} (hA : A ∈ center SL(2, F)) : A = 1 ∨ A = -1 := by
  obtain ⟨r, hr, hA'⟩ := sl2c_center_scalar hA
  exact sl2c_scalar_eq hr hA'

theorem sl2c_sq_eq_one (hF : ringChar F ≠ 2) {A : SL(2, F)} (hA : A * A = 1) : A = 1 ∨ A = -1 := by
  have h := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F)) hA
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  by_cases hs : (A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
  · exfalso
    have hd : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = -(A : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      linear_combination hs
    apply h2
    rw [hd] at hdet h11
    linear_combination -(hdet + h00)
  · have hb : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      have : (A : Matrix (Fin 2) (Fin 2) F) 0 1 * ((A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
        linear_combination h01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have : (A : Matrix (Fin 2) (Fin 2) F) 1 0 * ((A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
        linear_combination h10
      exact (mul_eq_zero.1 this).resolve_right hs
    rw [hb, hc] at h00 h11 hdet
    have ha2 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by linear_combination h00
    have hd2 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by linear_combination hdet
    have hd : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      have h0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
        intro h0; rw [h0] at ha2; simp at ha2
      apply mul_left_cancel₀ h0
      rw [hd2, ha2]
    apply sl2c_scalar_eq (r := (A : Matrix (Fin 2) (Fin 2) F) 0 0) (by linear_combination ha2)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hb, hc, hd]

theorem isQuasisimple_sl2c [Finite F] (h4 : 4 ≤ Nat.card F) : CFSG.IsQuasisimple SL(2, F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h4' : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨t, ht⟩
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr h4')
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr h4')
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  simp only [not_exists, not_not] at hab
  have hle : commutator SL(2, F) ≤ Subgroup.center SL(2, F) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center SL(2, F))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hab (QuotientGroup.mk' _ x),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [Group.isPerfect_def.mp hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne (SL(2, F) ⧸ Subgroup.center SL(2, F))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

end SL2


section Block

@[expose] def dNeg : SL(3, F) := ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_dNeg :
    ((dNeg : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := rfl

theorem dNeg_mul_self : (dNeg : SL(3, F)) * dNeg = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_dNeg, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def bM (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem bM_mul (A B : Matrix (Fin 2) (Fin 2) F) : bM (A * B) = bM A * bM B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bM, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem bM_one : bM (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bM]

theorem det_bM (A : Matrix (Fin 2) (Fin 2) F) : (bM A).det = A.det := by
  simp [bM, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] def bSL : SL(2, F) →* SL(3, F) where
  toFun A := ⟨bM (A : Matrix (Fin 2) (Fin 2) F), by rw [det_bM]; exact A.2⟩
  map_one' := Subtype.ext (by simp [bM_one])
  map_mul' A B := Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact bM_mul _ _)

theorem coe_bSL (A : SL(2, F)) : ((bSL A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
    !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
      (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1, 0; 0, 0, 1] := rfl

theorem bSL_neg_one : bSL (-1 : SL(2, F)) = dNeg := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_bSL, coe_dNeg]

theorem bSL_mul_dNeg (A : SL(2, F)) : bSL A * dNeg = dNeg * bSL A := by
  rw [← bSL_neg_one, ← map_mul, ← map_mul]
  congr 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp

end Block

section Cen

variable (F) in
abbrev CenD : Subgroup SL(3, F) := Subgroup.centralizer {dNeg}

theorem mem_CenD {g : SL(3, F)} : g ∈ CenD F ↔ g * dNeg = dNeg * g := by
  rw [Subgroup.mem_centralizer_singleton_iff]

theorem entries_of_commute_dNeg (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 3) (Fin 3) F}
    (h : M * (dNeg : SL(3, F)).1 = (dNeg : SL(3, F)).1 * M) :
    M 0 2 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 := by
  have h02 := congrFun (congrFun h 0) 2
  have h12 := congrFun (congrFun h 1) 2
  have h20 := congrFun (congrFun h 2) 0
  have h21 := congrFun (congrFun h 2) 1
  simp [coe_dNeg, Matrix.mul_apply, Fin.sum_univ_three] at h02 h12 h20 h21
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (2 : F) * M 0 2 = 0 := by linear_combination h02
    exact (mul_eq_zero.1 this).resolve_left h2
  · have : (2 : F) * M 1 2 = 0 := by linear_combination h12
    exact (mul_eq_zero.1 this).resolve_left h2
  · have : (2 : F) * M 2 0 = 0 := by linear_combination -h20
    exact (mul_eq_zero.1 this).resolve_left h2
  · have : (2 : F) * M 2 1 = 0 := by linear_combination -h21
    exact (mul_eq_zero.1 this).resolve_left h2

theorem entries_of_mem_CenD (h2 : (2 : F) ≠ 0) {g : SL(3, F)} (hg : g ∈ CenD F) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have h := congrArg (fun B : SL(3, F) => (B : Matrix (Fin 3) (Fin 3) F)) (mem_CenD.1 hg)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h
  exact entries_of_commute_dNeg h2 h

theorem det_of_entries (g : SL(3, F)) (h02 : (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    (h12 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    ((g : Matrix (Fin 3) (Fin 3) F) 0 0 * (g : Matrix (Fin 3) (Fin 3) F) 1 1 -
      (g : Matrix (Fin 3) (Fin 3) F) 0 1 * (g : Matrix (Fin 3) (Fin 3) F) 1 0) *
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_three, h02, h12, h20, h21] at h
  linear_combination h

theorem g22_ne_zero (h2 : (2 : F) ≠ 0) {g : SL(3, F)} (hg : g ∈ CenD F) :
    (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
  obtain ⟨h02, h12, h20, h21⟩ := entries_of_mem_CenD h2 hg
  have := det_of_entries g h02 h12 h20 h21
  intro h
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem g22_mul (h2 : (2 : F) ≠ 0) {g h : SL(3, F)} (hg : g ∈ CenD F) :
    ((g * h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2 =
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 * (h : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  obtain ⟨-, -, h20, h21⟩ := entries_of_mem_CenD h2 hg
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, h20, h21]

@[expose] def cenHom (h2 : (2 : F) ≠ 0) : ↥(CenD F) →* Fˣ where
  toFun g := Units.mk0 (((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2) (g22_ne_zero h2 g.2)
  map_one' := by ext; simp
  map_mul' g h := by
    ext
    simp [g22_mul h2 g.2]

theorem cenHom_apply (h2 : (2 : F) ≠ 0) (g : ↥(CenD F)) :
    ((cenHom h2 g : Fˣ) : F) = ((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2 := rfl

theorem bSL_mem_CenD (A : SL(2, F)) : bSL A ∈ CenD F := mem_CenD.2 (bSL_mul_dNeg A)

theorem coe_bSL_22 (A : SL(2, F)) : ((bSL A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := rfl

theorem exists_bSL_of_g22 (h2 : (2 : F) ≠ 0) {g : SL(3, F)} (hg : g ∈ CenD F)
    (h22 : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1) : ∃ A : SL(2, F), bSL A = g := by
  obtain ⟨h02, h12, h20, h21⟩ := entries_of_mem_CenD h2 hg
  have hd := det_of_entries g h02 h12 h20 h21
  rw [h22, mul_one] at hd
  obtain ⟨A, hA⟩ : ∃ A : SL(2, F), (A : Matrix (Fin 2) (Fin 2) F) =
      !![(g : Matrix (Fin 3) (Fin 3) F) 0 0, (g : Matrix (Fin 3) (Fin 3) F) 0 1;
        (g : Matrix (Fin 3) (Fin 3) F) 1 0, (g : Matrix (Fin 3) (Fin 3) F) 1 1] :=
    ⟨⟨!![(g : Matrix (Fin 3) (Fin 3) F) 0 0, (g : Matrix (Fin 3) (Fin 3) F) 0 1;
      (g : Matrix (Fin 3) (Fin 3) F) 1 0, (g : Matrix (Fin 3) (Fin 3) F) 1 1], by
      rw [Matrix.det_fin_two]; simpa using hd⟩, rfl⟩
  refine ⟨A, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_bSL, hA]
  fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21, h22]

theorem bSL_injective : Function.Injective (bSL : SL(2, F) →* SL(3, F)) := by
  intro A B h
  have h' := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have := congrFun (congrFun h' (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [coe_bSL] using this


theorem ker_cenHom (h2 : (2 : F) ≠ 0) (x : ↥(CenD F)) :
    x ∈ (cenHom h2).ker ↔ (x : SL(3, F)) ∈ (bSL : SL(2, F) →* SL(3, F)).range := by
  constructor
  · intro hx
    have : (((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2) = 1 := by
      have := congrArg (fun u : Fˣ => (u : F)) (MonoidHom.mem_ker.1 hx)
      simpa [cenHom_apply] using this
    exact exists_bSL_of_g22 h2 x.2 this
  · rintro ⟨A, hA⟩
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [cenHom_apply, ← hA]
    simp [coe_bSL_22]

theorem bSL_range_le_CenD : (bSL : SL(2, F) →* SL(3, F)).range ≤ CenD F := by
  rintro _ ⟨A, rfl⟩
  exact bSL_mem_CenD A

theorem conj_mem_range (h2 : (2 : F) ≠ 0) {g : SL(3, F)} (hg : g ∈ CenD F) {b : SL(3, F)}
    (hb : b ∈ (bSL : SL(2, F) →* SL(3, F)).range) :
    g * b * g⁻¹ ∈ (bSL : SL(2, F) →* SL(3, F)).range := by
  have hbC : b ∈ CenD F := bSL_range_le_CenD hb
  have hker := ((cenHom h2).normal_ker).conj_mem ⟨b, hbC⟩ ((ker_cenHom h2 ⟨b, hbC⟩).2 hb) ⟨g, hg⟩
  exact (ker_cenHom h2 _).1 hker

theorem commutator_mem_range (h2 : (2 : F) ≠ 0) {g h : SL(3, F)} (hg : g ∈ CenD F) (hh : h ∈ CenD F) :
    ⁅g, h⁆ ∈ (bSL : SL(2, F) →* SL(3, F)).range := by
  have hc : ⁅g, h⁆ ∈ CenD F := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have : (⟨⁅g, h⁆, hc⟩ : ↥(CenD F)) ∈ (cenHom h2).ker := by
    rw [MonoidHom.mem_ker]
    have : (⟨⁅g, h⁆, hc⟩ : ↥(CenD F)) = ⁅(⟨g, hg⟩ : ↥(CenD F)), ⟨h, hh⟩⁆ := rfl
    rw [this, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)
  exact (ker_cenHom h2 _).1 this

end Cen

section Proj

@[expose] def tInv : projectiveSL 3 F := proj 3 F dNeg

@[expose] def blockEmb : SL(2, F) →* projectiveSL 3 F := (proj 3 F).comp bSL

theorem blockEmb_apply (A : SL(2, F)) : blockEmb A = proj 3 F (bSL A) := rfl

theorem blockEmb_neg_one : blockEmb (-1 : SL(2, F)) = tInv := by
  rw [blockEmb_apply, bSL_neg_one]
  rfl

theorem tInv_mul_self : (tInv : projectiveSL 3 F) * tInv = 1 := by
  rw [tInv, ← map_mul, dNeg_mul_self, map_one]

theorem blockEmb_injective : Function.Injective (blockEmb : SL(2, F) →* projectiveSL 3 F) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [blockEmb_apply, proj_eq_one_iff] at hA
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hA
  have h22 := congrFun (congrFun hc 2) 2
  rw [coe_bSL_22] at h22
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h22
  have hc1 : (c : F) = 1 := h22.symm
  have : bSL A = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hc, hc1]
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  exact bSL_injective (this.trans (map_one bSL).symm)

theorem neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have h' := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at h'
  simp at h'
  apply h2
  linear_combination -h'

theorem tInv_ne_one (h2 : (2 : F) ≠ 0) : (tInv : projectiveSL 3 F) ≠ 1 := by
  intro h
  rw [← blockEmb_neg_one, ← map_one (blockEmb : SL(2, F) →* projectiveSL 3 F)] at h
  exact neg_one_ne_one h2 (blockEmb_injective h)


theorem dNeg_entries {M : Matrix (Fin 3) (Fin 3) F} {c : F}
    (hM : (dNeg : SL(3, F)).1 * M = (M * (dNeg : SL(3, F)).1) * Matrix.scalar (Fin 3) c) (i j : Fin 3) :
    (dNeg : SL(3, F)).1 i i * M i j = M i j * (dNeg : SL(3, F)).1 j j * c := by
  have := congrFun (congrFun hM i) j
  simp only [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, coe_dNeg,
    Fin.sum_univ_three] at this
  fin_cases i <;> fin_cases j <;> simp [coe_dNeg] at this ⊢ <;> linear_combination this

theorem eq_one_of_dNeg_scalar (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 3) (Fin 3) F} (hM0 : M ≠ 0)
    {c : F} (hc3 : c ^ 3 = 1)
    (hM : (dNeg : SL(3, F)).1 * M = (M * (dNeg : SL(3, F)).1) * Matrix.scalar (Fin 3) c) : c = 1 := by
  by_contra hne
  have hne' : c ≠ -1 := by
    intro h
    rw [h] at hc3
    apply h2
    linear_combination -hc3
  have h1c : (1 : F) - c ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have h1c' : (1 : F) + c ≠ 0 := fun h => hne' (by linear_combination h)
  apply hM0
  ext i j
  have e := dNeg_entries hM i j
  have hdiag : ∀ k : Fin 3, (dNeg : SL(3, F)).1 k k = 1 ∨ (dNeg : SL(3, F)).1 k k = -1 := by
    intro k
    fin_cases k <;> simp [coe_dNeg]
  rcases hdiag i with hi | hi <;> rcases hdiag j with hj | hj <;> rw [hi, hj] at e
  · exact (mul_eq_zero.1 (show (1 - c) * M i j = 0 by linear_combination e)).resolve_left h1c
  · exact (mul_eq_zero.1 (show (1 + c) * M i j = 0 by linear_combination e)).resolve_left h1c'
  · exact (mul_eq_zero.1 (show (1 + c) * M i j = 0 by linear_combination -e)).resolve_left h1c'
  · exact (mul_eq_zero.1 (show (1 - c) * M i j = 0 by linear_combination -e)).resolve_left h1c

theorem mem_CenD_of_commute (h2 : (2 : F) ≠ 0) {g : SL(3, F)}
    (h : proj 3 F g * tInv = tInv * proj 3 F g) : g ∈ CenD F := by
  have h' : proj 3 F (g * dNeg) = proj 3 F (dNeg * g) := by
    rw [map_mul, map_mul]
    exact h
  rw [proj_eq_proj_iff] at h'
  obtain ⟨c, hc3, hc⟩ := mem_scalars.1 h'
  set z : SL(3, F) := (g * dNeg)⁻¹ * (dNeg * g) with hz
  have key : (dNeg * g : SL(3, F)) = (g * dNeg) * z := by rw [hz]; group
  have hM : (dNeg : SL(3, F)).1 * (g : Matrix (Fin 3) (Fin 3) F) =
      ((g : Matrix (Fin 3) (Fin 3) F) * (dNeg : SL(3, F)).1) * Matrix.scalar (Fin 3) (c : F) := by
    have := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) key
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    rw [hc] at this
    exact this
  have hc3' : (c : F) ^ 3 = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hc3
    simpa using this
  have hg0 : (g : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
    intro h0
    have hdet := g.2
    rw [h0] at hdet
    simp at hdet
  have hc1 := eq_one_of_dNeg_scalar h2 hg0 hc3' hM
  rw [hc1] at hM
  apply mem_CenD.2
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have := congrFun (congrFun hM i) j
  simp only [map_one, Matrix.mul_one] at this
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact this.symm

@[expose] def blockSub : Subgroup (projectiveSL 3 F) := (blockEmb : SL(2, F) →* projectiveSL 3 F).range

theorem mem_blockSub {x : projectiveSL 3 F} : x ∈ blockSub ↔ ∃ A : SL(2, F), blockEmb A = x := Iff.rfl

theorem blockEmb_mem (A : SL(2, F)) : blockEmb A ∈ blockSub := ⟨A, rfl⟩

theorem tInv_mem_blockSub : (tInv : projectiveSL 3 F) ∈ blockSub := ⟨-1, blockEmb_neg_one⟩

theorem blockSub_le_centralizer : blockSub ≤ Subgroup.centralizer ({tInv} : Set (projectiveSL 3 F)) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [blockEmb_apply, tInv, ← map_mul, ← map_mul, bSL_mul_dNeg]

theorem exists_CenD_of_mem_centralizer (h2 : (2 : F) ≠ 0) {x : projectiveSL 3 F}
    (hx : x ∈ Subgroup.centralizer ({tInv} : Set (projectiveSL 3 F))) :
    ∃ g ∈ CenD F, proj 3 F g = x := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  exact ⟨g, mem_CenD_of_commute h2 (Subgroup.mem_centralizer_singleton_iff.1 hx), rfl⟩

theorem conj_mem_blockSub (h2 : (2 : F) ≠ 0) {x : projectiveSL 3 F}
    (hx : x ∈ Subgroup.centralizer ({tInv} : Set (projectiveSL 3 F))) {s : projectiveSL 3 F}
    (hs : s ∈ blockSub) : x * s * x⁻¹ ∈ blockSub := by
  obtain ⟨g, hg, rfl⟩ := exists_CenD_of_mem_centralizer h2 hx
  obtain ⟨A, rfl⟩ := hs
  obtain ⟨B, hB⟩ := conj_mem_range h2 hg (b := bSL A) ⟨A, rfl⟩
  refine ⟨B, ?_⟩
  rw [blockEmb_apply, hB, map_mul, map_mul, map_inv]
  rfl

theorem commutator_mem_blockSub (h2 : (2 : F) ≠ 0) {x y : projectiveSL 3 F}
    (hx : x ∈ Subgroup.centralizer ({tInv} : Set (projectiveSL 3 F)))
    (hy : y ∈ Subgroup.centralizer ({tInv} : Set (projectiveSL 3 F))) : ⁅x, y⁆ ∈ blockSub := by
  obtain ⟨g, hg, rfl⟩ := exists_CenD_of_mem_centralizer h2 hx
  obtain ⟨h, hh, rfl⟩ := exists_CenD_of_mem_centralizer h2 hy
  obtain ⟨B, hB⟩ := commutator_mem_range h2 hg hh
  refine ⟨B, ?_⟩
  rw [blockEmb_apply, hB, map_commutatorElement]

theorem isQuasisimple_blockSub [Finite F] (h4 : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple ↥(blockSub : Subgroup (projectiveSL 3 F)) := by
  have e : SL(2, F) ≃* ↥(blockSub : Subgroup (projectiveSL 3 F)) :=
    MonoidHom.ofInjective (blockEmb_injective (F := F))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_sl2c h4)

theorem blockSub_involution (hF : ringChar F ≠ 2) {s : projectiveSL 3 F} (hs : s ∈ blockSub)
    (hs2 : s * s = 1) : s = 1 ∨ s = tInv := by
  obtain ⟨A, rfl⟩ := hs
  have h1 : blockEmb (A * A) = 1 := by rw [map_mul]; exact hs2
  have h2 : A * A = 1 := blockEmb_injective (h1.trans (map_one _).symm)
  rcases sl2c_sq_eq_one hF h2 with rfl | rfl
  · left
    exact map_one _
  · right
    exact blockEmb_neg_one

theorem blockSub_center {s : ↥(blockSub : Subgroup (projectiveSL 3 F))}
    (hs : s ∈ Subgroup.center ↥(blockSub : Subgroup (projectiveSL 3 F))) :
    (s : projectiveSL 3 F) = 1 ∨ (s : projectiveSL 3 F) = tInv := by
  obtain ⟨x, hx⟩ := s.2
  have hA : x ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    have h := Subgroup.mem_center_iff.1 hs ⟨blockEmb B, blockEmb_mem B⟩
    have h' : blockEmb B * blockEmb x = blockEmb x * blockEmb B := by
      have := congrArg Subtype.val h
      simp only [Subgroup.coe_mul] at this
      rw [hx]
      exact this
    exact blockEmb_injective (by rw [map_mul, map_mul]; exact h')
  rcases sl2c_center_eq hA with rfl | rfl
  · left
    rw [← hx]
    exact map_one _
  · right
    rw [← hx]
    exact blockEmb_neg_one

end Proj

end CFSG.GH74.KGroups.L3Eps
