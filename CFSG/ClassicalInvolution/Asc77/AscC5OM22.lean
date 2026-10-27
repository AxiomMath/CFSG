module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM7
public import CFSG.ClassicalInvolution.Asc77.AscC5OM9
public import CFSG.ClassicalInvolution.Asc77.AscC5OM12
public import CFSG.ClassicalInvolution.Generic.Generation.Layer

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (exists_conjAut_fieldAut_sp4)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups

section BD

variable {F : Type} [Field F]

@[expose] def plane : Fin 2 ⊕ Fin 2 → Fin 2 := Sum.elim id id

@[expose] def side : Fin 2 ⊕ Fin 2 → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

@[expose] def bd (h : Fin 2 → Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.of fun a b => if plane a = plane b then h (plane a) (side a) (side b) else 0

@[simp] theorem bd_inl_inl (h : Fin 2 → Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    bd h (Sum.inl i) (Sum.inl j) = if i = j then h i 0 0 else 0 := by
  by_cases hij : i = j <;> simp [bd, plane, side, hij]

@[simp] theorem bd_inl_inr (h : Fin 2 → Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    bd h (Sum.inl i) (Sum.inr j) = if i = j then h i 0 1 else 0 := by
  by_cases hij : i = j <;> simp [bd, plane, side, hij]

@[simp] theorem bd_inr_inl (h : Fin 2 → Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    bd h (Sum.inr i) (Sum.inl j) = if i = j then h i 1 0 else 0 := by
  by_cases hij : i = j <;> simp [bd, plane, side, hij]

@[simp] theorem bd_inr_inr (h : Fin 2 → Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    bd h (Sum.inr i) (Sum.inr j) = if i = j then h i 1 1 else 0 := by
  by_cases hij : i = j <;> simp [bd, plane, side, hij]

theorem bd_mul (h g : Fin 2 → Matrix (Fin 2) (Fin 2) F) :
    bd h * bd g = bd (fun k => h k * g k) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, bd_inl_inl, bd_inl_inr,
      bd_inr_inl, bd_inr_inr] <;>
    fin_cases i <;> fin_cases j <;> simp

theorem bd_one : bd (fun _ => (1 : Matrix (Fin 2) (Fin 2) F)) = 1 := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    fin_cases i <;> fin_cases j <;> simp

theorem bd_map (σ : F ≃+* F) (h : Fin 2 → Matrix (Fin 2) (Fin 2) F) :
    (bd h).map σ = bd (fun k => (h k).map σ) := by
  ext a b
  simp only [Matrix.map_apply, bd, Matrix.of_apply]
  split_ifs <;> simp

@[expose] def IsBD (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) : Prop :=
  ∀ a b, plane a ≠ plane b → X a b = 0

theorem bd_stdBlock {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hX : IsBD X) :
    bd (fun k => stdBlock k X) = X := by
  ext a b
  by_cases hab : plane a = plane b
  · rcases a with i | i <;> rcases b with j | j <;> simp only [plane, Sum.elim_inl,
      Sum.elim_inr, id] at hab <;> subst hab <;> simp [stdBlock]
  · rw [hX a b hab]
    simp [bd, hab]

theorem mat_longBlock_eq_bd (k : Fin 2) (b : SL(2, F)) :
    mat 2 F (longBlock F 2 k b) = bd (fun k' => if k' = k then (b : Matrix (Fin 2) (Fin 2) F)
      else 1) := by
  rw [mat_longBlock]
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [CFSG.LieType.Steinberg.Sp.blockMat, Matrix.one_apply]

theorem mem_coords_zero_iff (c : Fin 2 ⊕ Fin 2) : c ∈ coords (0 : Fin 2) ↔ plane c = 0 := by
  rcases c with i | i <;> simp [coords, plane]

theorem isBD_of_comm_longInv (h2 : (2 : F) ≠ 0) {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hX : X * mat 2 F (longInv F 2 0) = mat 2 F (longInv F 2 0) * X) : IsBD X := by
  intro a b hab
  have e := congrFun (congrFun hX a) b
  rw [mat_longInv, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  simp only [mem_coords_zero_iff] at e
  have h01 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  have key : (2 : F) * X a b = 0 := by
    rcases h01 (plane a) with ha | ha <;> rcases h01 (plane b) with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · simp only [ha, hb] at e
      simp at e
      linear_combination e
    · simp only [ha, hb] at e
      simp at e
      linear_combination -e
    · exact absurd (ha.trans hb.symm) hab
  exact (mul_eq_zero.mp key).resolve_left h2

theorem det_eq_mu_of_gm_eq_bd (M : gsp 2 F) {h : Fin 2 → Matrix (Fin 2) (Fin 2) F}
    (hM : gm M = bd h) (k : Fin 2) : (h k).det = mu M := by
  have e := congrFun (congrFun (gm_transpose_mul M) (Sum.inl k)) (Sum.inr k)
  rw [hM] at e
  rw [Matrix.det_fin_two]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, gram, Matrix.fromBlocks] at e
  linear_combination e

theorem mat_longInv_map (σ : F ≃+* F) (k : Fin 2) :
    (mat 2 F (longInv F 2 k)).map σ = mat 2 F (longInv F 2 k) := by
  rw [mat_longInv, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext a
  split_ifs <;> simp

theorem gm_mul_eq_of_conjSp_eq (M : gsp 2 F) (σ : F ≃+* F) {s : StatedSp 2 F}
    (h : conjSp 2 F M (fieldSp 2 F σ s) = s) :
    gm M * (mat 2 F s).map σ = mat 2 F s * gm M := by
  have h1 := congrArg (fun y : StatedSp 2 F => ((y : GL (Fin 2 ⊕ Fin 2) F))) h
  simp only [coe_conjSp] at h1
  rw [mul_inv_eq_iff_eq_mul] at h1
  have h2 := congrArg Units.val h1
  rw [Units.val_mul, Units.val_mul, coe_fieldSp] at h2
  exact h2

theorem isBD_gm_of_conjSp_longInv (h2 : (2 : F) ≠ 0) (M : gsp 2 F) (σ : F ≃+* F)
    (h : conjSp 2 F M (fieldSp 2 F σ (longInv F 2 0)) = longInv F 2 0) : IsBD (gm M) := by
  have e := gm_mul_eq_of_conjSp_eq M σ h
  rw [mat_longInv_map] at e
  exact isBD_of_comm_longInv h2 e

end BD

section Perfect

variable {G : Type*} [Group G]

theorem le_of_perfect_of_le_sup_center {H A Z : Subgroup G} (hH : ⁅H, H⁆ = H)
    (hZ : Z ≤ Subgroup.center G) (hle : H ≤ A ⊔ Z) : H ≤ A := by
  rw [← hH]
  refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
  have hZc : ∀ z ∈ Z, ∀ h ∈ (⊤ : Subgroup G), z * h = h * z := fun z hz h _ =>
    (Subgroup.mem_center_iff.mp (hZ hz) h).symm
  obtain ⟨a, ha, z, hz, rfl⟩ := exists_mul_of_mem_sup_central le_top hZc (hle hg₁)
  obtain ⟨b, hb, w, hw, rfl⟩ := exists_mul_of_mem_sup_central le_top hZc (hle hg₂)
  rw [commutator_mul_of_central (Subgroup.mem_top w) (Subgroup.mem_top a) (Subgroup.mem_top b)
    (hZc z hz) (hZc w hw), commutatorElement_def]
  exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)

end Perfect

theorem spScalars_le_center {F : Type} [Field F] :
    spScalars 2 F ≤ Subgroup.center (StatedSp 2 F) := by
  intro z hz
  rcases mem_spScalars_iff.mp hz with rfl | rfl
  · exact one_mem _
  · exact negOne_mem_center

variable {F : Type} [Field F]
  {Y₁ : Type} [Group Y₁] {Φ₁ : Set (Subgroup Y₁)} {A₁ A₁' : Subgroup Y₁} {z₁ : Y₁}
  {Y₂ : Type} [Group Y₂] {Φ₂ : Set (Subgroup Y₂)} {A₂ A₂' : Subgroup Y₂} {z₂ : Y₂}

namespace Frame

theorem exists_lift_iso [Finite F] (h2 : (2 : F) ≠ 0) (fr₁ : Frame F Y₁ Φ₁ A₁ A₁' z₁)
    (fr₂ : Frame F Y₂ Φ₂ A₂ A₂' z₂) (γ : Y₁ ≃* Y₂) :
    ∃ (M : gsp 2 F) (σ : F ≃+* F),
      ∀ x, γ (fr₁.ψ x) = fr₂.ψ (conjSp 2 F M (fieldSp 2 F σ x)) := by
  let β' : MulAut (StatedProj (StatedSp 2 F)) := fr₁.e.trans (γ.trans fr₂.e.symm)
  obtain ⟨M, σ, hβ'⟩ := exists_conjAut_fieldAut_sp4 h2 β'
  refine ⟨M, σ, fun x => ?_⟩
  have h1 : β' (proj 2 F x) = proj 2 F (conjSp 2 F M (fieldSp 2 F σ x)) := by
    rw [hβ', MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  have h3 := congrArg fr₂.e h1
  have h4 : fr₂.e (β' (proj 2 F x)) = γ (fr₁.e (proj 2 F x)) := by
    simp [β']
  rw [h4, e_proj, e_proj] at h3
  exact h3

theorem lift_longInv [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (fr₁ : Frame F Y₁ Φ₁ A₁ A₁' z₁) (fr₂ : Frame F Y₂ Φ₂ A₂ A₂' z₂) (γ : Y₁ ≃* Y₂)
    (M : gsp 2 F) (σ : F ≃+* F)
    (hγ : ∀ x, γ (fr₁.ψ x) = fr₂.ψ (conjSp 2 F M (fieldSp 2 F σ x)))
    (hA : A₁.map γ.toMonoidHom ≤ A₂) :
    conjSp 2 F M (fieldSp 2 F σ (longInv F 2 0)) = longInv F 2 0 := by
  set α : MulAut (StatedSp 2 F) := conjSp 2 F M * fieldSp 2 F σ with hαdef
  have hα : ∀ x, α x = conjSp 2 F M (fieldSp 2 F σ x) := fun x => rfl
  have : Group.IsPerfect (longRootSp2 F 2 0) := (isClassicalSL2_longRootSp2 h2 0).isPerfect h4
  have : Group.IsPerfect ((longRootSp2 F 2 0).map α.toMonoidHom) :=
    Group.IsPerfect.map α.toMonoidHom
  have hHle : (longRootSp2 F 2 0).map α.toMonoidHom ≤ longRootSp2 F 2 0 ⊔ spScalars 2 F := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 : fr₂.ψ (α r) ∈ A₂ := by
      rw [hα, ← hγ]
      exact hA ⟨fr₁.ψ r, fr₁.mem_A hr, rfl⟩
    have h1' : fr₂.ψ (α r) ∈ (longRootSp2 F 2 0).map fr₂.ψ := fr₂.hA ▸ h1
    obtain ⟨l, hl, hle⟩ := h1'
    rcases fr₂.lift_eq_iff.mp hle.symm with h | h
    · rw [MulEquiv.coe_toMonoidHom, h]
      exact Subgroup.mem_sup_left hl
    · rw [MulEquiv.coe_toMonoidHom, h]
      exact Subgroup.mul_mem_sup hl negOne_mem_spScalars
  have hle := le_of_perfect_of_le_sup_center Subgroup.commutator_eq_self spScalars_le_center hHle
  have hi : α (longInv F 2 0) ∈ longRootSp2 F 2 0 :=
    hle ⟨_, longInv_mem_longRootSp2 0, rfl⟩
  have hsq : α (longInv F 2 0) * α (longInv F 2 0) = 1 := by
    rw [← map_mul, longInv_mul_self, map_one]
  rcases sq_eq_one_of_mem_L h2 0 hi hsq with h | h
  · exfalso
    apply longInv_ne_one h2 0
    exact α.injective (by rw [h, map_one])
  · exact h

end Frame

end CFSG.ClassicalInvolution.Asc77.C5O.M
