module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessDefs
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessB2
public import CFSG.GH74.QTGen4.DSGen4.L34Semidirect

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257.L3
  CFSG.Quasithin.H13.F431.L3.P3

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def wbIota : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(Ln F) where
  toFun A := ⟨wbK A, wbK_mem_Ln A⟩
  map_one' := Subtype.ext wbK_one
  map_mul' A B := Subtype.ext (wbK_mul A B)

theorem wbIota_val (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((wbIota A : ↥(Ln F)) : projectiveSL 3 F) = wbK A :=
  rfl

theorem wbIota_injective : Function.Injective (wbIota (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hK : wbK A = 1 := congrArg Subtype.val hA
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp hK)
  have e22 := congrFun (congrFun hc 2) 2
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp [wbEmb, wbEmbMat, Matrix.scalar_apply] at e22 e00 e01 e10 e11
  have hc1 : (c : F) = 1 := by
    first
    | exact e22.symm
    | exact e22
  rw [hc1] at e00 e11
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

abbrev wbN (F : Type) [Field F] [Finite F] [CharP F 2] : Subgroup ↥(Ln F) :=
  (V2 : Subgroup (projectiveSL 3 F)).subgroupOf (Ln F)

@[expose] def wbNv (v : F × F) : ↥(Ln F) :=
  ⟨wbV v, wbV_mem_Ln v⟩

theorem wbNv_mem (v : F × F) : wbNv v ∈ wbN F := by
  rw [wbN, Subgroup.mem_subgroupOf]
  exact wbV_mem_V2 v

theorem wbNv_mul (v w : F × F) : wbNv v * wbNv w = wbNv (v + w) :=
  Subtype.ext (wbV_add v w).symm

theorem wbN_comm : ∀ a ∈ wbN F, ∀ b ∈ wbN F, a * b = b * a := by
  intro a ha b hb
  rw [wbN, Subgroup.mem_subgroupOf] at ha hb
  obtain ⟨c1, b1, h1⟩ := mem_V2.mp ha
  obtain ⟨c2, b2, h2⟩ := mem_V2.mp hb
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, h1, h2, V2_mul, V2_mul, add_comm b1 b2, add_comm c1 c2]

theorem wbN_inf_range : wbN F ⊓ (wbIota (F := F)).range = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxN, hxK⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hxK
  rw [wbN, Subgroup.mem_subgroupOf] at hxN
  obtain ⟨b, c, hbc⟩ := mem_V2.mp hxN
  have key : wbV (c, b) * wbK (1 : Matrix.SpecialLinearGroup (Fin 2) F) =
      wbV (0 : F × F) * wbK A := by
    rw [wbK_one, mul_one, wbV_zero, one_mul]
    exact hbc.symm
  obtain ⟨-, hA⟩ := wbV_mul_wbK_inj key
  rw [Subgroup.mem_bot, ← hA, map_one]

theorem wbN_sup_range (hq : Nat.card F = 4) : wbN F ⊔ (wbIota (F := F)).range = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨v, A, hg⟩ := ln_normal_form hq g.2
  have hg' : g = wbNv v * wbIota A := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact hg
  rw [hg']
  exact Subgroup.mul_mem_sup (wbNv_mem v) (MonoidHom.mem_range.mpr ⟨A, rfl⟩)

theorem wbIota_symm_val (k : (wbIota (F := F)).range) :
    wbIota ((MonoidHom.ofInjective (wbIota_injective (F := F))).symm k) = (k : ↥(Ln F)) := by
  have h := congrArg Subtype.val
    ((MonoidHom.ofInjective (wbIota_injective (F := F))).apply_symm_apply k)
  exact h

@[expose] noncomputable def wbDelta (κ : F) (k : (wbIota (F := F)).range) : ↥(wbN F) :=
  ⟨wbNv (wbD κ ((MonoidHom.ofInjective (wbIota_injective (F := F))).symm k)), wbNv_mem _⟩

theorem wbDelta_val (κ : F) (k : (wbIota (F := F)).range) :
    ((wbDelta κ k : ↥(wbN F)) : ↥(Ln F)) =
      wbNv (wbD κ ((MonoidHom.ofInjective (wbIota_injective (F := F))).symm k)) := by
  unfold wbDelta
  rfl

theorem wbDelta_cross (hq : Nat.card F = 4) (κ : F) (k k' : (wbIota (F := F)).range) :
    ((wbDelta κ (k * k') : ↥(wbN F)) : ↥(Ln F)) =
      (wbDelta κ k : ↥(Ln F)) * ((k : ↥(Ln F)) * (wbDelta κ k' : ↥(Ln F)) * (k : ↥(Ln F))⁻¹) := by
  apply Subtype.ext
  set e := MonoidHom.ofInjective (wbIota_injective (F := F)) with he
  have hk : ((k : ↥(Ln F)) : projectiveSL 3 F) = wbK (e.symm k) := by
    rw [← wbIota_val, wbIota_symm_val k]
  have hkk : e.symm (k * k') = e.symm k * e.symm k' := map_mul e.symm k k'
  show wbV (wbD κ (e.symm (k * k'))) = wbV (wbD κ (e.symm k)) *
    (((k : ↥(Ln F)) : projectiveSL 3 F) * wbV (wbD κ (e.symm k')) *
      ((k : ↥(Ln F)) : projectiveSL 3 F)⁻¹)
  rw [hk, hkk, wbD_mul hq κ, wbK_conj_wbV, ← wbV_add]

@[expose] def wbX (a : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def wbT (hq : Nat.card F = 4) (t₁ t₂ : Fˣ) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![(t₁ : F) ^ 2 * (t₂ : F), 0; 0, (t₁ : F) * (t₂ : F) ^ 2], by
    rw [Matrix.det_fin_two_of]
    have h := cube_units hq (t₁ * t₂)
    rw [Units.val_mul] at h
    linear_combination h⟩

theorem wbX_00 (a : F) : (wbX a).1 0 0 = 1 := rfl
theorem wbX_01 (a : F) : (wbX a).1 0 1 = a := rfl
theorem wbX_10 (a : F) : (wbX a).1 1 0 = 0 := rfl
theorem wbX_11 (a : F) : (wbX a).1 1 1 = 1 := rfl

theorem wbT_00 (hq : Nat.card F = 4) (t₁ t₂ : Fˣ) :
    (wbT hq t₁ t₂).1 0 0 = (t₁ : F) ^ 2 * (t₂ : F) := rfl
theorem wbT_01 (hq : Nat.card F = 4) (t₁ t₂ : Fˣ) : (wbT hq t₁ t₂).1 0 1 = 0 := rfl
theorem wbT_10 (hq : Nat.card F = 4) (t₁ t₂ : Fˣ) : (wbT hq t₁ t₂).1 1 0 = 0 := rfl
theorem wbT_11 (hq : Nat.card F = 4) (t₁ t₂ : Fˣ) :
    (wbT hq t₁ t₂).1 1 1 = (t₁ : F) * (t₂ : F) ^ 2 := rfl

theorem units_cube (hq : Nat.card F = 4) (t : Fˣ) : t ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact cube_units hq t

theorem wbK_wbX (a : F) : wbK (wbX a) = xP a := by
  unfold wbK xP
  rfl

theorem wbEmb_wbT (hq : Nat.card F = 4) (t₁ t₂ : Fˣ) :
    wbEmb (wbT hq t₁ t₂) =
      scalarElement (t₁ * t₂) (units_cube hq (t₁ * t₂)) * dMat t₁ t₂ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement]
  have h1 : (t₁ : F) ≠ 0 := t₁.ne_zero
  have h2 : (t₂ : F) ≠ 0 := t₂.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wbEmb, wbEmbMat, wbT, coe_dMat, Matrix.scalar_apply, Matrix.diagonal_mul,
      Matrix.diagonal_apply, h1, h2, Units.val_mul]
  all_goals field_simp

theorem wbK_wbT (hq : Nat.card F = 4) (t₁ t₂ : Fˣ) :
    wbK (wbT hq t₁ t₂) = proj 3 F (dMat t₁ t₂) := by
  unfold wbK
  rw [wbEmb_wbT hq t₁ t₂, map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars _ _), one_mul]

theorem uElt_eq_wbV (a β c : F) : uElt a β c = wbV (c, β) * xP a := by
  unfold uElt wbV xP yP wP
  simp only [← map_mul]
  congr 1
  apply Subtype.ext
  change xM a * yM β * wM (c - a * β) = yM β * wM c * xM a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xM, yM, wM, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uElt_mul_dMat (hq : Nat.card F = 4) (a β c : F) (t₁ t₂ : Fˣ) :
    uElt a β c * proj 3 F (dMat t₁ t₂) = wbV (c, β) * wbK (wbX a * wbT hq t₁ t₂) := by
  rw [wbK_mul, wbK_wbX, wbK_wbT, uElt_eq_wbV, mul_assoc]

theorem wbD_wbX_wbT (hq : Nat.card F = 4) (κ a : F) (t₁ t₂ : Fˣ) :
    wbD κ (wbX a * wbT hq t₁ t₂) = (κ * a ^ 2, 0) := by
  have hef : ((t₁ : F) ^ 2 * (t₂ : F)) * ((t₁ : F) * (t₂ : F) ^ 2) = 1 := by
    have h := cube_units hq (t₁ * t₂)
    rw [Units.val_mul] at h
    linear_combination h
  unfold wbD
  simp only [wb_mul_00, wb_mul_01, wb_mul_10, wb_mul_11, wbX_00, wbX_01, wbX_10, wbX_11,
    wbT_00, wbT_01, wbT_10, wbT_11]
  refine Prod.ext ?_ ?_
  · simp only
    linear_combination κ * a ^ 2 * ((t₁ : F) ^ 2 * (t₂ : F) * ((t₁ : F) * (t₂ : F) ^ 2) + 1) * hef
  · simp only
    ring

theorem nuMap_one_val (κ a β c : F) (τ : ↥(torus3 F)) :
    ((nuMap 1 1 κ 0 false (nuNFEquiv F (a, β, c, τ)) : ↥(Ln F ⊓ Pt F)) :
      projectiveSL 3 F) =
      uElt a β (c + κ * a ^ 2) * (τ : projectiveSL 3 F) := by
  rw [nuMap_nuNFEquiv, nuNFEquiv_val]
  simp [nuCoord, nuFrob]

theorem wb_restrict (hq : Nat.card F = 4) (κ : F) (φ : MulAut ↥(Ln F))
    (hφNK : ∀ (v : ↥(wbN F)) (k : ↥(wbIota (F := F)).range),
      φ ((v : ↥(Ln F)) * (k : ↥(Ln F))) =
        ((v : ↥(Ln F)) * (wbDelta κ k : ↥(Ln F))) * (k : ↥(Ln F))) :
    ∀ (b : ↥(Ln F ⊓ Pt F)) (m : ↥(Ln F)), (m : projectiveSL 3 F) = (b : projectiveSL 3 F) →
      ((φ m : ↥(Ln F)) : projectiveSL 3 F) =
        ((nuMap 1 1 κ 0 false b : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) := by
  intro b m hmb
  obtain ⟨⟨a, β, c, τ⟩, rfl⟩ := (nuNFEquiv F).surjective b
  obtain ⟨t₁, t₂, hτ⟩ := mem_torus3.mp τ.2
  have hmb' : (m : projectiveSL 3 F) = uElt a β c * (τ : projectiveSL 3 F) := by
    rw [hmb, nuNFEquiv_val]
  have hm : m = wbNv (c, β) * wbIota (wbX a * wbT hq t₁ t₂) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hmb', hτ, uElt_mul_dMat hq]
    rfl
  have hkZ : (wbIota (wbX a * wbT hq t₁ t₂) : ↥(Ln F)) ∈ (wbIota (F := F)).range :=
    MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hZk : (MonoidHom.ofInjective (wbIota_injective (F := F))).symm
      ⟨wbIota (wbX a * wbT hq t₁ t₂), hkZ⟩ = wbX a * wbT hq t₁ t₂ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h1 := hφNK ⟨wbNv (c, β), wbNv_mem _⟩ ⟨wbIota (wbX a * wbT hq t₁ t₂), hkZ⟩
  rw [wbDelta_val, hZk, wbD_wbX_wbT hq κ a t₁ t₂] at h1
  have hφm : φ m = wbNv (c + κ * a ^ 2, β) * wbIota (wbX a * wbT hq t₁ t₂) := by
    rw [hm]
    have h2 : (φ (wbNv (c, β) * wbIota (wbX a * wbT hq t₁ t₂))) =
        (wbNv (c, β) * wbNv (κ * a ^ 2, 0)) * wbIota (wbX a * wbT hq t₁ t₂) := h1
    rw [h2, wbNv_mul]
    congr 2
    ext <;> simp
  rw [hφm, nuMap_one_val]
  show wbV (c + κ * a ^ 2, β) * wbK (wbX a * wbT hq t₁ t₂) = _
  rw [← uElt_mul_dMat hq, hτ]

theorem nuMap_surjective_one (κ : F) (y : ↥(Ln F ⊓ Pt F)) :
    ∃ x : ↥(Ln F ⊓ Pt F), nuMap 1 1 κ 0 false x = y := by
  obtain ⟨⟨a, β, c, τ⟩, rfl⟩ := (nuNFEquiv F).surjective y
  refine ⟨nuNFEquiv F (a, β, c - κ * a ^ 2, τ), ?_⟩
  rw [nuMap_nuNFEquiv]
  congr 1
  simp [nuCoord, nuFrob]

theorem wb_pt_iff (κ : F) (φ : MulAut ↥(Ln F))
    (hW : ∀ (b : ↥(Ln F ⊓ Pt F)) (m : ↥(Ln F)), (m : projectiveSL 3 F) = (b : projectiveSL 3 F) →
      ((φ m : ↥(Ln F)) : projectiveSL 3 F) =
        ((nuMap 1 1 κ 0 false b : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F)) :
    ∀ m : ↥(Ln F), (m : projectiveSL 3 F) ∈ Pt F ↔
      ((φ m : ↥(Ln F)) : projectiveSL 3 F) ∈ Pt F := by
  intro m
  constructor
  · intro hm
    have hmB : (m : projectiveSL 3 F) ∈ Ln F ⊓ Pt F := Subgroup.mem_inf.mpr ⟨m.2, hm⟩
    rw [hW ⟨m, hmB⟩ m rfl]
    exact (Subgroup.mem_inf.mp (nuMap 1 1 κ 0 false ⟨m, hmB⟩).2).2
  · intro hφ
    have hyB : ((φ m : ↥(Ln F)) : projectiveSL 3 F) ∈ Ln F ⊓ Pt F :=
      Subgroup.mem_inf.mpr ⟨(φ m).2, hφ⟩
    obtain ⟨x, hx⟩ := nuMap_surjective_one κ ⟨_, hyB⟩
    have hxm := hW x ⟨(x : projectiveSL 3 F), (Subgroup.mem_inf.mp x.2).1⟩ rfl
    rw [hx] at hxm
    have hmm : φ ⟨(x : projectiveSL 3 F), (Subgroup.mem_inf.mp x.2).1⟩ = φ m :=
      Subtype.ext hxm
    have hmeq := φ.injective hmm
    rw [← hmeq]
    exact (Subgroup.mem_inf.mp x.2).2

end Main

theorem witnessLn {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F = 4) (κ : F) :
    WitnessLn F κ := by
  obtain ⟨φ, -, hφNK, -⟩ := semidirect_aut (wbN F) (wbIota (F := F)).range wbN_comm
    wbN_inf_range (wbN_sup_range hq) (wbDelta κ) (wbDelta_cross hq κ)
  have hW := wb_restrict hq κ φ hφNK
  exact ⟨φ, wb_pt_iff κ φ hW, hW⟩

end CFSG.GH74.QTGen4.DSGen4.L34

end
