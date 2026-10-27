module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParH1Check

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix

@[expose] def genMat (s : Fin 3) : Matrix (Fin 8) (Fin 8) (ZMod 2) := toMat 8 8 (genBits s)

@[expose] def urMat (C : Fin 3 → Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    List (Fin 3) → Matrix (Fin 8) (Fin 8) (ZMod 2) × Matrix (Fin 8) (Fin 8) (ZMod 2)
  | [] => (1, 0)
  | s :: w => (genMat s * (urMat C w).1, genMat s * (urMat C w).2 + C s * (urMat C w).1)

theorem toMat_id8 : toMat 8 8 id8 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMat_zero8 : toMat 8 8 zero8 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMat_urPair (C : Fin 3 → Array ℕ) (w : List (Fin 3)) :
    toMat 8 8 (urPair C w).1 = (urMat (fun s => toMat 8 8 (C s)) w).1 ∧
      toMat 8 8 (urPair C w).2 = (urMat (fun s => toMat 8 8 (C s)) w).2 := by
  induction w with
  | nil => exact ⟨toMat_id8, toMat_zero8⟩
  | cons s w ih =>
    simp only [urPair, urMat, toMat_bmul, toMat_bxor, ih.1, ih.2, genMat, and_self]

theorem urMat_fst (C C' : Fin 3 → Matrix (Fin 8) (Fin 8) (ZMod 2)) (w : List (Fin 3)) :
    (urMat C w).1 = (urMat C' w).1 := by
  induction w with
  | nil => rfl
  | cons s w ih => simp only [urMat, ih]

theorem urMat_add (C C' : Fin 3 → Matrix (Fin 8) (Fin 8) (ZMod 2)) (w : List (Fin 3)) :
    (urMat (C + C') w).2 = (urMat C w).2 + (urMat C' w).2 := by
  induction w with
  | nil => simp [urMat]
  | cons s w ih =>
    simp only [urMat, ih, Pi.add_apply, urMat_fst (C + C') C w, urMat_fst C' C w]
    noncomm_ring

theorem urMat_smul (c : ZMod 2) (C : Fin 3 → Matrix (Fin 8) (Fin 8) (ZMod 2))
    (w : List (Fin 3)) : (urMat (c • C) w).2 = c • (urMat C w).2 := by
  induction w with
  | nil => simp [urMat]
  | cons s w ih =>
    simp only [urMat, ih, Pi.smul_apply, urMat_fst (c • C) C w, smul_add, mul_smul_comm,
      smul_mul_assoc]

@[expose] def urLin : (Fin 3 → Matrix (Fin 8) (Fin 8) (ZMod 2)) →ₗ[ZMod 2]
    (Fin 7 → Matrix (Fin 8) (Fin 8) (ZMod 2)) where
  toFun C k := (urMat C (h1Rels.getD k [])).2
  map_add' C C' := by ext k : 1; exact urMat_add C C' _
  map_smul' c C := by ext k : 1; exact urMat_smul c C _

@[expose] def h1F : (Fin (3 * 64) → ZMod 2) →ₗ[ZMod 2] (Fin (7 * 64) → ZMod 2) :=
  (blocksEquiv 7).symm.toLinearMap ∘ₗ urLin ∘ₗ (blocksEquiv 3).toLinearMap

@[expose] def cobLin : Matrix (Fin 8) (Fin 8) (ZMod 2) →ₗ[ZMod 2]
    (Fin 3 → Matrix (Fin 8) (Fin 8) (ZMod 2)) where
  toFun X s := genMat s * X + X * genMat s
  map_add' X X' := by ext s : 1; simp only [Pi.add_apply]; noncomm_ring
  map_smul' c X := by ext s : 1; simp [smul_add]

@[expose] def cobF : (Fin (1 * 64) → ZMod 2) →ₗ[ZMod 2] (Fin (3 * 64) → ZMod 2) :=
  (blocksEquiv 3).symm.toLinearMap ∘ₗ cobLin ∘ₗ
    (LinearMap.proj 0 ∘ₗ (blocksEquiv 1).toLinearMap)

theorem toVec_h1Fb (v : ℕ) : toVec (7 * 64) (h1Fb v) = h1F (toVec (3 * 64) v) := by
  rw [h1Fb, toVec_packBlks]
  simp only [h1F, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquiv_symm_apply,
    blocksEquiv_apply]
  congr 1
  ext k : 1
  rw [(toMat_urPair _ _).2]
  simp only [urLin, LinearMap.coe_mk, AddHom.coe_mk]
  congr 2
  ext s : 1
  exact toMat_unpackBlk 3 v s

theorem toVec_cobFb (v : ℕ) : toVec (3 * 64) (cobFb v) = cobF (toVec (1 * 64) v) := by
  rw [cobFb, toVec_packBlks]
  simp only [cobF, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquiv_symm_apply,
    blocksEquiv_apply, LinearMap.proj_apply]
  congr 1
  ext s : 1
  simp only [toMat_bxor, toMat_bmul, cobLin, LinearMap.coe_mk, AddHom.coe_mk, genMat,
    Fin.ofNat_val_eq_self]
  rw [← toMat_unpackBlk 1 v 0]
  rfl

theorem exists_coboundary (C : Fin 3 → Matrix (Fin 8) (Fin 8) (ZMod 2))
    (hC : ∀ w ∈ h1Rels, (urMat C w).2 = 0) :
    ∃ X : Matrix (Fin 8) (Fin 8) (ZMod 2), ∀ s, C s = genMat s * X + X * genMat s := by
  have hF : h1F (vecOf 3 C) = 0 := by
    simp only [h1F, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquiv_apply,
      blocksOf_vecOf, blocksEquiv_symm_apply]
    have : urLin C = 0 := by
      ext k : 1
      simp only [urLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      by_cases hk : (k : ℕ) < h1Rels.length
      · rw [List.getD_eq_getElem _ _ hk]
        exact hC _ (List.getElem_mem hk)
      · rw [List.getD_eq_default _ _ (not_lt.mp hk)]
        rfl
    rw [this]
    ext i
    simp [vecOf]
  have hR : toMat (7 * 64) (3 * 64) (linBits (3 * 64) (7 * 64) h1Fb) *ᵥ vecOf 3 C = 0 := by
    rw [toMat_linBits_mulVec h1Fb h1F (fun j => by rw [toVec_h1Fb, toVec_two_pow]), hF]
  obtain ⟨e, he⟩ := exists_eq_mulVec_of_certCheckWith h1CheckW_eq_true hR
  have hB : (toMat 64 (3 * 64) (Array.ofFn (n := 64) fun j => cobFb (2 ^ (j : ℕ))))ᵀ *ᵥ e =
      cobF e := by
    rw [← toMat_btr]
    exact toMat_linBits_mulVec cobFb cobF (fun j => by rw [toVec_cobFb, toVec_two_pow]) e
  rw [hB] at he
  refine ⟨blocksOf 1 e 0, fun s => ?_⟩
  have := congrArg (fun y => blocksOf 3 y s) he
  simp only [cobF, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquiv_apply,
    blocksEquiv_symm_apply, LinearMap.proj_apply, blocksOf_vecOf] at this
  exact this

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
