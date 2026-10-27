module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeBridgeInputs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModels
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open Matrix Subgroup CFSG.LargeExtraspecial CFSG.ComponentClassification.AS81.HeSylow
open CFSG.Monster.B.Co2 CFSG.RankThree.Native
open scoped MatrixGroups

local notation:1024 "↑ₘ" A:1024 => ((A : SL(5, ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))

theorem coe_heT0 :
    ((DW.cornerTransvection (N := 5) (by norm_num) : SL(5, ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 + single 0 4 1 :=
  rfl

theorem entries_of_commute_heT0 {M : Matrix (Fin 5) (Fin 5) (ZMod 2)}
    (h : M * (1 + single 0 4 1) = (1 + single 0 4 1) * M) :
    (M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 3 0 = 0 ∧ M 4 0 = 0) ∧ (M 4 1 = 0 ∧ M 4 2 = 0 ∧ M 4 3 = 0) ∧
      M 0 0 = M 4 4 := by
  have e : ∀ i j, (M * (1 + single 0 4 1) : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j =
      ((1 + single 0 4 1) * M : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j := fun i j => by rw [h]
  have e14 := e 1 4
  have e24 := e 2 4
  have e34 := e 3 4
  have e44 := e 4 4
  have e01 := e 0 1
  have e02 := e 0 2
  have e03 := e 0 3
  have e04 := e 0 4
  simp [Matrix.mul_add, Matrix.add_mul] at e14 e24 e34 e44 e01 e02 e03 e04
  exact ⟨⟨e14, e24, e34, e44⟩, ⟨e01, e02, e03⟩, e04⟩

theorem submatrix_mid_mul {M N : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hM1 : M 1 0 = 0)
    (hM2 : M 2 0 = 0) (hM3 : M 3 0 = 0) (hN1 : N 4 1 = 0) (hN2 : N 4 2 = 0) (hN3 : N 4 3 = 0) :
    (M * N).submatrix ![1, 2, 3] ![1, 2, 3] =
      M.submatrix ![1, 2, 3] ![1, 2, 3] * N.submatrix ![1, 2, 3] ![1, 2, 3] := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> simp [hM1, hM2, hM3, hN1, hN2, hN3]

theorem mul_apply_zero_zero {M N : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hN1 : N 1 0 = 0)
    (hN2 : N 2 0 = 0) (hN3 : N 3 0 = 0) (hN4 : N 4 0 = 0) : (M * N) 0 0 = M 0 0 * N 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_five, hN1, hN2, hN3, hN4]

variable {g : SL(5, ZMod 2)}

theorem heCent_entries
    (hg : g ∈ centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} :
      Set (SL(5, ZMod 2)))) :
    (↑ₘg 1 0 = 0 ∧ ↑ₘg 2 0 = 0 ∧ ↑ₘg 3 0 = 0 ∧ ↑ₘg 4 0 = 0) ∧
      (↑ₘg 4 1 = 0 ∧ ↑ₘg 4 2 = 0 ∧ ↑ₘg 4 3 = 0) ∧ ↑ₘg 0 0 = 1 ∧ ↑ₘg 4 4 = 1 := by
  have hcomm : ∀ x ∈ centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} :
      Set (SL(5, ZMod 2))), ↑ₘx * (1 + single 0 4 1) = (1 + single 0 4 1) * ↑ₘx := by
    intro x hx
    have h := congrArg (fun y : SL(5, ZMod 2) => (y : Matrix (Fin 5) (Fin 5) (ZMod 2)))
      (mem_centralizer_singleton_iff.mp hx)
    simpa only [Matrix.SpecialLinearGroup.coe_mul, coe_heT0] using h
  obtain ⟨h0, h4, h04⟩ := entries_of_commute_heT0 (hcomm g hg)
  obtain ⟨h0', -, -⟩ := entries_of_commute_heT0 (hcomm g⁻¹ (inv_mem hg))
  have h1 : (↑ₘg * ↑ₘg⁻¹) 0 0 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      one_apply_eq]
  rw [mul_apply_zero_zero h0'.1 h0'.2.1 h0'.2.2.1 h0'.2.2.2] at h1
  have h00 : ↑ₘg 0 0 = 1 := by
    generalize ↑ₘg 0 0 = a at h1
    generalize ↑ₘg⁻¹ 0 0 = b at h1
    revert a b
    decide
  exact ⟨h0, h4, h00, h04 ▸ h00⟩

@[expose] noncomputable def heMidHom :
    ↥(centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} : Set (SL(5, ZMod 2)))) →*
      Matrix (Fin 3) (Fin 3) (ZMod 2) where
  toFun g := (↑ₘ(g : SL(5, ZMod 2))).submatrix ![1, 2, 3] ![1, 2, 3]
  map_one' := submatrix_one _ (by decide)
  map_mul' g h := by
    obtain ⟨⟨hg1, hg2, hg3, -⟩, -, -, -⟩ := heCent_entries g.2
    obtain ⟨-, ⟨hh1, hh2, hh3⟩, -, -⟩ := heCent_entries h.2
    change (↑ₘ((g : SL(5, ZMod 2)) * (h : SL(5, ZMod 2)))).submatrix _ _ = _
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact submatrix_mid_mul hg1 hg2 hg3 hh1 hh2 hh3

@[expose] def heEdgeData (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    (Fin 3 → ZMod 2) × ZMod 2 × (Fin 3 → ZMod 2) :=
  (fun a => M 0 (![1, 2, 3] a), M 0 4, fun a => M (![1, 2, 3] a) 4)

theorem heMid_edge_injective :
    Function.Injective fun g : ↥(centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} :
        Set (SL(5, ZMod 2)))) => (heMidHom.toHomUnits g, heEdgeData ↑ₘ(g : SL(5, ZMod 2))) := by
  intro g h hgh
  simp only [Prod.mk.injEq] at hgh
  obtain ⟨hmid, hedge⟩ := hgh
  have hm : ∀ a b, (heMidHom g) a b = (heMidHom h) a b := fun a b => by
    rw [← MonoidHom.coe_toHomUnits heMidHom g, hmid, MonoidHom.coe_toHomUnits]
  simp only [heEdgeData, Prod.mk.injEq] at hedge
  obtain ⟨hr, hc, hl⟩ := hedge
  have hr' := congrFun hr
  have hl' := congrFun hl
  obtain ⟨⟨g10, g20, g30, g40⟩, ⟨g41, g42, g43⟩, g00, g44⟩ := heCent_entries g.2
  obtain ⟨⟨h10, h20, h30, h40⟩, ⟨h41, h42, h43⟩, h00, h44⟩ := heCent_entries h.2
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact g00.trans h00.symm | exact g44.trans h44.symm | exact hc
    | exact hr' 0 | exact hr' 1 | exact hr' 2 | exact hl' 0 | exact hl' 1 | exact hl' 2
    | exact g10.trans h10.symm | exact g20.trans h20.symm | exact g30.trans h30.symm
    | exact g40.trans h40.symm | exact g41.trans h41.symm | exact g42.trans h42.symm
    | exact g43.trans h43.symm
    | exact hm 0 0 | exact hm 0 1 | exact hm 0 2 | exact hm 1 0 | exact hm 1 1 | exact hm 1 2
    | exact hm 2 0 | exact hm 2 1 | exact hm 2 2

theorem card_heCent_le :
    Nat.card ↥(centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} :
      Set (SL(5, ZMod 2)))) ≤ 21504 := by
  have hGL : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
    rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_three]
    rfl
  have h := Nat.card_le_card_of_injective _ heMid_edge_injective
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, hGL, Nat.card_fun, Nat.card_zmod,
    Nat.card_fin] at h
  simpa using h

theorem coe_heVecEquiv (u : Fin 5 → ZMod 2) :
    (heVecEquiv u : ℕ) = ∑ i : Fin 5, (u i).val * 2 ^ (i : ℕ) :=
  rfl

theorem val_heVecEquiv_symm (x : Fin 32) (j : Fin 5) :
    (heVecEquiv.symm x j).val = x / 2 ^ (j : ℕ) % 2 :=
  rfl

theorem val_mulVec_heVecEquiv_symm (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) (x : Fin 32)
    (i : Fin 5) : ((g *ᵥ heVecEquiv.symm x) i).val = heImgRow g i x := by
  have h : (g *ᵥ heVecEquiv.symm x) i =
      ((∑ j : Fin 5, (g i j).val * (x / 2 ^ (j : ℕ) % 2) : ℕ) : ZMod 2) := by
    simp only [mulVec, dotProduct, Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val,
      ← val_heVecEquiv_symm]
  rw [h, ZMod.val_natCast, Fin.sum_univ_five, heImgRow]
  norm_num

theorem heImg_eq (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) (x : Fin 32) :
    heImg g x = (heVecEquiv (g *ᵥ heVecEquiv.symm x) : ℕ) := by
  rw [coe_heVecEquiv, Fin.sum_univ_five]
  simp only [val_mulVec_heVecEquiv_symm, heImg]
  norm_num
  ring

theorem coe_heRho_apply (g : SL(5, ZMod 2)) (x : Fin 32) : (heRho g x : ℕ) = heImg ↑ₘg x :=
  (heImg_eq _ x).symm

theorem heRho_injective : Function.Injective heRho := by
  intro g h hgh
  apply Matrix.SpecialLinearGroup.toLin'_injective
  refine LinearEquiv.ext fun v => ?_
  have h := congrArg (fun σ : Equiv.Perm (Fin 32) => σ (heVecEquiv v)) hgh
  simpa [heRho] using h

theorem hePC_le_map :
    hePC ≤ (centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} :
      Set (SL(5, ZMod 2)))).map heRho := by
  obtain ⟨hlen, hk⟩ := heBridgeFacts
  refine grpN_le fun a ha => ?_
  obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem ha
  have hk12 : k < 12 := hlen ▸ hk'
  obtain ⟨himg, hcomm⟩ := hk ⟨k, hk12⟩
  have hrep : Rep 32 (hePCGens[k]'hk') (heRho (heBridgeGen ⟨k, hk12⟩)) := fun x => by
    rw [coe_heRho_apply, ← himg x, getElem!_pos hePCGens k hk']
  rw [permOfArr_eq_of_rep hrep]
  exact mem_map_of_mem heRho (mem_centralizer_singleton_iff.mpr hcomm)

theorem nonempty_centralizer_mulEquiv_hePC (hcard : Nat.card hePC = 21504) :
    Nonempty (↥(centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} :
      Set (SL(5, ZMod 2)))) ≃* ↥hePC) := by
  have heq : hePC = (centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} :
      Set (SL(5, ZMod 2)))).map heRho := by
    refine eq_of_le_of_card_ge hePC_le_map ?_
    rw [card_map_of_injective heRho_injective, hcard]
    exact card_heCent_le
  exact ⟨(equivMapOfInjective _ heRho heRho_injective).trans (MulEquiv.subgroupCongr heq.symm)⟩

end CFSG.ComponentClassification.AS81.HeTri
