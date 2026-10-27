
module

public import CFSG.Certificates.Kernel.ThDemp.ChainExBase
public import CFSG.Certificates.Kernel.ThDemp.OrbUnfoldBase
public import CFSG.Certificates.Kernel.ThDemp.OrbFacts
import Mathlib.Data.Fintype.Prod
public import CFSG.Certificates.Kernel.Th.Spec.FwdRel

public section

namespace CFSG.Certificates.ThDemp.Stab

open MulAction CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp
  CFSG.Certificates.ThDemp.Act CFSG.Certificates.ThDemp.Lanes CFSG.Certificates.ThDemp.Batches
  CFSG.Certificates.ThDemp.Key

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

variable {J : Subgroup (GL (Fin 248) (ZMod 2))}

theorem inv_smul_eq (g : J) (W : Pts) : g⁻¹ • W = mapM (𝕄 g) W := by
  rw [Subgroup.smul_def, Subgroup.coe_inv, Act.smul_def, inv_inv]

theorem smul_eq_mapM (g : J) (W : Pts) : g • W = mapM (𝕄 g⁻¹) W := by
  conv_lhs => rw [← inv_inv g]
  exact inv_smul_eq g⁻¹ W

theorem mat_mul' (g h : J) : 𝕄 (g * h) = 𝕄 g * 𝕄 h := by
  rw [Subgroup.coe_mul, Units.val_mul]

theorem mat_mul_inv (g : J) : 𝕄 g * 𝕄 g⁻¹ = 1 := by
  rw [← mat_mul', mul_inv_cancel, Subgroup.coe_one, Units.val_one]

theorem mat_inv_mul (g : J) : 𝕄 g⁻¹ * 𝕄 g = 1 := by
  rw [← mat_mul', inv_mul_cancel, Subgroup.coe_one, Units.val_one]

structure Ctx (D : DempData) (O : OrbData) (J : Subgroup (GL (Fin 248) (ZMod 2))) where
  d₀ : J
  d₁ : J
  t : ℕ → ℕ → J
  mem : ∀ l < 6, ∀ i < D.oszL l, t l i ∈ Subgroup.closure ({d₀, d₁} : Set J)
  mat : ∀ l < 6, ∀ i < D.oszL l, 𝕄 (t l i) = pkMat (D.T l i)
  uniq : ∀ x ∈ Subgroup.closure ({d₀, d₁} : Set J), ∃! y : Coords, chainProd t y = x
  inv : ∀ l < 3, ∀ i < D.oszL l, pkMat (O.TI l i) = 𝕄 (t l i)⁻¹
  osz : D.oszL 0 = 31 ∧ D.oszL 1 = 30 ∧ D.oszL 2 = 28 ∧ D.oszL 3 = 24 ∧ D.oszL 4 = 16 ∧
    D.oszL 5 = 32
  md₀ : 𝕄 d₀ = pkMat (gen D 0)
  md₁ : 𝕄 d₁ = pkMat (gen D 1)
  lev5 : ∀ x ∈ Subgroup.closure ({d₀, d₁} : Set J),
    (∀ l < 5, Matrix.vecMul (pkVec (D.bvL l)) (𝕄 x) = pkVec (D.bvL l)) → ∃ z < 32, x = t 5 z

namespace Ctx

variable {D : DempData} {O : OrbData} (C : Ctx D O J)

abbrev Dg : Subgroup J := Subgroup.closure ({C.d₀, C.d₁} : Set J)

theorem exists_gen {g : ℕ} (hg : g < 2) : ∃ d : J, d ∈ C.Dg ∧ 𝕄 d = pkMat (gen D g) := by
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · exact ⟨C.d₀, Subgroup.subset_closure (by simp), C.md₀⟩
  · exact ⟨C.d₁, Subgroup.subset_closure (by simp), C.md₁⟩

@[expose] noncomputable def xP (D : DempData) (P : ℕ) (y : Coords) : ℕ :=
  mulB (rep 1 256 5) (2 ^ 248 - 1) (mulB (rep 1 256 5) (2 ^ 248 - 1)
    (mulB (rep 1 256 5) (2 ^ 248 - 1) P (D.T 5 y.2.2.2.2.2)) (D.T 4 y.2.2.2.2.1)) (D.T 3 y.2.2.2.1)

@[expose] noncomputable def yP (O : OrbData) (P : ℕ) (y : Coords) : ℕ :=
  mulB (rep 1 256 5) (2 ^ 248 - 1) (mulB (rep 1 256 5) (2 ^ 248 - 1)
    (mulB (rep 1 256 5) (2 ^ 248 - 1) P (O.TI 0 y.1)) (O.TI 1 y.2.1)) (O.TI 2 y.2.2.1)

section
include C

theorem y0_lt (y : Coords) : y.1.val < D.oszL 0 := by rw [C.osz.1]; exact y.1.isLt
theorem y1_lt (y : Coords) : y.2.1.val < D.oszL 1 := by rw [C.osz.2.1]; exact y.2.1.isLt
theorem y2_lt (y : Coords) : y.2.2.1.val < D.oszL 2 := by rw [C.osz.2.2.1]; exact y.2.2.1.isLt
theorem y3_lt (y : Coords) : y.2.2.2.1.val < D.oszL 3 := by
  rw [C.osz.2.2.2.1]; exact y.2.2.2.1.isLt
theorem y4_lt (y : Coords) : y.2.2.2.2.1.val < D.oszL 4 := by
  rw [C.osz.2.2.2.2.1]; exact y.2.2.2.2.1.isLt
theorem y5_lt (y : Coords) : y.2.2.2.2.2.val < D.oszL 5 := by
  rw [C.osz.2.2.2.2.2]; exact y.2.2.2.2.2.isLt

end

theorem chainProd_mem (y : Coords) : chainProd C.t y ∈ C.Dg := by
  unfold chainProd
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (C.mem 5 (by omega) _ (C.y5_lt y)) (C.mem 4 (by omega) _ (C.y4_lt y)))
    (C.mem 3 (by omega) _ (C.y3_lt y))) (C.mem 2 (by omega) _ (C.y2_lt y)))
    (C.mem 1 (by omega) _ (C.y1_lt y))) (C.mem 0 (by omega) _ (C.y0_lt y))

theorem chainProd_smul_iff (P : ℕ) (y : Coords) :
    chainProd C.t y • sp P = sp P ↔ sp (xP D P y) = sp (yP O P y) := by
  set A := C.t 5 y.2.2.2.2.2 * C.t 4 y.2.2.2.2.1 * C.t 3 y.2.2.2.1
  set B := C.t 2 y.2.2.1 * C.t 1 y.2.1 * C.t 0 y.1
  have e : chainProd C.t y = A * B := by
    simp only [chainProd, A, B, mul_assoc]
  have hA : A⁻¹ • sp P = sp (xP D P y) := by
    rw [inv_smul_eq, mat_mul', mat_mul', C.mat 5 (by omega) _ (C.y5_lt y),
      C.mat 4 (by omega) _ (C.y4_lt y), C.mat 3 (by omega) _ (C.y3_lt y), mapM_mul, mapM_mul,
      xP, sp_mulB, sp_mulB, sp_mulB]
  have hB : B • sp P = sp (yP O P y) := by
    rw [smul_eq_mapM]
    simp only [B, mul_inv_rev]
    rw [mat_mul', mat_mul', ← C.inv 0 (by omega) _ (C.y0_lt y), ← C.inv 1 (by omega) _ (C.y1_lt y),
      ← C.inv 2 (by omega) _ (C.y2_lt y), mapM_mul, mapM_mul, yP, sp_mulB, sp_mulB, sp_mulB]
  rw [e, mul_smul, smul_eq_iff_eq_inv_smul, hA, hB, eq_comm]

theorem card_stabilizer_eq (P : ℕ) :
    Nat.card (stabilizer C.Dg (sp P)) =
      Nat.card {y : Coords // sp (xP D P y) = sp (yP O P y)} := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun y : {y : Coords // sp (xP D P y) = sp (yP O P y)} =>
      (⟨⟨chainProd C.t y.1, C.chainProd_mem y.1⟩, (C.chainProd_smul_iff P y.1).mpr y.2⟩ :
        stabilizer C.Dg (sp P))) ⟨?_, ?_⟩)).symm
  · rintro ⟨y, hy⟩ ⟨y', hy'⟩ e
    have e' : chainProd C.t y = chainProd C.t y' := congrArg (fun s => s.1.1) e
    obtain ⟨z, -, hz⟩ := C.uniq _ (C.chainProd_mem y)
    have h1 := hz y rfl
    have h2 := hz y' e'.symm
    exact Subtype.ext (h1.trans h2.symm)
  · rintro ⟨⟨x, hx⟩, hs⟩
    obtain ⟨y, hy, -⟩ := C.uniq x hx
    have hs' : chainProd C.t y • sp P = sp P := by
      rw [hy]
      exact hs
    exact ⟨⟨y, (C.chainProd_smul_iff P y).mp hs'⟩, Subtype.ext (Subtype.ext hy)⟩

theorem T_inv {l i : ℕ} (hl : l < 6) (hi : i < D.oszL l) :
    pkMat (D.T l i) * 𝕄 (C.t l i)⁻¹ = 1 := by
  rw [← C.mat l hl i hi]
  exact mat_mul_inv _

theorem TI_inv {l i : ℕ} (hl : l < 3) (hi : i < D.oszL l) :
    pkMat (O.TI l i) * 𝕄 (C.t l i) = 1 := by
  rw [C.inv l hl i hi]
  exact mat_inv_mul _

include C in
theorem lil_xP {P : ℕ} (hP : LIL (rowsOf (2 ^ 248 - 1) P)) (y : Coords) :
    LIL (rowsOf (2 ^ 248 - 1) (xP D P y)) :=
  lil_mulB (C.T_inv (by omega) (C.y3_lt y)) (lil_mulB (C.T_inv (by omega) (C.y4_lt y))
    (lil_mulB (C.T_inv (by omega) (C.y5_lt y)) hP))

include C in
theorem lil_yP {P : ℕ} (hP : LIL (rowsOf (2 ^ 248 - 1) P)) (y : Coords) :
    LIL (rowsOf (2 ^ 248 - 1) (yP O P y)) :=
  lil_mulB (C.TI_inv (by omega) (C.y2_lt y)) (lil_mulB (C.TI_inv (by omega) (C.y1_lt y))
    (lil_mulB (C.TI_inv (by omega) (C.y0_lt y)) hP))

@[expose] def idx (y : Coords) : ℕ × ℕ :=
  (512 * y.2.2.2.1.val + (32 * y.2.2.2.2.1.val + y.2.2.2.2.2.val),
    930 * y.2.2.1.val + (31 * y.2.1.val + y.1.val))

theorem idx_injective : Function.Injective idx := by
  rintro ⟨a0, a1, a2, a3, a4, a5⟩ ⟨b0, b1, b2, b3, b4, b5⟩ e
  simp only [idx, Prod.mk.injEq] at e
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt; have := a4.isLt
  have := a5.isLt; have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  have := b4.isLt; have := b5.isLt
  have h0 : a0 = b0 := Fin.ext (by omega)
  have h1 : a1 = b1 := Fin.ext (by omega)
  have h2 : a2 = b2 := Fin.ext (by omega)
  have h3 : a3 = b3 := Fin.ext (by omega)
  have h4 : a4 = b4 := Fin.ext (by omega)
  have h5 : a5 = b5 := Fin.ext (by omega)
  rw [h0, h1, h2, h3, h4, h5]

@[expose] def ofIdx (a b : ℕ) (ha : a < 12288) (hb : b < 26040) : Coords :=
  (⟨b % 930 % 31, by omega⟩, ⟨b % 930 / 31, by omega⟩, ⟨b / 930, by omega⟩, ⟨a / 512, by omega⟩,
    ⟨a % 512 / 32, by omega⟩, ⟨a % 512 % 32, by omega⟩)

theorem idx_ofIdx {a b : ℕ} (ha : a < 12288) (hb : b < 26040) : idx (ofIdx a b ha hb) = (a, b) := by
  simp only [idx, ofIdx, Prod.mk.injEq]
  omega

variable (hrm : D.rm = 2 ^ 248 - 1)
include hrm

theorem xPt_idx (P : ℕ) (y : Coords) : xPt (xBat D P) (idx y).1 = xP D P y :=
  xPt_xBat hrm P y.2.2.2.1.isLt y.2.2.2.2.1.isLt y.2.2.2.2.2.isLt

theorem yPt_idx (P : ℕ) (y : Coords) : yPt (yBat D O P) (idx y).2 = yP O P y :=
  yPt_yBat hrm P y.1.isLt y.2.1.isLt y.2.2.1.isLt

theorem card_stabilizer_pt {i : ℕ} (hb : ∀ y3 < 24, batchChk D O i y3 = true)
    (hk : kyChk D O i = true) (hl : lowChk D O i = true)
    (hP : LIL (rowsOf (2 ^ 248 - 1) (pt D O i))) :
    Nat.card (stabilizer C.Dg (sp (pt D O i))) = lget O.sb i := by
  classical
  obtain ⟨L, hlen, hnd, hL, hgrp⟩ := Facts.lowChk_sound D O hl
  have hky : yKeys D (yBat D O (pt D O i)) = lget O.ky i := Nat.eq_of_beq_eq_true hk
  rw [C.card_stabilizer_eq, Nat.card_eq_fintype_card, Fintype.card_subtype, ← hlen,
    ← List.toFinset_card_of_nodup hnd]
  refine Finset.card_bij (fun y _ => idx y) ?_ (fun y _ y' _ e => idx_injective e) ?_
  · intro y hy
    have hy' : sp (xP D (pt D O i) y) = sp (yP O (pt D O i) y) := (Finset.mem_filter.mp hy).2
    have hkey := Act.keyL_eq (C.lil_xP hP y) (C.lil_yP hP y) hy'
    have h3 := y.2.2.2.1.isLt
    have hp : 32 * y.2.2.2.2.1.val + y.2.2.2.2.2.val < 512 := by
      have := y.2.2.2.2.1.isLt
      have := y.2.2.2.2.2.isLt
      omega
    have hq : (idx y).2 < 26040 := by
      have := y.1.isLt
      have := y.2.1.isLt
      have := y.2.2.1.isLt
      simp only [idx]
      omega
    have e1 := keyAt_xKeys hrm (pt D O i) h3 hp
    have e2 := keyAt_yKeys hrm (yBat D O (pt D O i)) hq
    rw [hky] at e2
    have hx : keyAt (xKeys D (pt D O i) y.2.2.2.1.val) (32 * y.2.2.2.2.1.val + y.2.2.2.2.2.val) =
        keyAt (lget O.ky i) (idx y).2 := by
      rw [e1, e2]
      change keyL _ (xPt (xBat D (pt D O i)) (idx y).1) = keyL _ (yPt (yBat D O (pt D O i)) (idx y).2)
      rw [xPt_idx hrm, yPt_idx hrm]
      exact hkey
    obtain ⟨g, hg, hg0, e, he, hey⟩ :=
      Facts.batchChk_sound D O (hb _ h3) _ hp _ hq hx
    have hm := hgrp _ g hg e he
    rw [hg0, hey] at hm
    exact List.mem_toFinset.mpr hm
  · intro ab hab
    have hab' := List.mem_toFinset.mp hab
    obtain ⟨ha, hb', G, hG⟩ := hL ab hab'
    refine ⟨ofIdx ab.1 ab.2 ha hb', ?_, by rw [idx_ofIdx]⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have e := idx_ofIdx ha hb'
    rw [← xPt_idx hrm, ← yPt_idx hrm, e]
    rw [hrm] at hG
    have h1 := C.lil_xP hP (ofIdx ab.1 ab.2 ha hb')
    have h2 := C.lil_yP hP (ofIdx ab.1 ab.2 ha hb')
    rw [← xPt_idx hrm, e] at h1
    rw [← yPt_idx hrm, e] at h2
    exact sp_eq_of_combChk hG h1 h2

theorem not_mem_orbit_pt {i j : ℕ} (hc : ∀ y3 < 24, crossChk D O i j y3 = true)
    (hk : kyChk D O j = true) (hPi : LIL (rowsOf (2 ^ 248 - 1) (pt D O i)))
    (hPj : LIL (rowsOf (2 ^ 248 - 1) (pt D O j))) :
    sp (pt D O i) ∉ orbit C.Dg (sp (pt D O j)) := by
  rintro ⟨⟨x, hx⟩, hxe⟩
  obtain ⟨y, hy, -⟩ := C.uniq x hx
  set A := C.t 5 y.2.2.2.2.2 * C.t 4 y.2.2.2.2.1 * C.t 3 y.2.2.2.1
  set B := C.t 2 y.2.2.1 * C.t 1 y.2.1 * C.t 0 y.1
  have e : chainProd C.t y = A * B := by
    simp only [chainProd, A, B, mul_assoc]
  have hxe' : (A * B) • sp (pt D O j) = sp (pt D O i) := by
    rw [← e, hy]
    exact hxe
  have hA : A⁻¹ • sp (pt D O i) = sp (xP D (pt D O i) y) := by
    rw [inv_smul_eq, mat_mul', mat_mul', C.mat 5 (by omega) _ (C.y5_lt y),
      C.mat 4 (by omega) _ (C.y4_lt y), C.mat 3 (by omega) _ (C.y3_lt y), mapM_mul, mapM_mul,
      xP, sp_mulB, sp_mulB, sp_mulB]
  have hB : B • sp (pt D O j) = sp (yP O (pt D O j) y) := by
    rw [smul_eq_mapM]
    simp only [B, mul_inv_rev]
    rw [mat_mul', mat_mul', ← C.inv 0 (by omega) _ (C.y0_lt y), ← C.inv 1 (by omega) _ (C.y1_lt y),
      ← C.inv 2 (by omega) _ (C.y2_lt y), mapM_mul, mapM_mul, yP, sp_mulB, sp_mulB, sp_mulB]
  rw [mul_smul, smul_eq_iff_eq_inv_smul, hB, hA] at hxe'
  have hkey := Act.keyL_eq (C.lil_xP hPi y) (C.lil_yP hPj y) hxe'.symm
  have h3 := y.2.2.2.1.isLt
  have hp : 32 * y.2.2.2.2.1.val + y.2.2.2.2.2.val < 512 := by
    have := y.2.2.2.2.1.isLt
    have := y.2.2.2.2.2.isLt
    omega
  have hq : (idx y).2 < 26040 := by
    have := y.1.isLt
    have := y.2.1.isLt
    have := y.2.2.1.isLt
    simp only [idx]
    omega
  have hky : yKeys D (yBat D O (pt D O j)) = lget O.ky j := Nat.eq_of_beq_eq_true hk
  have e1 := keyAt_xKeys hrm (pt D O i) h3 hp
  have e2 := keyAt_yKeys hrm (yBat D O (pt D O j)) hq
  rw [hky] at e2
  apply Facts.crossChk_sound D O (hc _ h3) _ hp _ hq
  rw [e1, e2]
  change keyL _ (xPt (xBat D (pt D O i)) (idx y).1) = keyL _ (yPt (yBat D O (pt D O j)) (idx y).2)
  rw [xPt_idx hrm, yPt_idx hrm]
  exact hkey

end Ctx

end CFSG.Certificates.ThDemp.Stab

end
