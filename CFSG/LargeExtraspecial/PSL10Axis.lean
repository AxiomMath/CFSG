module

public import CFSG.LargeExtraspecial.PSL10Fix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.PSLPSU10

open Subgroup CFSG.Open Matrix
open scoped MatrixGroups

variable {n : ℕ}

theorem add_self_eq_zero_zmod_two (X : Matrix (Fin n) (Fin n) (ZMod 2)) : X + X = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (X i j)

theorem sub_one_mul_self_of_mul_self {t : SL(n, ZMod 2)} (ht : t * t = 1) :
    ((t : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * ((t : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) =
      0 := by
  have h : (t : Matrix (Fin n) (Fin n) (ZMod 2)) * t = 1 := congrArg (fun x : SL(n, ZMod 2) =>
    (x : Matrix (Fin n) (Fin n) (ZMod 2))) ht
  have e : ((t : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * ((t : Matrix (Fin n) (Fin n) (ZMod 2)) -
      1) = ((t : Matrix (Fin n) (Fin n) (ZMod 2)) * t + 1) -
        ((t : Matrix (Fin n) (Fin n) (ZMod 2)) + t) := by noncomm_ring
  rw [e, h, add_self_eq_zero_zmod_two, add_self_eq_zero_zmod_two, sub_zero]

section Axis

variable {t : SL(n, ZMod 2)}

@[expose] def cmat (c : centralizer ({t} : Set SL(n, ZMod 2))) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  ((c : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))

theorem cmat_mul (a b : centralizer ({t} : Set SL(n, ZMod 2))) : cmat (a * b) = cmat a * cmat b :=
  rfl

theorem cmat_one : cmat (1 : centralizer ({t} : Set SL(n, ZMod 2))) = 1 :=
  rfl

theorem cmat_injective : Function.Injective (cmat (t := t)) := fun _ _ h =>
  Subtype.ext (Subtype.ext h)

theorem cmat_pow (a : centralizer ({t} : Set SL(n, ZMod 2))) (k : ℕ) :
    cmat (a ^ k) = cmat a ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, cmat_mul, ih, pow_succ]

theorem sub_one_mul_cmat (c : centralizer ({t} : Set SL(n, ZMod 2))) :
    ((t : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * cmat c =
      cmat c * ((t : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) := by
  have h : cmat c * (t : Matrix (Fin n) (Fin n) (ZMod 2)) = (t : Matrix (Fin n) (Fin n) (ZMod 2)) *
      cmat c := congrArg (fun x : SL(n, ZMod 2) => (x : Matrix (Fin n) (Fin n) (ZMod 2)))
    (mem_centralizer_singleton_iff.mp c.2)
  rw [sub_mul, mul_sub, one_mul, mul_one, h]

@[expose] def slMat (n : ℕ) : SL(n, ZMod 2) →* Matrix (Fin n) (Fin n) (ZMod 2) where
  toFun g := g
  map_one' := rfl
  map_mul' _ _ := rfl

theorem slMat_injective : Function.Injective (slMat n) := fun _ _ h => Subtype.ext h

@[expose] def axisGroup (t : SL(n, ZMod 2)) (ht : t * t = 1) :
    Subgroup (centralizer ({t} : Set SL(n, ZMod 2))) :=
  axisGroupOf (slMat n) t (sub_one_mul_self_of_mul_self ht)

theorem mem_axisGroup {ht : t * t = 1} {c : centralizer ({t} : Set SL(n, ZMod 2))} :
    c ∈ axisGroup t ht ↔ (∃ X, cmat c - 1 = ((t : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * X) ∧
      ∃ Y, cmat c - 1 = Y * ((t : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) :=
  Iff.rfl

theorem axisGroup_normal (ht : t * t = 1) : (axisGroup t ht).Normal :=
  axisGroupOf_normal _ _ _

theorem axisGroup_comm (ht : t * t = 1) :
    ∀ a ∈ axisGroup t ht, ∀ b ∈ axisGroup t ht, a * b = b * a :=
  axisGroupOf_comm _ slMat_injective _ _

@[expose] noncomputable def colAction :
    centralizer ({t} : Set SL(n, ZMod 2)) →* Module.End (ZMod 2) (Fin n → ZMod 2) where
  toFun g := Matrix.toLin' (cmat g)
  map_one' := Matrix.toLin'_one
  map_mul' _ _ := Matrix.toLin'_mul _ _

theorem colAction_apply (g : centralizer ({t} : Set SL(n, ZMod 2))) (v : Fin n → ZMod 2) :
    colAction g v = cmat g *ᵥ v :=
  Matrix.toLin'_apply _ _

@[expose] noncomputable def rowAction :
    centralizer ({t} : Set SL(n, ZMod 2)) →* Module.End (ZMod 2) (Fin n → ZMod 2) where
  toFun g := Matrix.toLin' (cmat g⁻¹)ᵀ
  map_one' := by
    rw [inv_one, cmat_one, transpose_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [_root_.mul_inv_rev, cmat_mul, transpose_mul, Matrix.toLin'_mul]
    rfl

theorem rowAction_apply (g : centralizer ({t} : Set SL(n, ZMod 2))) (v : Fin n → ZMod 2) :
    rowAction g v = v ᵥ* cmat g⁻¹ := by
  rw [rowAction, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.toLin'_apply, mulVec_transpose]

theorem det_eq_one_of_mul_self {s : Matrix (Fin n) (Fin n) (ZMod 2)} (hs : s * s = 1) :
    s.det = 1 := by
  have h := congrArg Matrix.det hs
  rw [Matrix.det_mul, Matrix.det_one] at h
  revert h
  generalize s.det = d
  revert d
  decide

theorem exists_eq_one_add_vecMulVec (ht : t * t = 1) (ht1 : t ≠ 1)
    (hP : IsPGroup 2 (timmesfeldFStar (centralizer ({t} : Set SL(n, ZMod 2)))))
    (hZ : Nat.card (center (timmesfeldFStar (centralizer ({t} : Set SL(n, ZMod 2))))) = 2) :
    ∃ w ψ : Fin n → ZMod 2, w ≠ 0 ∧ ψ ≠ 0 ∧ ψ ⬝ᵥ w = 0 ∧
      (t : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + vecMulVec w ψ := by
  obtain ⟨D, hD⟩ : ∃ D, (t : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 = D := ⟨_, rfl⟩
  have hDD : D * D = 0 := hD ▸ sub_one_mul_self_of_mul_self ht
  have hcomm : ∀ c : centralizer ({t} : Set SL(n, ZMod 2)), D * cmat c = cmat c * D :=
    fun c => hD ▸ sub_one_mul_cmat c
  have hD0 : D ≠ 0 := by
    rintro rfl
    exact ht1 (Subtype.ext (sub_eq_zero.mp hD))
  have hU₁ : LinearMap.range (Matrix.toLin' D) ≠ ⊥ := by
    rw [Ne, LinearMap.range_eq_bot, LinearEquiv.map_eq_zero_iff]
    exact hD0
  obtain ⟨w, ⟨u, hu⟩, hw0, hwfix⟩ := exists_ne_zero_forall_eq hP
    ((colAction (t := t)).comp (timmesfeldFStar _).subtype) hU₁ (by
      rintro g _ ⟨v, rfl⟩
      refine ⟨cmat (g : centralizer ({t} : Set SL(n, ZMod 2))) *ᵥ v, ?_⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, colAction_apply, Matrix.toLin'_apply,
        Matrix.toLin'_apply, mulVec_mulVec, mulVec_mulVec, hcomm])
  rw [Matrix.toLin'_apply] at hu
  have hwfix' : ∀ g ∈ timmesfeldFStar (centralizer ({t} : Set SL(n, ZMod 2))),
      cmat g *ᵥ w = w := fun g hg => (colAction_apply _ _).symm.trans (hwfix ⟨g, hg⟩)
  have hU₂ : LinearMap.range (Matrix.toLin' Dᵀ) ≠ ⊥ := by
    rw [Ne, LinearMap.range_eq_bot, LinearEquiv.map_eq_zero_iff, transpose_eq_zero]
    exact hD0
  obtain ⟨ψ, ⟨φ, hφ⟩, hψ0, hψfix⟩ := exists_ne_zero_forall_eq hP
    ((rowAction (t := t)).comp (timmesfeldFStar _).subtype) hU₂ (by
      rintro g _ ⟨v, rfl⟩
      refine ⟨(cmat (g : centralizer ({t} : Set SL(n, ZMod 2)))⁻¹)ᵀ *ᵥ v, ?_⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, rowAction_apply, Matrix.toLin'_apply,
        Matrix.toLin'_apply, mulVec_transpose, mulVec_transpose, mulVec_transpose, vecMul_vecMul,
        vecMul_vecMul, hcomm])
  rw [Matrix.toLin'_apply, mulVec_transpose] at hφ
  have hψfix' : ∀ g ∈ timmesfeldFStar (centralizer ({t} : Set SL(n, ZMod 2))),
      ψ ᵥ* cmat g = ψ := fun g hg => by
    have h := (rowAction_apply _ _).symm.trans (hψfix ⟨g⁻¹, inv_mem hg⟩)
    change ψ ᵥ* cmat g⁻¹⁻¹ = ψ at h
    rwa [inv_inv] at h
  have hV1 : vecMulVec w ψ = D * vecMulVec u ψ := by rw [mul_vecMulVec, hu]
  have hV2 : vecMulVec w ψ = vecMulVec w φ * D := by rw [vecMulVec_mul, hφ]
  have hVV := mul_eq_zero_of_factor hDD hV1 hV2
  have hψw : ψ ⬝ᵥ w = 0 := by
    rw [← hφ, ← hu, ← dotProduct_mulVec, mulVec_mulVec, hDD, zero_mulVec, dotProduct_zero]
  have hSS : (1 + vecMulVec w ψ) * (1 + vecMulVec w ψ) = 1 := by
    have e : (1 + vecMulVec w ψ) * (1 + vecMulVec w ψ) =
        1 + (vecMulVec w ψ + vecMulVec w ψ) + vecMulVec w ψ * vecMulVec w ψ := by noncomm_ring
    rw [e, add_self_eq_zero_zmod_two, hVV, add_zero, add_zero]
  let sSL : SL(n, ZMod 2) := ⟨1 + vecMulVec w ψ, det_eq_one_of_mul_self hSS⟩
  have hVD : vecMulVec w ψ * D = 0 := by rw [hV2, mul_assoc, hDD, mul_zero]
  have hDV : D * vecMulVec w ψ = 0 := by rw [hV1, ← mul_assoc, hDD, zero_mul]
  have hT : (t : Matrix (Fin n) (Fin n) (ZMod 2)) = D + 1 := (sub_eq_iff_eq_add.mp hD)
  have hst : sSL * t = t * sSL := by
    apply Subtype.ext
    change (1 + vecMulVec w ψ) * (t : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (t : Matrix (Fin n) (Fin n) (ZMod 2)) * (1 + vecMulVec w ψ)
    have e1 : (1 + vecMulVec w ψ) * (D + 1) = 1 + vecMulVec w ψ + D + vecMulVec w ψ * D := by
      noncomm_ring
    have e2 : (D + 1) * (1 + vecMulVec w ψ) = 1 + vecMulVec w ψ + D + D * vecMulVec w ψ := by
      noncomm_ring
    rw [hT, e1, e2, hVD, hDV]
  let sC : centralizer ({t} : Set SL(n, ZMod 2)) := ⟨sSL, mem_centralizer_singleton_iff.mpr hst⟩
  have hsC : cmat sC = 1 + vecMulVec w ψ := rfl
  have hsA : sC ∈ axisGroup t ht := by
    rw [mem_axisGroup, hD, hsC, add_sub_cancel_left]
    exact ⟨⟨_, hV1⟩, ⟨_, hV2⟩⟩
  let tC : centralizer ({t} : Set SL(n, ZMod 2)) := ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩
  have htZ : tC ∈ center (centralizer ({t} : Set SL(n, ZMod 2))) :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have htC1 : tC ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hsc : ∀ x ∈ timmesfeldFStar (centralizer ({t} : Set SL(n, ZMod 2))), x * sC = sC * x := by
    intro x hx
    apply cmat_injective
    rw [cmat_mul, cmat_mul, hsC, mul_add, add_mul, mul_one, one_mul, mul_vecMulVec, vecMulVec_mul,
      hwfix' x hx, hψfix' x hx]
  rcases eq_one_or_eq_of_centralizes_fstar hZ htZ htC1 (axisGroup_normal ht) (axisGroup_comm ht)
    hsA hsc with h | h
  · exfalso
    have hV : vecMulVec w ψ = 0 := by
      have h1 : cmat sC = 1 := by rw [h, cmat_one]
      rw [hsC] at h1
      exact (add_eq_left.mp h1)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw0
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hψ0
    have := congrFun (congrFun hV i) j
    rw [vecMulVec_apply] at this
    exact mul_ne_zero hi hj this
  · exact ⟨w, ψ, hw0, hψ0, hψw, by rw [← hsC, h]; rfl⟩

end Axis

end CFSG.LargeExtraspecial.S14.PSLPSU10
