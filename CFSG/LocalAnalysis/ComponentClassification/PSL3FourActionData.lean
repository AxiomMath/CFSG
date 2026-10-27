module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ComponentClassification.PSL3Four

open Matrix

structure F4 where
  code : Fin 4
deriving DecidableEq

namespace F4

@[expose] def codeEquiv : F4 ≃ Fin 4 where
  toFun := code
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype F4 := Fintype.ofEquiv (Fin 4) codeEquiv.symm

@[expose] def mulCode (a b : Fin 4) : Fin 4 :=
  ⟨(a.val % 2 * (b.val % 2) + a.val / 2 * (b.val / 2)) % 2 +
    2 * ((a.val % 2 * (b.val / 2) + a.val / 2 * (b.val % 2) + a.val / 2 * (b.val / 2)) % 2),
    by omega⟩

instance : Zero F4 := ⟨⟨0⟩⟩

instance : One F4 := ⟨⟨1⟩⟩

instance : Add F4 := ⟨fun a b => ⟨a.code ^^^ b.code⟩⟩

instance : Mul F4 := ⟨fun a b => ⟨mulCode a.code b.code⟩⟩

instance : Neg F4 := ⟨fun a => a⟩

instance : Sub F4 := ⟨fun a b => a + b⟩

instance : Inv F4 := ⟨fun a => a * a⟩

instance : CommRing F4 where
  add := (· + ·)
  mul := (· * ·)
  zero := 0
  one := 1
  neg := Neg.neg
  sub := Sub.sub
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  mul_comm := by decide
  neg_add_cancel := by decide
  sub_eq_add_neg := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec

instance : Field F4 where
  inv := Inv.inv
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := by decide
  inv_zero := by decide
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

@[expose] def ω : F4 := ⟨2⟩

theorem card_eq : Fintype.card F4 = 4 := rfl

theorem roots_quadratic : ∀ x : F4, x * x + x + 1 = 0 ↔ x = ω ∨ x = 1 + ω := by decide

end F4

open F4

abbrev Vec := Fin 3 → F4

@[expose] def lead (v : Vec) : F4 := if v 0 ≠ 0 then v 0 else if v 1 ≠ 0 then v 1 else v 2

@[expose] def normalize (v : Vec) : Vec := fun i => (lead v)⁻¹ * v i

@[expose] def allVecs : List Vec :=
  (List.finRange 4).flatMap fun x => (List.finRange 4).flatMap fun y =>
    (List.finRange 4).map fun z => ![⟨x⟩, ⟨y⟩, ⟨z⟩]

@[expose] def V : List Vec := allVecs.filter fun v => decide (v ≠ 0 ∧ normalize v = v)

@[expose] def vecOf (i : Fin 42) : Vec := V.getD (i.val % 21) 0

@[expose] def vIdx (u : Vec) : ℕ := V.idxOf (normalize u) % 21

theorem vIdx_lt (u : Vec) : vIdx u < 21 := Nat.mod_lt _ (by norm_num)

theorem length_V : V.length = 21 := by decide

theorem nodup_V : V.Nodup := by decide

theorem mem_allVecs (v : Vec) : v ∈ allVecs := by
  have hv : v = ![⟨(v 0).code⟩, ⟨(v 1).code⟩, ⟨(v 2).code⟩] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [allVecs, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨_, _, _, rfl⟩

theorem mem_V {v : Vec} : v ∈ V ↔ v ≠ 0 ∧ normalize v = v := by
  simp only [V, List.mem_filter, decide_eq_true_eq, mem_allVecs v, true_and]

theorem lead_ne_zero {v : Vec} (hv : v ≠ 0) : lead v ≠ 0 := by
  unfold lead
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        funext i
        fin_cases i
        exacts [h0, h1, h2]
      simp [h0, h1, h2]
    · simp [h0, h1]
  · simp [h0]

theorem lead_smul {c : F4} (hc : c ≠ 0) (v : Vec) : lead (c • v) = c * lead v := by
  unfold lead
  simp only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, hc, false_or]
  split_ifs <;> rfl

theorem normalize_smul {c : F4} (hc : c ≠ 0) (v : Vec) : normalize (c • v) = normalize v := by
  funext i
  show (lead (c • v))⁻¹ * (c * v i) = (lead v)⁻¹ * v i
  rw [lead_smul hc, mul_inv, mul_comm c⁻¹, mul_assoc, ← mul_assoc c⁻¹, inv_mul_cancel₀ hc,
    one_mul]

theorem normalize_eq_smul (v : Vec) : normalize v = (lead v)⁻¹ • v := rfl

theorem normalize_ne_zero {v : Vec} (hv : v ≠ 0) : normalize v ≠ 0 := by
  rw [normalize_eq_smul]
  exact smul_ne_zero (inv_ne_zero (lead_ne_zero hv)) hv

theorem normalize_normalize (v : Vec) : normalize (normalize v) = normalize v := by
  by_cases hv : v = 0
  · subst hv
    decide
  · calc normalize (normalize v) = normalize ((lead v)⁻¹ • v) := rfl
      _ = normalize v := normalize_smul (inv_ne_zero (lead_ne_zero hv)) v

theorem normalize_mem {u : Vec} (hu : u ≠ 0) : normalize u ∈ V :=
  mem_V.2 ⟨normalize_ne_zero hu, normalize_normalize u⟩

theorem idxOf_lt {u : Vec} (hu : u ≠ 0) : V.idxOf (normalize u) < 21 := by
  rw [← length_V]
  exact List.idxOf_lt_length_of_mem (normalize_mem hu)

theorem vIdx_eq {u : Vec} (hu : u ≠ 0) : vIdx u = V.idxOf (normalize u) :=
  Nat.mod_eq_of_lt (idxOf_lt hu)

theorem getD_vIdx {u : Vec} (hu : u ≠ 0) : V.getD (vIdx u) 0 = normalize u := by
  rw [vIdx_eq hu, List.getD_eq_getElem _ _ (by rw [length_V]; exact idxOf_lt hu)]
  exact List.getElem_idxOf (by rw [length_V]; exact idxOf_lt hu)

theorem vIdx_smul {c : F4} (hc : c ≠ 0) (u : Vec) : vIdx (c • u) = vIdx u := by
  rw [vIdx, vIdx, normalize_smul hc]

theorem vecOf_mem (i : Fin 42) : vecOf i ∈ V := by
  rw [vecOf, List.getD_eq_getElem _ _ (by rw [length_V]; omega)]
  exact List.getElem_mem _

theorem vecOf_ne_zero (i : Fin 42) : vecOf i ≠ 0 := (mem_V.1 (vecOf_mem i)).1

theorem vIdx_vecOf (i : Fin 42) : vIdx (vecOf i) = i.val % 21 := by
  have hlt : i.val % 21 < V.length := by rw [length_V]; omega
  rw [vIdx, (mem_V.1 (vecOf_mem i)).2, vecOf, List.getD_eq_getElem _ _ hlt,
    nodup_V.idxOf_getElem _ hlt]
  exact Nat.mod_eq_of_lt (by omega)

theorem vecOf_of_lt {j : ℕ} (hj : j < 21) (h : j < 42) : vecOf ⟨j, h⟩ = V.getD j 0 := by
  show V.getD (j % 21) 0 = V.getD j 0
  rw [Nat.mod_eq_of_lt hj]

theorem vecOf_add {j : ℕ} (hj : j < 21) (h : 21 + j < 42) : vecOf ⟨21 + j, h⟩ = V.getD j 0 := by
  show V.getD ((21 + j) % 21) 0 = V.getD j 0
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt hj]

theorem mulVec_ne_zero (A : GL (Fin 3) F4) {u : Vec} (hu : u ≠ 0) :
    (A : Matrix (Fin 3) (Fin 3) F4) *ᵥ u ≠ 0 := by
  intro h
  apply hu
  have := congrArg (fun w => ((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ w) h
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
  rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this

@[expose] def rhoFun (A : GL (Fin 3) F4) (i : Fin 42) : Fin 42 :=
  if i.val < 21 then
    ⟨vIdx ((A : Matrix (Fin 3) (Fin 3) F4) *ᵥ vecOf i),
      by have := vIdx_lt (A.val *ᵥ vecOf i); omega⟩
  else
    ⟨21 + vIdx (((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ *ᵥ vecOf i),
      by have := vIdx_lt ((A⁻¹ : GL (Fin 3) F4).valᵀ *ᵥ vecOf i); omega⟩

theorem vIdx_mulVec_mulVec (M N : GL (Fin 3) F4) {v : Vec} (hv : v ≠ 0) :
    vIdx ((M : Matrix (Fin 3) (Fin 3) F4) *ᵥ V.getD (vIdx ((N : Matrix (Fin 3) (Fin 3) F4) *ᵥ v)) 0)
      = vIdx (((M * N : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ v) := by
  have hN := mulVec_ne_zero N hv
  rw [getD_vIdx hN, normalize_eq_smul, Matrix.mulVec_smul,
    vIdx_smul (inv_ne_zero (lead_ne_zero hN)), Matrix.mulVec_mulVec, Units.val_mul]

theorem inv_transpose_mul (A B : GL (Fin 3) F4) :
    (((A * B)⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ =
      ((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ *
        ((B⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ := by
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

@[expose] def invTranspose (A : GL (Fin 3) F4) : GL (Fin 3) F4 :=
  ⟨((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ,
    ((A : Matrix (Fin 3) (Fin 3) F4))ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]⟩

theorem coe_invTranspose (A : GL (Fin 3) F4) :
    ((invTranspose A : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      ((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ := rfl

theorem invTranspose_mul (A B : GL (Fin 3) F4) :
    invTranspose (A * B) = invTranspose A * invTranspose B :=
  Units.ext (by rw [Units.val_mul, coe_invTranspose, coe_invTranspose, coe_invTranspose,
    inv_transpose_mul])

theorem rhoFun_rhoFun (A B : GL (Fin 3) F4) (i : Fin 42) :
    rhoFun A (rhoFun B i) = rhoFun (A * B) i := by
  by_cases hi : i.val < 21
  · have hj := vIdx_lt ((B : Matrix (Fin 3) (Fin 3) F4) *ᵥ vecOf i)
    simp only [rhoFun, hi, ↓reduceIte, hj]
    apply Fin.ext
    simp only
    rw [vecOf_of_lt hj, vIdx_mulVec_mulVec A B (vecOf_ne_zero i)]
  · have hj := vIdx_lt (((B⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ *ᵥ vecOf i)
    have hnot :
        ¬ 21 + vIdx (((B⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ *ᵥ vecOf i) < 21 := by
      omega
    simp only [rhoFun, hi, ↓reduceIte, hnot]
    apply Fin.ext
    simp only [Nat.add_left_cancel_iff]
    rw [vecOf_add hj, ← coe_invTranspose, ← coe_invTranspose, ← coe_invTranspose,
      vIdx_mulVec_mulVec _ _ (vecOf_ne_zero i), invTranspose_mul]

theorem rhoFun_one (i : Fin 42) : rhoFun 1 i = i := by
  apply Fin.ext
  by_cases hi : i.val < 21
  · simp only [rhoFun, hi, ↓reduceIte, Units.val_one, Matrix.one_mulVec, vIdx_vecOf]
    omega
  · simp only [rhoFun, hi, ↓reduceIte, inv_one, Units.val_one, Matrix.transpose_one,
      Matrix.one_mulVec, vIdx_vecOf]
    omega

@[expose] def rho : GL (Fin 3) F4 →* Equiv.Perm (Fin 42) where
  toFun A :=
    { toFun := rhoFun A
      invFun := rhoFun A⁻¹
      left_inv := fun i => by rw [rhoFun_rhoFun, inv_mul_cancel, rhoFun_one]
      right_inv := fun i => by rw [rhoFun_rhoFun, mul_inv_cancel, rhoFun_one] }
  map_one' := Equiv.ext rhoFun_one
  map_mul' A B := Equiv.ext fun i => (rhoFun_rhoFun A B i).symm

theorem rho_apply (A : GL (Fin 3) F4) (i : Fin 42) : rho A i = rhoFun A i := rfl

@[expose] def aMat : Matrix (Fin 3) (Fin 3) F4 := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def bMat : Matrix (Fin 3) (Fin 3) F4 := 1 + Matrix.single 0 1 1

@[expose] def cMat : Matrix (Fin 3) (Fin 3) F4 := 1 + Matrix.single 0 1 ω

@[expose] def dMat : Matrix (Fin 3) (Fin 3) F4 := Matrix.diagonal ![ω, 1, 1]

@[expose] def aGL : GL (Fin 3) F4 :=
  ⟨aMat, !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩

@[expose] def bGL : GL (Fin 3) F4 := ⟨bMat, bMat, by decide, by decide⟩

@[expose] def cGL : GL (Fin 3) F4 := ⟨cMat, cMat, by decide, by decide⟩

@[expose] def dGL : GL (Fin 3) F4 :=
  ⟨dMat, Matrix.diagonal ![1 + ω, 1, 1], by decide, by decide⟩

@[expose] def g₁ : Equiv.Perm (Fin 42) := rho aGL

@[expose] def g₂ : Equiv.Perm (Fin 42) := rho bGL

@[expose] def g₃ : Equiv.Perm (Fin 42) := rho cGL

@[expose] def g₄ : Equiv.Perm (Fin 42) := rho dGL

@[expose] def g5Fun (i : Fin 42) : Fin 42 :=
  ⟨21 * (i.val / 21) + vIdx (fun k => vecOf i k ^ 2), by
    have := vIdx_lt (fun k => vecOf i k ^ 2)
    have : i.val / 21 ≤ 1 := by omega
    omega⟩

theorem g5Fun_g5Fun (i : Fin 42) : g5Fun (g5Fun i) = i := by revert i; decide

@[expose] def g6Fun (i : Fin 42) : Fin 42 :=
  if h : i.val < 21 then ⟨i.val + 21, by omega⟩ else ⟨i.val - 21, by omega⟩

theorem g6Fun_g6Fun (i : Fin 42) : g6Fun (g6Fun i) = i := by revert i; decide

@[expose] def g₅ : Equiv.Perm (Fin 42) := ⟨g5Fun, g5Fun, g5Fun_g5Fun, g5Fun_g5Fun⟩

@[expose] def g₆ : Equiv.Perm (Fin 42) := ⟨g6Fun, g6Fun, g6Fun_g6Fun, g6Fun_g6Fun⟩

@[expose] def S : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure {g₁, g₂, g₃}

@[expose] def R : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure {g₁, g₂, g₃, g₄, g₅, g₆}

@[expose] def r₁ : Equiv.Perm (Fin 42) := g₁ ^ 2 * g₂ * g₁

@[expose] def r₂ : Equiv.Perm (Fin 42) := g₅

@[expose] def r₃ : Equiv.Perm (Fin 42) := g₆

@[expose] def r₄ : Equiv.Perm (Fin 42) := g₅ * g₆

@[expose] def C₁ : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.centralizer {r₁} ⊓ S

@[expose] def C₂ : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.centralizer {r₂} ⊓ S

@[expose] def C₃ : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.centralizer {r₃} ⊓ S

@[expose] def C₄ : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.centralizer {r₄} ⊓ S

theorem det_aMat : aMat.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

theorem det_bMat : bMat.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

theorem det_cMat : cMat.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

theorem det_dMat : dMat.det = ω := by
  rw [Matrix.det_fin_three]
  decide

theorem action_data :
    Fintype.card F4 = 4 ∧ (∀ x : F4, x * x + x + 1 = 0 ↔ x = ω ∨ x = 1 + ω) ∧
      V.length = 21 ∧ V.Nodup ∧ (∀ v : Vec, v ∈ V ↔ v ≠ 0 ∧ normalize v = v) ∧
      (∀ u : Vec, u ≠ 0 → normalize u = (lead u)⁻¹ • u ∧ normalize u ∈ V) ∧
      (∀ A B : GL (Fin 3) F4, rho (A * B) = rho A * rho B) ∧
      aMat.det = 1 ∧ bMat.det = 1 ∧ cMat.det = 1 ∧ dMat.det = ω ∧
      g₅ * g₅ = 1 ∧ g₆ * g₆ = 1 :=
  ⟨F4.card_eq, F4.roots_quadratic, length_V, nodup_V, fun _ => mem_V,
    fun _ hu => ⟨normalize_eq_smul _, normalize_mem hu⟩, map_mul rho, det_aMat, det_bMat,
    det_cMat, det_dMat, Equiv.ext g5Fun_g5Fun, Equiv.ext g6Fun_g6Fun⟩

end CFSG.ComponentClassification.PSL3Four
