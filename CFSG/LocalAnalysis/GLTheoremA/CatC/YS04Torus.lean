module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS04G

open Matrix

section Diag

variable (n : ℕ) (F : Type) [Field F]

@[expose] noncomputable def diagGL : (Fin n → Fˣ) →* GL (Fin n) F :=
  (Units.map (Matrix.diagonalRingHom (Fin n) F).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin n => F)).symm.toMonoidHom

theorem diagGL_coe (d : Fin n → Fˣ) :
    ((diagGL n F d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun i => (d i : F)) := rfl

theorem diagGL_injective : Function.Injective (diagGL n F) := by
  intro d d' h
  have h1 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h
  simp only [diagGL_coe] at h1
  funext i
  have := Matrix.diagonal_injective h1
  exact Units.ext (congrFun this i)

end Diag


section Signed

variable {n : ℕ} {F : Type} [Field F]

@[expose] noncomputable def tMat (i0 i1 i2 : Fin n) : Matrix (Fin n) (Fin n) F :=
  Matrix.diagonal (fun i => if i = i2 then (-1 : F) else 1) * (Equiv.swap i0 i1).permMatrix F

variable {i0 i1 i2 : Fin n}

theorem permMatrix_mul_diagonal (σ : Equiv.Perm (Fin n)) (e : Fin n → F)
    (he : ∀ i, e (σ i) = e i) :
    σ.permMatrix F * Matrix.diagonal e = Matrix.diagonal e * σ.permMatrix F := by
  ext i j
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply, Matrix.diagonal_apply,
    id_eq, Equiv.symm_apply_eq]
  by_cases h : σ i = j
  · subst h
    simp [he]
  · have h' : ¬ i = σ.symm j := fun h' => h ((Equiv.apply_eq_iff_eq_symm_apply σ).2 h')
    simp [h, h']

@[expose] def sgn (F : Type) [Field F] (i2 : Fin n) : Fin n → F := fun i => if i = i2 then -1 else 1

theorem sgn_sq (i2 : Fin n) (i : Fin n) : sgn F i2 i * sgn F i2 i = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem sgn_swap (h20 : i2 ≠ i0) (h21 : i2 ≠ i1) (i : Fin n) :
    sgn F i2 (Equiv.swap i0 i1 i) = sgn F i2 i := by
  unfold sgn
  by_cases h0 : i = i0
  · subst h0
    simp [Equiv.swap_apply_left, h21.symm, h20.symm]
  · by_cases h1 : i = i1
    · subst h1
      simp [Equiv.swap_apply_right, h20.symm, h21.symm]
    · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]

theorem tMat_def : (tMat i0 i1 i2 : Matrix (Fin n) (Fin n) F) =
    Matrix.diagonal (sgn F i2) * (Equiv.swap i0 i1).permMatrix F := rfl

theorem tMat_mul_self (h20 : i2 ≠ i0) (h21 : i2 ≠ i1) :
    (tMat i0 i1 i2 : Matrix (Fin n) (Fin n) F) * tMat i0 i1 i2 = 1 := by
  set P : Matrix (Fin n) (Fin n) F := (Equiv.swap i0 i1).permMatrix F with hP
  set D : Matrix (Fin n) (Fin n) F := Matrix.diagonal (sgn F i2) with hD
  have hPD : P * D = D * P := permMatrix_mul_diagonal _ _ (sgn_swap h20 h21)
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one
    exact sgn_sq i2 _
  have hPP : P * P = 1 := by
    rw [hP, ← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
  rw [tMat_def]
  calc D * P * (D * P) = D * (P * D) * P := by simp only [Matrix.mul_assoc]
    _ = D * (D * P) * P := by rw [hPD]
    _ = (D * D) * (P * P) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hDD, hPP, Matrix.mul_one]

theorem tMat_transpose (h20 : i2 ≠ i0) (h21 : i2 ≠ i1) :
    (tMat i0 i1 i2 : Matrix (Fin n) (Fin n) F)ᵀ = tMat i0 i1 i2 := by
  rw [tMat_def, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.transpose_permMatrix,
    Equiv.swap_inv]
  exact permMatrix_mul_diagonal _ _ (sgn_swap h20 h21)

theorem tMat_det (h01 : i0 ≠ i1) :
    (tMat i0 i1 i2 : Matrix (Fin n) (Fin n) F).det = 1 := by
  rw [tMat_def, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation,
    Equiv.Perm.sign_swap h01]
  unfold sgn
  simp [Finset.prod_ite_eq']

theorem tMat_commute (h20 : i2 ≠ i0) (h21 : i2 ≠ i1) (e : Fin n → F)
    (he : ∀ i, e (Equiv.swap i0 i1 i) = e i) :
    (tMat i0 i1 i2 : Matrix (Fin n) (Fin n) F) * Matrix.diagonal e =
      Matrix.diagonal e * tMat i0 i1 i2 := by
  rw [tMat_def, Matrix.mul_assoc, permMatrix_mul_diagonal _ _ he, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  exact mul_comm _ _

theorem tMat_apply_01 (h20 : i2 ≠ i0) (h01 : i0 ≠ i1) :
    (tMat i0 i1 i2 : Matrix (Fin n) (Fin n) F) i0 i1 = 1 := by
  rw [tMat_def, Matrix.diagonal_mul]
  simp [sgn, h20.symm, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

theorem tMat_map_pow (q : ℕ) (hq : q ≠ 0) (hneg : (-1 : F) ^ q = -1) :
    (tMat i0 i1 i2 : Matrix (Fin n) (Fin n) F).map (· ^ q) = tMat i0 i1 i2 := by
  ext i j
  rw [Matrix.map_apply, tMat_def, Matrix.diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, sgn]
  by_cases hij : Equiv.swap i0 i1 i = j
  · by_cases hi : i = i2
    · simp [hij, hi, hneg, zero_pow hq]
    · simp [hij, hi, zero_pow hq]
  · simp [Option.mem_def, hij, zero_pow hq]

theorem diagonal_unitary (e : Fin n → F) (q : ℕ) (hq : q ≠ 0) (he : ∀ i, e i ^ q * e i = 1) :
    ((Matrix.diagonal e).map (· ^ q))ᵀ * Matrix.diagonal e = 1 := by
  have h1 : (Matrix.diagonal e).map (· ^ q) = Matrix.diagonal (fun i => e i ^ q) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply, hij, zero_pow hq]
  rw [h1, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one
  exact he _

theorem tMat_unitary (h20 : i2 ≠ i0) (h21 : i2 ≠ i1) (q : ℕ) (hq : q ≠ 0)
    (hneg : (-1 : F) ^ q = -1) :
    ((tMat i0 i1 i2 : Matrix (Fin n) (Fin n) F).map (· ^ q))ᵀ * tMat i0 i1 i2 = 1 := by
  rw [tMat_map_pow q hq hneg, tMat_transpose h20 h21, tMat_mul_self h20 h21]

end Signed

section Torus

variable {F : Type} [Field F]

@[expose] noncomputable def constraint (n : ℕ) (i0 i1 : Fin n) (ω : Fˣ) :
    (Fin n → Subgroup.zpowers ω) →* Subgroup.zpowers ω × Subgroup.zpowers ω where
  toFun d := (d i0 * (d i1)⁻¹, ∏ i, d i)
  map_one' := by simp
  map_mul' d d' := by
    refine Prod.ext ?_ ?_
    · simp only [Pi.mul_apply, mul_inv, Prod.fst_mul]
      exact mul_mul_mul_comm _ _ _ _
    · simp [Finset.prod_mul_distrib]

theorem pow_le_card_ker_constraint {p : ℕ} (hp : p.Prime) {ω : Fˣ} (hω : orderOf ω = p) {n : ℕ}
    (hn : 2 ≤ n) (i0 i1 : Fin n) :
    p ^ (n - 2) ≤ Nat.card (constraint n i0 i1 ω).ker := by
  have hZ : Nat.card (Subgroup.zpowers ω) = p := by rw [Nat.card_zpowers, hω]
  haveI : Finite (Subgroup.zpowers ω) := Nat.finite_of_card_ne_zero (by rw [hZ]; exact hp.ne_zero)
  have hT : Nat.card (Fin n → Subgroup.zpowers ω) = p ^ n := by
    rw [Nat.card_pi]
    simp [hZ]
  have h1 := Subgroup.card_ker_mul_card_range (constraint n i0 i1 ω)
  rw [hT] at h1
  have h2 : Nat.card (constraint n i0 i1 ω).range ≤ p ^ 2 := by
    calc Nat.card (constraint n i0 i1 ω).range
        ≤ Nat.card (Subgroup.zpowers ω × Subgroup.zpowers ω) := Subgroup.card_le_card_group _
      _ = p ^ 2 := by rw [Nat.card_prod, hZ]; ring
  have h3 : p ^ (n - 2) * p ^ 2 ≤ Nat.card (constraint n i0 i1 ω).ker * p ^ 2 := by
    calc p ^ (n - 2) * p ^ 2 = p ^ n := by rw [← pow_add]; congr 1; omega
      _ = Nat.card (constraint n i0 i1 ω).ker * Nat.card (constraint n i0 i1 ω).range := h1.symm
      _ ≤ Nat.card (constraint n i0 i1 ω).ker * p ^ 2 := Nat.mul_le_mul_left _ h2
  exact Nat.le_of_mul_le_mul_right h3 (by have := hp.pos; positivity)

@[expose] noncomputable def torusHom (n : ℕ) (F : Type) [Field F] (ω : Fˣ) :
    (Fin n → Subgroup.zpowers ω) →* GL (Fin n) F :=
  (diagGL n F).comp (MonoidHom.compLeft (Subgroup.zpowers ω).subtype (Fin n))

theorem torusHom_coe (n : ℕ) (ω : Fˣ) (d : Fin n → Subgroup.zpowers ω) :
    ((torusHom n F ω d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun i => (((d i : Subgroup.zpowers ω) : Fˣ) : F)) := rfl

theorem torusHom_injective (n : ℕ) (ω : Fˣ) : Function.Injective (torusHom n F ω) := by
  intro d d' h
  have h1 := diagGL_injective n F h
  funext i
  exact Subtype.ext (congrFun h1 i)

theorem exists_torus [Finite F] {n p : ℕ} (hn : 3 ≤ n) (hp : p.Prime) {ω : Fˣ}
    (hω : orderOf ω = p) :
    ∃ (E : Subgroup (GL (Fin n) F)) (t : GL (Fin n) F) (k : ℕ),
      Nat.card E = p ^ k ∧ n - 2 ≤ k ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ p = 1) ∧
      (∀ a ∈ E, a * t = t * a) ∧ t ^ 2 = 1 ∧ t ∉ Subgroup.center (GL (Fin n) F) ∧
      (∀ a ∈ E, (a : Matrix (Fin n) (Fin n) F).det = 1) ∧
      (t : Matrix (Fin n) (Fin n) F).det = 1 ∧
      ∀ q : ℕ, q ≠ 0 → ω ^ (q + 1) = 1 → (-1 : F) ^ q = -1 →
        (∀ a ∈ E, ((a : Matrix (Fin n) (Fin n) F).map (· ^ q))ᵀ *
            (a : Matrix (Fin n) (Fin n) F) = 1) ∧
        ((t : Matrix (Fin n) (Fin n) F).map (· ^ q))ᵀ * (t : Matrix (Fin n) (Fin n) F) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set i2 : Fin n := ⟨2, by omega⟩ with hi2
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have h20 : i2 ≠ i0 := by simp [hi0, hi2, Fin.ext_iff]
  have h21 : i2 ≠ i1 := by simp [hi1, hi2, Fin.ext_iff]
  set ν := constraint n i0 i1 ω with hν
  let t : GL (Fin n) F := ⟨tMat i0 i1 i2, tMat i0 i1 i2, tMat_mul_self h20 h21,
    tMat_mul_self h20 h21⟩
  have htcoe : (t : Matrix (Fin n) (Fin n) F) = tMat i0 i1 i2 := rfl
  set E : Subgroup (GL (Fin n) F) := ν.ker.map (torusHom n F ω) with hE
  have hZ : Nat.card (Subgroup.zpowers ω) = p := by rw [Nat.card_zpowers, hω]
  have hxp : ∀ x : Fin n → Subgroup.zpowers ω, x ^ p = 1 := fun x => by
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    rw [← hZ]
    exact pow_card_eq_one'
  have hEp : ∀ a ∈ E, a ^ p = 1 := by
    rintro a ⟨x, -, rfl⟩
    rw [← map_pow, hxp x, map_one]
  have hpg : IsPGroup p E := fun a => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hEp a a.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  have hcardE : Nat.card E = Nat.card ν.ker :=
    Subgroup.card_map_of_injective (torusHom_injective n ω)
  have hk2 : n - 2 ≤ k := by
    have h1 := pow_le_card_ker_constraint hp hω (n := n) (by omega) i0 i1
    rw [← hν, ← hcardE, hk] at h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  have hker : ∀ x ∈ ν.ker, x i0 = x i1 ∧ ∏ i, x i = 1 := by
    intro x hx
    have h := MonoidHom.mem_ker.1 hx
    have h1 : x i0 * (x i1)⁻¹ = 1 := congrArg Prod.fst h
    exact ⟨mul_inv_eq_one.1 h1, congrArg Prod.snd h⟩
  have hswap : ∀ x ∈ ν.ker, ∀ i, (((x (Equiv.swap i0 i1 i) : Subgroup.zpowers ω) : Fˣ) : F) =
      (((x i : Subgroup.zpowers ω) : Fˣ) : F) := by
    intro x hx i
    have h0 := (hker x hx).1
    by_cases hi : i = i0
    · subst hi
      rw [Equiv.swap_apply_left, ← h0]
    · by_cases hi' : i = i1
      · subst hi'
        rw [Equiv.swap_apply_right, h0]
      · rw [Equiv.swap_apply_of_ne_of_ne hi hi']
  refine ⟨E, t, k, hk, hk2, ?_, hEp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm x y]
  · rintro _ ⟨x, hx, rfl⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, torusHom_coe, htcoe]
    exact (tMat_commute h20 h21 _ (hswap x hx)).symm
  · apply Units.ext
    rw [pow_two, Units.val_mul, htcoe, tMat_mul_self h20 h21, Units.val_one]
  · intro hc
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨c, hc⟩ := hc
    have h1 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) i0 i1) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, htcoe, tMat_apply_01 h20 h01,
      Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h01] at h1
    exact zero_ne_one h1
  · rintro _ ⟨x, hx, rfl⟩
    rw [torusHom_coe, Matrix.det_diagonal]
    have h2 := (hker x hx).2
    let ψ : Subgroup.zpowers ω →* F := (Units.coeHom F).comp (Subgroup.zpowers ω).subtype
    have h3 : ∏ i, ψ (x i) = 1 := by rw [← map_prod ψ x Finset.univ, h2, map_one]
    exact h3
  · rw [htcoe]
    exact tMat_det h01
  · intro q hq hωq hneg
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [torusHom_coe]
      refine diagonal_unitary _ q hq fun i => ?_
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (x i).2
      have h1 : (((x i : Subgroup.zpowers ω) : Fˣ)) ^ (q + 1) = 1 := by
        rw [← hm, ← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
          _root_.zpow_natCast, hωq, _root_.one_zpow]
      have h2 := congrArg (fun u : Fˣ => (u : F)) h1
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at h2
      rw [← pow_succ]
      exact h2
    · rw [htcoe]
      exact tMat_unitary h20 h21 q hq hneg

end Torus

end CFSG.LocalAnalysis.GLTheoremA.YS04G
