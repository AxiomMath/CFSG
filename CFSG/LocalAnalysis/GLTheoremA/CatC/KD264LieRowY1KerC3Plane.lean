module

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

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3.Plane

open Matrix

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

structure SympPair (B : LinearMap.BilinForm K V) (P : Module.End K V) where
  e : V
  f : V
  he : P e = e
  hf : P f = f
  hef : B e f = 1
  coord : ∀ w, P w = w → w = B w f • e - B w e • f

variable {B : LinearMap.BilinForm K V} {P : Module.End K V}

theorem bilin_antisymm (halt : ∀ v : V, B v v = 0) (v w : V) : B v w = -B w v := by
  have h1 := halt (v + w)
  simp only [map_add, LinearMap.add_apply, halt, add_zero, zero_add] at h1
  linear_combination h1

theorem P_one_sub (hP : P * P = P) (v : V) : P (v - P v) = 0 := by
  have := congrArg (fun g : Module.End K V => g v) hP
  simp only [Module.End.mul_apply] at this
  rw [map_sub, this, sub_self]

theorem orth_left (hP : P * P = P) (hPa : ∀ u v, B (P u) v = B u (P v)) (v w : V)
    (hw : P w = w) : B (v - P v) w = 0 := by
  rw [← hw, ← hPa, P_one_sub hP, map_zero, LinearMap.zero_apply]

theorem orth_right (hP : P * P = P) (hPa : ∀ u v, B (P u) v = B u (P v)) (v w : V)
    (hw : P w = w) : B w (v - P v) = 0 := by
  rw [← hw, hPa, P_one_sub hP, map_zero]

section Basic

variable (S : SympPair B P)

theorem B_fe (halt : ∀ v : V, B v v = 0) : B S.f S.e = -1 := by
  have := bilin_antisymm halt S.e S.f
  rw [S.hef] at this
  linear_combination this

theorem B_pair (halt : ∀ v : V, B v v = 0) (x y z w : K) :
    B (x • S.e + y • S.f) (z • S.e + w • S.f) = x * w - y * z := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
    S.hef, B_fe S halt]
  ring

@[expose] def l0 : V →ₗ[K] K := (B.flip S.f).comp P

@[expose] def l1 : V →ₗ[K] K := -((B.flip S.e).comp P)

theorem l0_apply (v : V) : l0 S v = B (P v) S.f := rfl

theorem l1_apply (v : V) : l1 S v = -B (P v) S.e := by
  simp [l1]

theorem l0_e (halt : ∀ v : V, B v v = 0) : l0 S S.e = 1 := by
  rw [l0_apply, S.he, S.hef]

theorem l1_e (halt : ∀ v : V, B v v = 0) : l1 S S.e = 0 := by
  rw [l1_apply, S.he, halt, neg_zero]

theorem l0_f (halt : ∀ v : V, B v v = 0) : l0 S S.f = 0 := by
  rw [l0_apply, S.hf, halt]

theorem l1_f (halt : ∀ v : V, B v v = 0) : l1 S S.f = 1 := by
  rw [l1_apply, S.hf, neg_eq_iff_eq_neg, ← B_fe S halt]

theorem coord_P (hP : P * P = P) (v : V) :
    P v = (l0 S v) • S.e + (l1 S v) • S.f := by
  have hPv : P (P v) = P v := by
    have := congrArg (fun g : Module.End K V => g v) hP
    simpa [Module.End.mul_apply] using this
  rw [S.coord (P v) hPv, l0_apply, l1_apply, sub_eq_add_neg, neg_smul]

theorem coeffs_eq (halt : ∀ v : V, B v v = 0) (x y : K) :
    l0 S (x • S.e + y • S.f) = x ∧ l1 S (x • S.e + y • S.f) = y := by
  constructor
  · simp only [map_add, map_smul, l0_e S halt, l0_f S halt, smul_eq_mul, mul_one, mul_zero,
      add_zero]
  · simp only [map_add, map_smul, l1_e S halt, l1_f S halt, smul_eq_mul, mul_one, mul_zero,
      zero_add]

theorem exists_sympPair [FiniteDimensional K V] (halt : ∀ v : V, B v v = 0) (hP : P * P = P)
    (hdim : Module.finrank K (LinearMap.range P) = 2)
    (hnd : ∀ v ∈ LinearMap.range P, (∀ w ∈ LinearMap.range P, B v w = 0) → v = 0) :
    Nonempty (SympPair B P) := by
  have hrange_fix : ∀ w ∈ LinearMap.range P, P w = w := by
    rintro w ⟨x, rfl⟩
    have := congrArg (fun g : Module.End K V => g x) hP
    simpa [Module.End.mul_apply] using this
  have hne : LinearMap.range P ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    exact absurd hdim (by norm_num)
  obtain ⟨e, he_mem, he_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hf0 : ∃ f ∈ LinearMap.range P, B e f ≠ 0 := by
    by_contra h
    push Not at h
    exact he_ne (hnd e he_mem (fun w hw => h w hw))
  obtain ⟨f₀, hf₀_mem, hf₀⟩ := hf0
  have hf_mem : (B e f₀)⁻¹ • f₀ ∈ LinearMap.range P := Submodule.smul_mem _ _ hf₀_mem
  have hef : B e ((B e f₀)⁻¹ • f₀) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hf₀]
  set f := (B e f₀)⁻¹ • f₀ with hfdef
  have hfe : B f e = -1 := by
    have := bilin_antisymm halt e f
    rw [hef] at this
    linear_combination this
  have hli : LinearIndependent K ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun w => B w f) hst
    have h2 := congrArg (fun w => B e w) hst
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
      hef, hfe, map_zero, LinearMap.zero_apply] at h1 h2
    constructor
    · linear_combination h1
    · linear_combination h2
  have hspan : Submodule.span K (Set.range ![e, f]) = LinearMap.range P := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact he_mem
      · exact hf_mem
    · rw [finrank_span_eq_card hli, hdim]
      simp
  refine ⟨⟨e, f, hrange_fix e he_mem, hrange_fix f hf_mem, hef, ?_⟩⟩
  intro w hw
  have hwmem : w ∈ Submodule.span K (Set.range ![e, f]) := by
    rw [hspan]
    exact LinearMap.mem_range.2 ⟨w, hw⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hwmem
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hc
  rw [← hc]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
    hef, hfe]
  module

end Basic

section Phi

variable (S : SympPair B P)

@[expose] def Phi (A : Matrix (Fin 2) (Fin 2) K) : Module.End K V :=
  (1 - P) + LinearMap.smulRight (A 0 0 • l0 S + A 0 1 • l1 S) S.e +
    LinearMap.smulRight (A 1 0 • l0 S + A 1 1 • l1 S) S.f

theorem Phi_apply (A : Matrix (Fin 2) (Fin 2) K) (v : V) :
    Phi S A v = (v - P v) + (A 0 0 * l0 S v + A 0 1 * l1 S v) • S.e +
      (A 1 0 * l0 S v + A 1 1 * l1 S v) • S.f := by
  simp only [Phi, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul]

theorem P_Phi (hP : P * P = P) (A : Matrix (Fin 2) (Fin 2) K) (v : V) :
    P (Phi S A v) = (A 0 0 * l0 S v + A 0 1 * l1 S v) • S.e +
      (A 1 0 * l0 S v + A 1 1 * l1 S v) • S.f := by
  rw [Phi_apply, map_add, map_add, map_smul, map_smul, P_one_sub hP, S.he, S.hf, zero_add]

theorem Phi_part (hP : P * P = P) (A : Matrix (Fin 2) (Fin 2) K) (v : V) :
    Phi S A v - P (Phi S A v) = v - P v := by
  rw [P_Phi S hP A v, Phi_apply]
  abel

theorem l0_Phi (halt : ∀ v : V, B v v = 0) (hP : P * P = P) (A : Matrix (Fin 2) (Fin 2) K)
    (v : V) : l0 S (Phi S A v) = A 0 0 * l0 S v + A 0 1 * l1 S v := by
  rw [l0_apply, P_Phi S hP A v]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
    S.hef, S.hf, mul_one, mul_zero, add_zero, zero_add]

theorem l1_Phi (halt : ∀ v : V, B v v = 0) (hP : P * P = P) (A : Matrix (Fin 2) (Fin 2) K)
    (v : V) : l1 S (Phi S A v) = A 1 0 * l0 S v + A 1 1 * l1 S v := by
  rw [l1_apply, P_Phi S hP A v]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
    B_fe S halt, S.hef, S.he, mul_one, mul_zero, add_zero, zero_add, neg_mul, one_mul]
  ring

theorem Phi_mul (halt : ∀ v : V, B v v = 0) (hP : P * P = P) (A A' : Matrix (Fin 2) (Fin 2) K)
    (v : V) : Phi S A (Phi S A' v) = Phi S (A * A') v := by
  rw [Phi_apply S A (Phi S A' v), Phi_part S hP A' v, l0_Phi S halt hP A' v,
    l1_Phi S halt hP A' v, Phi_apply S (A * A') v]
  have hd0 : A 0 0 * (A' 0 0 * l0 S v + A' 0 1 * l1 S v) +
      A 0 1 * (A' 1 0 * l0 S v + A' 1 1 * l1 S v) =
      (A * A') 0 0 * l0 S v + (A * A') 0 1 * l1 S v := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hd1 : A 1 0 * (A' 0 0 * l0 S v + A' 0 1 * l1 S v) +
      A 1 1 * (A' 1 0 * l0 S v + A' 1 1 * l1 S v) =
      (A * A') 1 0 * l0 S v + (A * A') 1 1 * l1 S v := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hd0, hd1]

theorem Phi_one (hP : P * P = P) : Phi S 1 = 1 := by
  refine LinearMap.ext fun v => ?_
  rw [Phi_apply, Module.End.one_apply]
  have h01 : (1 : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by simp
  have h10 : (1 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by simp
  have h11 : (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simp
  have h22 : (1 : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by simp
  rw [h01, h10, h11, h22, zero_mul, zero_mul, one_mul, one_mul, add_zero, zero_add]
  rw [add_assoc, ← coord_P S hP v, sub_add_cancel]

theorem Phi_e (halt : ∀ v : V, B v v = 0) (hP : P * P = P) (A : Matrix (Fin 2) (Fin 2) K) :
    Phi S A S.e = A 0 0 • S.e + A 1 0 • S.f := by
  rw [Phi_apply, S.he, sub_self, zero_add, l0_e S halt, l1_e S halt]
  simp

theorem Phi_f (halt : ∀ v : V, B v v = 0) (hP : P * P = P) (A : Matrix (Fin 2) (Fin 2) K) :
    Phi S A S.f = A 0 1 • S.e + A 1 1 • S.f := by
  rw [Phi_apply, S.hf, sub_self, zero_add, l0_f S halt, l1_f S halt]
  simp

theorem Phi_inj (halt : ∀ v : V, B v v = 0) (hP : P * P = P) (A A' : Matrix (Fin 2) (Fin 2) K)
    (h : Phi S A = Phi S A') : A = A' := by
  have he : Phi S A S.e = Phi S A' S.e := by rw [h]
  have hf : Phi S A S.f = Phi S A' S.f := by rw [h]
  rw [Phi_e S halt hP, Phi_e S halt hP] at he
  rw [Phi_f S halt hP, Phi_f S halt hP] at hf
  have h1 := congrArg (l0 S) he
  have h2 := congrArg (l1 S) he
  have h3 := congrArg (l0 S) hf
  have h4 := congrArg (l1 S) hf
  rw [(coeffs_eq S halt _ _).1, (coeffs_eq S halt _ _).1] at h1
  rw [(coeffs_eq S halt _ _).2, (coeffs_eq S halt _ _).2] at h2
  rw [(coeffs_eq S halt _ _).1, (coeffs_eq S halt _ _).1] at h3
  rw [(coeffs_eq S halt _ _).2, (coeffs_eq S halt _ _).2] at h4
  ext i j
  fin_cases i <;> fin_cases j
  · exact h1
  · exact h3
  · exact h2
  · exact h4

theorem Phi_apply' (A : Matrix (Fin 2) (Fin 2) K) (v : V) :
    Phi S A v = (v - P v) + ((A 0 0 * l0 S v + A 0 1 * l1 S v) • S.e +
      (A 1 0 * l0 S v + A 1 1 * l1 S v) • S.f) := by
  rw [Phi_apply, add_assoc]

theorem B_split (hP : P * P = P) (hPa : ∀ u v, B (P u) v = B u (P v)) (u v X Y : V)
    (hX : P X = X) (hY : P Y = Y) :
    B ((u - P u) + X) ((v - P v) + Y) = B (u - P u) (v - P v) + B X Y := by
  simp only [map_add, LinearMap.add_apply]
  rw [orth_left hP hPa u Y hY, orth_right hP hPa v X hX]
  ring_nf

theorem Phi_bilin (halt : ∀ v : V, B v v = 0) (hP : P * P = P)
    (hPa : ∀ u v, B (P u) v = B u (P v)) (A : Matrix (Fin 2) (Fin 2) K) (hdet : A.det = 1)
    (u v : V) : B (Phi S A u) (Phi S A v) = B u v := by
  have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    linear_combination hdet
  have hPX : ∀ x y : K, P (x • S.e + y • S.f) = x • S.e + y • S.f := by
    intro x y
    rw [map_add, map_smul, map_smul, S.he, S.hf]
  have hPu : B u v = B (u - P u) (v - P v) + B (P u) (P v) := by
    have e1 : u = (u - P u) + P u := by abel
    have e2 : v = (v - P v) + P v := by abel
    have hPPu : P (P u) = P u := by
      have := congrArg (fun g : Module.End K V => g u) hP
      simpa [Module.End.mul_apply] using this
    have hPPv : P (P v) = P v := by
      have := congrArg (fun g : Module.End K V => g v) hP
      simpa [Module.End.mul_apply] using this
    conv_lhs => rw [e1, e2]
    rw [B_split hP hPa _ _ _ _ (hPPu) (hPPv)]
  have hPP : B (P u) (P v) = l0 S u * l1 S v - l1 S u * l0 S v := by
    rw [coord_P S hP u, coord_P S hP v, B_pair S halt]
  rw [Phi_apply' S A u, Phi_apply' S A v, B_split hP hPa _ _ _ _
    (hPX _ _) (hPX _ _), B_pair S halt, hPu, hPP]
  linear_combination (l0 S u * l1 S v - l1 S u * l0 S v) * hdet'

theorem Phi_conj (halt : ∀ v : V, B v v = 0) (hP : P * P = P)
    (x : Module.End K V) (hxP : x * P = P * x) (hxB : ∀ u v, B (x u) (x v) = B u v) :
    ∃ M : Matrix (Fin 2) (Fin 2) K, M.det = 1 ∧
      ∀ A : Matrix (Fin 2) (Fin 2) K, x * Phi S A = Phi S (M * A * M⁻¹) * x := by
  have hxPw : ∀ w, P (x w) = x (P w) := fun w => by
    have := congrArg (fun g : Module.End K V => g w) hxP
    simpa [Module.End.mul_apply] using this.symm
  have hxPe : P (x S.e) = x S.e := by rw [hxPw, S.he]
  have hxPf : P (x S.f) = x S.f := by rw [hxPw, S.hf]
  obtain ⟨M, hM00, hM10, hM01, hM11⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K,
      M 0 0 = l0 S (x S.e) ∧ M 1 0 = l1 S (x S.e) ∧ M 0 1 = l0 S (x S.f) ∧
        M 1 1 = l1 S (x S.f) :=
    ⟨!![l0 S (x S.e), l0 S (x S.f); l1 S (x S.e), l1 S (x S.f)], rfl, rfl, rfl, rfl⟩
  have hxe : x S.e = M 0 0 • S.e + M 1 0 • S.f := by
    rw [hM00, hM10, ← coord_P S hP (x S.e), hxPe]
  have hxf : x S.f = M 0 1 • S.e + M 1 1 • S.f := by
    rw [hM01, hM11, ← coord_P S hP (x S.f), hxPf]
  have hdet : M.det = 1 := by
    have h := hxB S.e S.f
    rw [hxe, hxf, B_pair S halt, S.hef] at h
    rw [Matrix.det_fin_two]
    linear_combination h
  have hinv1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (by rw [hdet]; exact isUnit_one)
  refine ⟨M, hdet, fun A => ?_⟩
  obtain ⟨A', hA'⟩ : ∃ A' : Matrix (Fin 2) (Fin 2) K, A' = M * A * M⁻¹ := ⟨_, rfl⟩
  rw [← hA']
  have hA'M : A' * M = M * A := by
    rw [hA', Matrix.mul_assoc, hinv1, Matrix.mul_one]
  have hPxv : ∀ v : V, P (x v) = (M 0 0 * l0 S v + M 0 1 * l1 S v) • S.e +
      (M 1 0 * l0 S v + M 1 1 * l1 S v) • S.f := by
    intro v
    rw [hxPw, coord_P S hP v, map_add, map_smul, map_smul, hxe, hxf]
    module
  have hl0x : ∀ v : V, l0 S (x v) = M 0 0 * l0 S v + M 0 1 * l1 S v := by
    intro v
    rw [l0_apply, hPxv v]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.hef, halt, S.hf, mul_one, mul_zero, add_zero, zero_add]
  have hl1x : ∀ v : V, l1 S (x v) = M 1 0 * l0 S v + M 1 1 * l1 S v := by
    intro v
    rw [l1_apply, hPxv v]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      B_fe S halt, halt, mul_one, mul_zero, add_zero, zero_add]
    ring
  have h00 := congrFun (congrFun hA'M 0) 0
  have h01 := congrFun (congrFun hA'M 0) 1
  have h10 := congrFun (congrFun hA'M 1) 0
  have h11 := congrFun (congrFun hA'M 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  refine LinearMap.ext fun v => ?_
  have hc0 : (A 0 0 * l0 S v + A 0 1 * l1 S v) * M 0 0 +
      (A 1 0 * l0 S v + A 1 1 * l1 S v) * M 0 1 =
      A' 0 0 * (M 0 0 * l0 S v + M 0 1 * l1 S v) + A' 0 1 * (M 1 0 * l0 S v + M 1 1 * l1 S v) := by
    linear_combination (-(l0 S v)) * h00 + (-(l1 S v)) * h01
  have hc1 : (A 0 0 * l0 S v + A 0 1 * l1 S v) * M 1 0 +
      (A 1 0 * l0 S v + A 1 1 * l1 S v) * M 1 1 =
      A' 1 0 * (M 0 0 * l0 S v + M 0 1 * l1 S v) + A' 1 1 * (M 1 0 * l0 S v + M 1 1 * l1 S v) := by
    linear_combination (-(l0 S v)) * h10 + (-(l1 S v)) * h11
  simp only [Module.End.mul_apply, Phi_apply' S A v, map_add, map_smul, map_sub]
  rw [← hxPw v, hxe, hxf, Phi_apply' S A' (x v), hl0x v, hl1x v]
  linear_combination (norm := module) hc0 • S.e + hc1 • S.f

theorem Phi_comm (S : SympPair B P) (hP : P * P = P) (ρf : Module.End K V)
    (hcommP : ρf * P = P * ρf) (hfix : ∀ w ∈ LinearMap.range P, ρf w = w)
    (A : Matrix (Fin 2) (Fin 2) K) : Phi S A * ρf = ρf * Phi S A := by
  refine LinearMap.ext fun v => ?_
  have hPρ : ∀ x, P (ρf x) = ρf (P x) := fun x => by
    have := congrArg (fun g : Module.End K V => g x) hcommP
    simpa [Module.End.mul_apply] using this.symm
  have hPv : ∀ x, ρf (P x) = P x := fun x => hfix _ (LinearMap.mem_range_self _ _)
  have he : ρf S.e = S.e := hfix _ (LinearMap.mem_range.2 ⟨S.e, S.he⟩)
  have hf : ρf S.f = S.f := hfix _ (LinearMap.mem_range.2 ⟨S.f, S.hf⟩)
  have hl0 : l0 S (ρf v) = l0 S v := by
    rw [l0_apply, l0_apply, hPρ, hPv]
  have hl1 : l1 S (ρf v) = l1 S v := by
    rw [l1_apply, l1_apply, hPρ, hPv]
  simp only [Module.End.mul_apply]
  rw [Phi_apply' S A (ρf v), hPρ, hPv, hl0, hl1, Phi_apply' S A v, map_add, map_sub,
    map_add, map_smul, map_smul, he, hf, hPv]

end Phi

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3.Plane

end
