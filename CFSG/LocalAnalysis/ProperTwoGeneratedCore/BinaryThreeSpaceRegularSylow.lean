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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

open Matrix

abbrev Mat3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def unitri (a b c : ZMod 2) : Mat3 := !![1, a, b; 0, 1, c; 0, 0, 1]

theorem unitri_mul_inv : ∀ a b c : ZMod 2, unitri a b c * unitri a (a * c + b) c = 1 := by
  decide

theorem unitri_inv_mul : ∀ a b c : ZMod 2, unitri a (a * c + b) c * unitri a b c = 1 := by
  decide

theorem unitri_mul : ∀ a b c a' b' c' : ZMod 2,
    unitri a b c * unitri a' b' c' = unitri (a + a') (b + b' + a * c') (c + c') := by
  decide

theorem unitri_zero : unitri 0 0 0 = 1 := by decide

@[expose] def unitriGL (a b c : ZMod 2) : GL (Fin 3) (ZMod 2) :=
  ⟨unitri a b c, unitri a (a * c + b) c, unitri_mul_inv a b c, unitri_inv_mul a b c⟩

@[expose] def sylowT : Subgroup (GL (Fin 3) (ZMod 2)) where
  carrier := {g | ∃ a b c, g = unitriGL a b c}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨a + a', b + b' + a * c', c + c', Units.ext (unitri_mul a b c a' b' c')⟩
  one_mem' := ⟨0, 0, 0, Units.ext unitri_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    refine ⟨a, a * c + b, c, Units.ext ?_⟩
    change unitri a (a * c + b) c = unitri a (a * c + b) c
    rfl

@[expose] def tripleEquiv : (ZMod 2 × ZMod 2 × ZMod 2) ≃ sylowT where
  toFun s := ⟨unitriGL s.1 s.2.1 s.2.2, ⟨_, _, _, rfl⟩⟩
  invFun g := ((g : GL (Fin 3) (ZMod 2)) 0 1, (g : GL (Fin 3) (ZMod 2)) 0 2,
    (g : GL (Fin 3) (ZMod 2)) 1 2)
  left_inv s := rfl
  right_inv g := by
    obtain ⟨_, a, b, c, rfl⟩ := g
    rfl

instance : Fintype sylowT := Fintype.ofEquiv (ZMod 2 × ZMod 2 × ZMod 2) tripleEquiv

@[expose] def traceZero : Submodule (ZMod 2) Mat3 :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 3) (ZMod 2) (ZMod 2))

abbrev E31 : Mat3 := Matrix.single 2 0 1

theorem conj_mem (g : GL (Fin 3) (ZMod 2)) :
    (g : Mat3) * E31 * ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) ∈ traceZero := by
  rw [traceZero, LinearMap.mem_ker, Matrix.traceLinearMap_apply, Matrix.trace_mul_cycle,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  decide

@[expose] def conjFamily (t : sylowT) : traceZero :=
  ⟨((t : GL (Fin 3) (ZMod 2)) : Mat3) * E31 * (((t : GL (Fin 3) (ZMod 2))⁻¹ :
    GL (Fin 3) (ZMod 2)) : Mat3), conj_mem _⟩

@[expose] def lamCoeff (s : ZMod 2 × ZMod 2 × ZMod 2) : Mat3 :=
  if s = (0, 0, 0) then !![0, 1, 1; 1, 0, 1; 1, 1, 0]
  else if s = (0, 0, 1) then !![1, 0, 1; 1, 0, 1; 0, 0, 0]
  else if s = (0, 1, 0) then !![0, 1, 1; 0, 1, 1; 0, 0, 0]
  else if s = (0, 1, 1) then !![1, 0, 1; 0, 1, 1; 0, 0, 0]
  else if s = (1, 0, 0) then !![1, 1, 1; 0, 1, 0; 0, 1, 0]
  else if s = (1, 0, 1) then !![1, 0, 1; 0, 1, 0; 0, 0, 0]
  else if s = (1, 1, 0) then !![1, 1, 1; 0, 0, 0; 0, 0, 0]
  else !![1, 0, 1; 0, 0, 0; 0, 0, 0]

@[expose] def lam (s : ZMod 2 × ZMod 2 × ZMod 2) : Mat3 →ₗ[ZMod 2] ZMod 2 where
  toFun X := ∑ i, ∑ j, lamCoeff s i j * X i j
  map_add' X Y := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

@[expose] def conjMat (s : ZMod 2 × ZMod 2 × ZMod 2) : Mat3 :=
  unitri s.1 s.2.1 s.2.2 * E31 * unitri s.1 (s.1 * s.2.2 + s.2.1) s.2.2

theorem lam_conj : ∀ s s' : ZMod 2 × ZMod 2 × ZMod 2,
    lam s (conjMat s') = if s = s' then 1 else 0 := by
  decide +kernel

@[expose] def traceZeroMat (x0 x1 x2 x3 x4 x5 x6 x7 : ZMod 2) : Mat3 :=
  !![x0, x1, x2; x3, x4, x5; x6, x7, x0 + x4]

theorem sum_lam_smul_traceZeroMat : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : ZMod 2,
    ∑ s, lam s (traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7) • conjMat s =
      traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7 := by
  decide +kernel

theorem eq_traceZeroMat {X : Mat3} (hX : X ∈ traceZero) :
    X = traceZeroMat (X 0 0) (X 0 1) (X 0 2) (X 1 0) (X 1 1) (X 1 2) (X 2 0) (X 2 1) := by
  have h : X 0 0 + X 1 1 + X 2 2 = 0 := by
    have := hX
    change Matrix.trace X = 0 at this
    rwa [Matrix.trace_fin_three] at this
  have h22 : X 2 2 = X 0 0 + X 1 1 :=
    (by decide : ∀ a b c : ZMod 2, a + b + c = 0 → c = a + b) _ _ _ h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [traceZeroMat, h22]

theorem sum_lam_smul {X : Mat3} (hX : X ∈ traceZero) : ∑ s, lam s X • conjMat s = X := by
  rw [eq_traceZeroMat hX]
  exact sum_lam_smul_traceZeroMat _ _ _ _ _ _ _ _

theorem conjFamily_tripleEquiv (s : ZMod 2 × ZMod 2 × ZMod 2) :
    (conjFamily (tripleEquiv s) : Mat3) = conjMat s :=
  rfl

theorem linearIndependent_conjFamily : LinearIndependent (ZMod 2) conjFamily := by
  refine (linearIndependent_equiv tripleEquiv).mp ?_
  let Λ : traceZero →ₗ[ZMod 2] (ZMod 2 × ZMod 2 × ZMod 2 → ZMod 2) :=
    LinearMap.pi fun s => (lam s).comp traceZero.subtype
  refine LinearIndependent.of_comp Λ ?_
  have h : ⇑Λ ∘ (conjFamily ∘ ⇑tripleEquiv) = ⇑(Pi.basisFun (ZMod 2) _) := by
    funext s' s
    simp only [Λ, Function.comp_apply, LinearMap.pi_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, conjFamily_tripleEquiv, lam_conj, Pi.basisFun_apply,
      Pi.single_apply]
  rw [h]
  exact (Pi.basisFun (ZMod 2) _).linearIndependent

theorem span_conjFamily : ⊤ ≤ Submodule.span (ZMod 2) (Set.range conjFamily) := by
  rintro ⟨X, hX⟩ -
  have hsum : (⟨X, hX⟩ : traceZero) = ∑ s, lam s X • conjFamily (tripleEquiv s) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, conjFamily_tripleEquiv]
    exact (sum_lam_smul hX).symm
  rw [hsum]
  exact Submodule.sum_mem _ fun s _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨tripleEquiv s, rfl⟩)

@[expose] noncomputable def conjBasis : Module.Basis sylowT (ZMod 2) traceZero :=
  Module.Basis.mk linearIndependent_conjFamily span_conjFamily

theorem conjBasis_apply (t : sylowT) : conjBasis t = conjFamily t :=
  Module.Basis.mk_apply _ _ t

theorem trace_zero_regular_Sylow_module :
    (∃ b : Module.Basis sylowT (ZMod 2) traceZero, ∀ t, b t = conjFamily t) ∧
    (∀ t, Fintype.linearCombination (ZMod 2) conjFamily (Pi.single t 1) = conjFamily t) ∧
    Function.Bijective (Fintype.linearCombination (ZMod 2) conjFamily) ∧
    ∀ (h : sylowT) (f : sylowT → ZMod 2),
      ((Fintype.linearCombination (ZMod 2) conjFamily (fun x => f (h⁻¹ * x)) : traceZero) :
          Mat3) =
        ((h : GL (Fin 3) (ZMod 2)) : Mat3) *
          (Fintype.linearCombination (ZMod 2) conjFamily f : Mat3) *
            (((h : GL (Fin 3) (ZMod 2))⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) := by
  refine ⟨⟨conjBasis, conjBasis_apply⟩, fun t => ?_, ?_, fun h f => ?_⟩
  · rw [Fintype.linearCombination_apply_single, one_smul]
  · have heq : ⇑(Fintype.linearCombination (ZMod 2) conjFamily) = ⇑conjBasis.equivFun.symm := by
      funext f
      rw [Module.Basis.equivFun_symm_apply, Fintype.linearCombination_apply]
      simp only [conjBasis_apply]
    rw [heq]
    exact conjBasis.equivFun.symm.bijective
  · simp only [Fintype.linearCombination_apply, Submodule.coe_sum, Submodule.coe_smul]
    rw [← Equiv.sum_comp (Equiv.mulLeft h)]
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [conjFamily, Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc]

end CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
