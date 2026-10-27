module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Congr
public import Mathlib.RingTheory.SimpleRing.Matrix
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.Setup.Offender

open TensorProduct Module

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]

@[expose] noncomputable def factorEnd (i : ι) (f : Module.End F (V i)) :
    Module.End F (⨂[F] j, V j) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : Module.End F (V j))) i f)

theorem factorEnd_tprod (i : ι) (f : Module.End F (V i)) (m : ∀ j, V j) :
    factorEnd i f (PiTensorProduct.tprod F m) =
      PiTensorProduct.tprod F (Function.update m i (f (m i))) := by
  unfold factorEnd
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem factorEnd_one (i : ι) : factorEnd (F := F) (V := V) i 1 = 1 := by
  have : Function.update (fun j => (LinearMap.id : Module.End F (V j))) i 1 =
      fun j => (LinearMap.id : Module.End F (V j)) := by
    ext j x
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [factorEnd, this]
  exact PiTensorProduct.map_id

theorem factorEnd_mul (i : ι) (f g : Module.End F (V i)) :
    factorEnd i (f * g) = factorEnd i f * factorEnd i g := by
  unfold factorEnd
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h, Function.update_of_ne h]
    rfl

theorem factorEnd_add (i : ι) (f g : Module.End F (V i)) :
    factorEnd i (f + g) = factorEnd i f + factorEnd i g := by
  unfold factorEnd
  exact PiTensorProduct.map_update_add _ _ _ _

theorem factorEnd_smul (i : ι) (c : F) (f : Module.End F (V i)) :
    factorEnd i (c • f) = c • factorEnd i f := by
  unfold factorEnd
  exact PiTensorProduct.map_update_smul _ _ _ _

theorem factorEnd_zero (i : ι) : factorEnd (F := F) (V := V) i 0 = 0 := by
  have := factorEnd_smul (F := F) (V := V) i 0 0
  simpa using this

@[expose] noncomputable def factorAlgHom (i : ι) :
    Module.End F (V i) →ₐ[F] Module.End F (⨂[F] j, V j) where
  toFun := factorEnd i
  map_one' := factorEnd_one i
  map_mul' := factorEnd_mul i
  map_zero' := factorEnd_zero i
  map_add' := factorEnd_add i
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    show factorEnd i (c • 1) = c • 1
    rw [factorEnd_smul, factorEnd_one]

theorem factorAlgHom_apply (i : ι) (f : Module.End F (V i)) :
    factorAlgHom (F := F) (V := V) i f = factorEnd i f := rfl

noncomputable abbrev factorAlg (i : ι) : Subalgebra F (Module.End F (⨂[F] j, V j)) :=
  (factorAlgHom (F := F) (V := V) i).range

theorem isSimpleRing_end {U : Type*} [AddCommGroup U] [Module F U] [Module.Finite F U]
    [Nontrivial U] : IsSimpleRing (Module.End F U) := by
  classical
  let b := Module.finBasis F U
  have : Nonempty (Fin (finrank F U)) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact IsSimpleRing.of_ringEquiv (LinearMap.toMatrixAlgEquiv b).symm.toRingEquiv inferInstance

omit [DecidableEq ι] in
theorem tprod_ne_zero_of_ne_zero [Fintype ι] {m : ∀ i, V i} (hm : ∀ i, m i ≠ 0) :
    PiTensorProduct.tprod F m ≠ 0 := by
  classical
  have : ∀ i, ∃ φ : Module.Dual F (V i), φ (m i) ≠ 0 := fun i => by
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero F (hm i)
    exact ⟨φ, hφ⟩
  choose φ hφ using this
  intro h
  have h1 := congrArg (PiTensorProduct.dualDistrib (R := F) (M := V) (PiTensorProduct.tprod F φ)) h
  rw [PiTensorProduct.dualDistrib_apply, map_zero] at h1
  exact (Finset.prod_ne_zero_iff.2 fun i _ => hφ i) h1

theorem factorAlgHom_injective [Fintype ι] [∀ i, Nontrivial (V i)] [∀ i, Module.Finite F (V i)]
    (i : ι) : Function.Injective (factorAlgHom (F := F) (V := V) i) := by
  classical
  have : IsSimpleRing (Module.End F (V i)) := isSimpleRing_end
  have : Nontrivial (⨂[F] j, V j) := by
    choose e he using fun j => exists_ne (0 : V j)
    exact ⟨⟨_, _, (tprod_ne_zero_of_ne_zero he)⟩⟩
  exact RingHom.injective (factorAlgHom (F := F) (V := V) i).toRingHom

section Constant

variable {U : Type*} [AddCommGroup U] [Module F U] {s : ℕ}

theorem reindex_factorEnd (π : Equiv.Perm (Fin s)) (i : Fin s) (g : Module.End F U)
    (x : ⨂[F] _ : Fin s, U) :
    PiTensorProduct.reindex F (fun _ : Fin s => U) π (factorEnd i g x) =
      factorEnd (π i) g (PiTensorProduct.reindex F (fun _ : Fin s => U) π x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul]
    rw [factorEnd_tprod, PiTensorProduct.reindex_tprod, PiTensorProduct.reindex_tprod,
      factorEnd_tprod]
    congr 2
    funext j
    by_cases h : j = π i
    · subst h; simp; rw [Equiv.symm_apply_apply]
    · have : π.symm j ≠ i := fun h' => h (by rw [← h']; simp)
      simp [Function.update_of_ne h, Function.update_of_ne this]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem congr_eq_map (g : Fin s → (U ≃ₗ[F] U)) (x : ⨂[F] _ : Fin s, U) :
    PiTensorProduct.congr g x =
      PiTensorProduct.map (fun i => ((g i : U ≃ₗ[F] U) : Module.End F U)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul]
    rw [PiTensorProduct.congr_tprod, PiTensorProduct.map_tprod]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem congr_factorEnd (g : Fin s → (U ≃ₗ[F] U)) (j : Fin s) (f : Module.End F U)
    (x : ⨂[F] _ : Fin s, U) :
    PiTensorProduct.congr g (factorEnd j f x) =
      factorEnd j (((g j : U ≃ₗ[F] U) : Module.End F U) * f *
        (((g j).symm : U ≃ₗ[F] U) : Module.End F U)) (PiTensorProduct.congr g x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul]
    rw [factorEnd_tprod, PiTensorProduct.congr_tprod, PiTensorProduct.congr_tprod,
      factorEnd_tprod]
    congr 2
    funext i
    by_cases h : i = j
    · subst h; simp
    · simp [Function.update_of_ne h]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem map_indicator_insert (f : Fin s → Module.End F U) (j : Fin s)
    (J : Finset (Fin s)) (hj : j ∉ J) :
    PiTensorProduct.map (fun i => if i ∈ insert j J then f i else (1 : Module.End F U)) =
      factorEnd j (f j) * PiTensorProduct.map (fun i => if i ∈ J then f i else 1) := by
  have hfun : (fun i => if i ∈ insert j J then f i else (1 : Module.End F U)) =
      fun i => (Function.update (fun _ => (1 : Module.End F U)) j (f j)) i *
        (if i ∈ J then f i else 1) := by
    funext i
    by_cases hij : i = j
    · subst hij; simp [hj]
    · simp [hij]
  have e : PiTensorProduct.map (Function.update (fun _ : Fin s => (1 : Module.End F U)) j (f j)) =
      factorEnd j (f j) := rfl
  rw [hfun, PiTensorProduct.map_mul, e]

theorem commute_map_of_commute_factorEnd (h : Module.End F (⨂[F] _ : Fin s, U))
    (hh : ∀ j f, h * factorEnd j f = factorEnd j f * h) (f : Fin s → Module.End F U) :
    h * PiTensorProduct.map f = PiTensorProduct.map f * h := by
  classical
  have key : ∀ J : Finset (Fin s), h * PiTensorProduct.map (fun i => if i ∈ J then f i else 1) =
      PiTensorProduct.map (fun i => if i ∈ J then f i else 1) * h := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, ite_false]
      have : PiTensorProduct.map (fun _ : Fin s => (1 : Module.End F U)) = (1 : Module.End F _) :=
        PiTensorProduct.map_one
      rw [this, mul_one, one_mul]
    | insert j J hj ih =>
      rw [map_indicator_insert f j J hj, ← mul_assoc, hh, mul_assoc, ih, mul_assoc]
  have := key Finset.univ
  simpa using this

theorem exists_smul_one_of_commute_factorEnd [Nontrivial U]
    (h : Module.End F (⨂[F] _ : Fin s, U)) (hh : ∀ j f, h * factorEnd j f = factorEnd j f * h) :
    ∃ c : F, h = c • 1 := by
  classical
  obtain ⟨e, he⟩ := exists_ne (0 : U)
  obtain ⟨φ₀, hφ₀⟩ := Module.Projective.exists_dual_ne_zero F he
  obtain ⟨φ, hφe⟩ : ∃ φ : Module.Dual F U, φ e = 1 :=
    ⟨(φ₀ e)⁻¹ • φ₀, by simp [hφ₀]⟩
  let r : U → Module.End F U := fun m => LinearMap.smulRight φ m
  have hr : ∀ m, r m e = m := fun m => by simp [r, hφe]
  have hmap := commute_map_of_commute_factorEnd h hh
  let t₀ : ⨂[F] _ : Fin s, U := PiTensorProduct.tprod F (fun _ => e)
  let Q : Module.End F (⨂[F] _ : Fin s, U) := PiTensorProduct.map (fun _ => r e)
  have hQrange : ∀ x, ∃ c : F, Q x = c • t₀ := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod a m =>
      refine ⟨a * ∏ i, φ (m i), ?_⟩
      simp only [map_smul, Q, PiTensorProduct.map_tprod]
      have : (fun i => r e (m i)) = fun i => φ (m i) • e := by funext i; simp [r]
      rw [this, MultilinearMap.map_smul_univ, smul_smul]
    | add x y hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, by rw [map_add, hc, hd, add_smul]⟩
  have hfixj : ∀ j, factorEnd j (r e) (h t₀) = h t₀ := by
    intro j
    have h1 : factorEnd j (r e) t₀ = t₀ := by
      simp [t₀, factorEnd_tprod, hr]
    have := congrArg (fun T => T t₀) (hh j (r e))
    simp only [Module.End.mul_apply] at this
    rw [← this, h1]
  have hQfix : Q (h t₀) = h t₀ := by
    have key : ∀ J : Finset (Fin s),
        PiTensorProduct.map (fun i => if i ∈ J then r e else 1) (h t₀) = h t₀ := by
      intro J
      induction J using Finset.induction_on with
      | empty =>
        simp only [Finset.notMem_empty, ite_false]
        have : PiTensorProduct.map (fun _ : Fin s => (1 : Module.End F U)) =
            (1 : Module.End F _) := PiTensorProduct.map_one
        rw [this]; rfl
      | insert j J hj ih =>
        rw [map_indicator_insert (fun _ => r e) j J hj, Module.End.mul_apply, ih, hfixj]
    have := key Finset.univ
    simpa [Q] using this
  obtain ⟨c, hc⟩ := hQrange (h t₀)
  have hct : h t₀ = c • t₀ := by rw [← hQfix, hc]
  have hpure : ∀ m : Fin s → U, h (PiTensorProduct.tprod F m) = c • PiTensorProduct.tprod F m := by
    intro m
    have h1 : PiTensorProduct.tprod F m =
        PiTensorProduct.map (fun j => r (m j)) t₀ := by
      simp [t₀, PiTensorProduct.map_tprod, hr]
    rw [h1]
    have := congrArg (fun T => T t₀) (hmap (fun j => r (m j)))
    simp only [Module.End.mul_apply] at this
    rw [this, hct, map_smul]
  refine ⟨c, ?_⟩
  refine LinearMap.ext fun x => ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a m =>
    rw [map_smul, hpure, smul_comm]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add]

end Constant

end CFSG.QuasithinUnique.Setup.Offender
