module

public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial Polynomial
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

theorem eq_zero_of_forall_sum_eq_zero {L : Type} [Field L] {ι' κ : Type*} [Fintype ι']
    {f : ι' → L} (hf : Function.Injective f) (s : Finset κ) (e : κ → ℕ) (he : Set.InjOn e s)
    {D : ℕ} (hD : ∀ x ∈ s, e x ≤ D) (hcard : D < Fintype.card ι') (m : κ → L)
    (h : ∀ i, ∑ x ∈ s, f i ^ e x * m x = 0) {x : κ} (hx : x ∈ s) : m x = 0 := by
  classical
  set P : L[X] := ∑ y ∈ s, C (m y) * X ^ e y with hP
  have hdeg : P.natDegree ≤ D :=
    natDegree_sum_le_of_forall_le _ _ fun y hy => (natDegree_C_mul_X_pow_le _ _).trans (hD y hy)
  have hev : ∀ i, P.eval (f i) = 0 := by
    intro i
    rw [← h i, hP, eval_finsetSum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]
  have hP0 : P = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hf hev
    (lt_of_le_of_lt hdeg hcard)
  have hc := congrArg (fun P : L[X] => P.coeff (e x)) hP0
  simp only [hP, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
  rw [Finset.sum_eq_single x (fun y hy hyx => by
    split_ifs with hxy
    · exact absurd (he hy hx hxy.symm) hyx
    · rw [mul_zero]) (fun h => absurd hx h)] at hc
  simpa using hc

theorem eq_zero_of_forall_sum_smul_eq_zero {L : Type} [Field L] {τ : Tag} {ι' κ : Type*}
    [Fintype ι'] {f : ι' → L} (hf : Function.Injective f) (s : Finset κ) (e : κ → ℕ)
    (he : Set.InjOn e s) {D : ℕ} (hD : ∀ x ∈ s, e x ≤ D) (hcard : D < Fintype.card ι')
    (N : κ → Module.End L (RootModule τ L))
    (h : ∀ i, ∑ x ∈ s, f i ^ e x • N x = 0) {x : κ} (hx : x ∈ s) : N x = 0 := by
  classical
  refine Finsupp.lhom_ext' fun j => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  refine eq_zero_of_forall_sum_eq_zero hf s e he hD hcard
    (fun y => N y (Finsupp.single j 1) a) (fun i => ?_) hx
  have h1 := congrArg (fun A : Module.End L (RootModule τ L) => A (Finsupp.single j 1) a) (h i)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, LinearMap.zero_apply, Finsupp.coe_zero,
    Pi.zero_apply] at h1
  exact h1

theorem injOn_add_mul {q : ℕ} (hq : 3 ≤ q) :
    Set.InjOn (fun x : ℕ × ℕ => x.1 + q * x.2) (Finset.range 3 ×ˢ Finset.range 3 : Finset _) := by
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hab hab'
  have h1 : (a + q * b) % q = (a' + q * b') % q := by simp only at h; rw [h]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at h1
  subst h1
  have h2 : q * b = q * b' := by simp only at h; omega
  have h3 : b = b' := Nat.eq_of_mul_eq_mul_left (by omega) h2
  rw [h3]

section Poly

variable {τ : Tag} {k : Type} [Field k]

@[expose] def rootUCoeff (β : Fin τ.rank → ℤ) (a : ℕ) : Module.End k (RootModule τ k) :=
  (pinnedWeyl τ k β : Module.End k (RootModule τ k)) * xCoeff τ k (pinnedData τ β).1 a *
    (((pinnedWeyl τ k β)⁻¹ : (Module.End k (RootModule τ k))ˣ) : Module.End k (RootModule τ k))

@[expose] def rootVCoeff (β : Fin τ.rank → ℤ) (a : ℕ) : Module.End k (RootModule τ k) :=
  (pinnedWeyl τ k β : Module.End k (RootModule τ k)) * yCoeff τ k (pinnedData τ β).1 a *
    (((pinnedWeyl τ k β)⁻¹ : (Module.End k (RootModule τ k))ˣ) : Module.End k (RootModule τ k))

theorem rootUCoeff_zero (β : Fin τ.rank → ℤ) : rootUCoeff (k := k) β 0 = 1 := by
  rw [rootUCoeff, xCoeff_zero, mul_one, Units.mul_inv]

theorem rootVCoeff_zero (β : Fin τ.rank → ℤ) : rootVCoeff (k := k) β 0 = 1 := by
  rw [rootVCoeff, yCoeff_zero, mul_one, Units.mul_inv]

theorem entryDegreeBound_succ (hτ : τ ≠ .G2) : entryDegreeBound τ + 1 = 3 := by
  simp [entryDegreeBound, hτ]

theorem rootSL2_uSL_eq_sum (hτ : τ ≠ .G2) (β : Fin τ.rank → ℤ) (t : k) :
    ((rootSL2 τ k β (uSL t) : ModGL τ k) : Module.End k (RootModule τ k)) =
      ∑ a ∈ Finset.range 3, t ^ a • rootUCoeff β a := by
  rw [rootSL2_apply, simpleRootSL2_uSL, Units.val_mul, Units.val_mul, coe_xUnit,
    xOp_eq_sum_xCoeff_entryDegreeBound, entryDegreeBound_succ hτ, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rootUCoeff, mul_smul_comm, smul_mul_assoc]

theorem rootSL2_vSL_eq_sum (hτ : τ ≠ .G2) (β : Fin τ.rank → ℤ) (t : k) :
    ((rootSL2 τ k β (vSL t) : ModGL τ k) : Module.End k (RootModule τ k)) =
      ∑ a ∈ Finset.range 3, t ^ a • rootVCoeff β a := by
  rw [rootSL2_apply, simpleRootSL2_vSL, Units.val_mul, Units.val_mul, coe_yUnit,
    yOp_eq_sum_yCoeff_entryDegreeBound, entryDegreeBound_succ hτ, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rootVCoeff, mul_smul_comm, smul_mul_assoc]

theorem commutator_sum_smul {κ : Type*} (s : Finset κ) (c : κ → k)
    (A : κ → Module.End k (RootModule τ k)) (z : Module.End k (RootModule τ k)) :
    z * (∑ x ∈ s, c x • A x) - (∑ x ∈ s, c x • A x) * z = ∑ x ∈ s, c x • (z * A x - A x * z) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, smul_sub]

end Poly

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
