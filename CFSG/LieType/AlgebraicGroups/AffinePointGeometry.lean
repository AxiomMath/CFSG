module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct

variable (k : Type) [Field k] [IsAlgClosed k]

theorem exists_algHom_ker_eq (A : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (m : Ideal A) [m.IsMaximal] : ∃ x : A →ₐ[k] k, RingHom.ker x = m := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (A ⧸ m) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have : Algebra.IsIntegral k (A ⧸ m) := Algebra.IsIntegral.of_finite k (A ⧸ m)
  have hbij : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hbij
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext a
  simp only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  constructor
  · intro h
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := congrArg e h
    simpa using this
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.2 h]
    simp

theorem eq_zero_of_forall_algHom (A : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [IsReduced A] (a : A) (h : ∀ x : A →ₐ[k] k, x a = 0) : a = 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hmem : a ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    obtain ⟨x, hx⟩ := exists_algHom_ker_eq k A m
    rw [← hx]
    exact h x
  rw [← Ideal.radical_eq_jacobson, Ideal.mem_radical_iff] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact IsReduced.eq_zero a ⟨n, Ideal.mem_bot.1 hn⟩

theorem evaluation_injective (A : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [IsReduced A] : Function.Injective fun (a : A) (x : A →ₐ[k] k) => x a := by
  intro a b hab
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_algHom k A _ fun x => ?_
  have := congrFun hab x
  simp only at this
  rw [map_sub, this, sub_self]

theorem exists_algHom_mem_of_isLocallyClosed (A : Type) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] {Z : Set (PrimeSpectrum A)} (hZ : IsLocallyClosed Z)
    (hne : Z.Nonempty) :
    ∃ x : A →ₐ[k] k, (⟨RingHom.ker x, RingHom.ker_isPrime _⟩ : PrimeSpectrum A) ∈ Z := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  obtain ⟨p, hpZ, hp⟩ := nonempty_inter_closedPoints hne hZ
  have : p.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).1 hp
  obtain ⟨x, hx⟩ := exists_algHom_ker_eq k A p.asIdeal
  refine ⟨x, ?_⟩
  have : (⟨RingHom.ker x, RingHom.ker_isPrime _⟩ : PrimeSpectrum A) = p := PrimeSpectrum.ext hx
  rw [this]
  exact hpZ

omit [IsAlgClosed k] in
theorem productMap_eq_sum (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    {ι : Type} (b : Module.Basis ι k B) (f : A ⊗[k] B) (x : A →ₐ[k] k) (y : B →ₐ[k] k) :
    Algebra.TensorProduct.productMap x y f =
      y (((Algebra.TensorProduct.basis A b).repr f).sum fun i c => x c • b i) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis A b).linearCombination_repr f]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    Algebra.TensorProduct.productMap_apply_tmul, map_smul, smul_eq_mul]
  simp

theorem tensor_eq_zero_of_forall_algHom (A B : Type) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [IsReduced A] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    [IsReduced B] (f : A ⊗[k] B)
    (h : ∀ (x : A →ₐ[k] k) (y : B →ₐ[k] k), Algebra.TensorProduct.productMap x y f = 0) :
    f = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace k B
  set c := (Algebra.TensorProduct.basis A b).repr f with hc
  suffices hc0 : c = 0 by
    rw [← (Algebra.TensorProduct.basis A b).repr.map_eq_zero_iff]
    exact hc0
  ext i
  refine eq_zero_of_forall_algHom k A _ fun x => ?_
  have hfx : (c.sum fun i a => x a • b i) = 0 :=
    eq_zero_of_forall_algHom k B _ fun y => by rw [← productMap_eq_sum, h]
  rw [Finsupp.sum] at hfx
  by_cases hi : i ∈ c.support
  · exact (linearIndependent_iff'.1 b.linearIndependent) c.support (fun i => x (c i)) hfx i hi
  · rw [Finsupp.notMem_support_iff.1 hi, map_zero]

theorem isReduced_tensorProduct (A B : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [IsReduced A] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by
  let E : A ⊗[k] B →ₐ[k] ((A →ₐ[k] k) × (B →ₐ[k] k) → k) :=
    AlgHom.pi fun p => Algebra.TensorProduct.productMap p.1 p.2
  have hE : Function.Injective E := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    exact tensor_eq_zero_of_forall_algHom k A B f fun x y => congrFun hf (x, y)
  exact isReduced_of_injective E hE

theorem isDomain_tensorProduct (A B : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [IsDomain A] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsDomain B] :
    IsDomain (A ⊗[k] B) := by
  classical
  let b := Module.Basis.ofVectorSpace k B
  have hspec : ∀ f g : A ⊗[k] B, f ≠ 0 → g ≠ 0 → ∃ x : A →ₐ[k] k,
      ((Algebra.TensorProduct.basis A b).repr f).sum (fun i c => x c • b i) ≠ 0 ∧
      ((Algebra.TensorProduct.basis A b).repr g).sum (fun i c => x c • b i) ≠ 0 := by
    intro f g hf hg
    obtain ⟨i, hi⟩ : ∃ i, (Algebra.TensorProduct.basis A b).repr f i ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hf
      rw [← (Algebra.TensorProduct.basis A b).repr.map_eq_zero_iff]
      ext i
      exact hall i
    obtain ⟨j, hj⟩ : ∃ j, (Algebra.TensorProduct.basis A b).repr g j ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hg
      rw [← (Algebra.TensorProduct.basis A b).repr.map_eq_zero_iff]
      ext j
      exact hall j
    obtain ⟨x, hx⟩ : ∃ x : A →ₐ[k] k, x ((Algebra.TensorProduct.basis A b).repr f i *
        (Algebra.TensorProduct.basis A b).repr g j) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact mul_ne_zero hi hj (eq_zero_of_forall_algHom k A _ hall)
    rw [map_mul] at hx
    refine ⟨x, fun h0 => ?_, fun h0 => ?_⟩
    · rw [Finsupp.sum] at h0
      exact left_ne_zero_of_mul hx ((linearIndependent_iff'.1 b.linearIndependent) _ _ h0 i
        (Finsupp.mem_support_iff.2 hi))
    · rw [Finsupp.sum] at h0
      exact right_ne_zero_of_mul hx ((linearIndependent_iff'.1 b.linearIndependent) _ _ h0 j
        (Finsupp.mem_support_iff.2 hj))
  have : Nontrivial (A ⊗[k] B) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    obtain ⟨n, hn⟩ := Ideal.exists_maximal B
    obtain ⟨x, -⟩ := exists_algHom_ker_eq k A m
    obtain ⟨y, -⟩ := exists_algHom_ker_eq k B n
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    have := congrArg (Algebra.TensorProduct.productMap x y) h
    rw [map_one, map_zero] at this
    exact one_ne_zero this
  have : NoZeroDivisors (A ⊗[k] B) := ⟨fun {f g} hfg => by
    by_contra hne
    push Not at hne
    obtain ⟨x, hfx, hgx⟩ := hspec f g hne.1 hne.2
    obtain ⟨y, hy⟩ : ∃ y : B →ₐ[k] k,
        y ((((Algebra.TensorProduct.basis A b).repr f).sum fun i c => x c • b i) *
          (((Algebra.TensorProduct.basis A b).repr g).sum fun i c => x c • b i)) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact mul_ne_zero hfx hgx (eq_zero_of_forall_algHom k B _ hall)
    apply hy
    rw [map_mul, ← productMap_eq_sum, ← productMap_eq_sum, ← map_mul, hfg, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

theorem exceptional_Lang_affine_point_and_product_geometry :
    (∀ (A : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A],
      Function.Injective fun (a : A) (x : A →ₐ[k] k) => x a) ∧
    (∀ (A : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
      (Z : Set (PrimeSpectrum A)), IsLocallyClosed Z → Z.Nonempty →
        ∃ x : A →ₐ[k] k, (⟨RingHom.ker x, RingHom.ker_isPrime _⟩ : PrimeSpectrum A) ∈ Z) ∧
    (∀ (A B : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A]
      [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B],
        IsReduced (A ⊗[k] B)) ∧
    (∀ (A B : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A]
      [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B],
        IrreducibleSpace (PrimeSpectrum A) → IrreducibleSpace (PrimeSpectrum B) →
          IrreducibleSpace (PrimeSpectrum (A ⊗[k] B))) ∧
    (∀ (A B : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A]
      [CommRing B] [Algebra k B] (f g : B →ₐ[k] A),
        (∀ x : A →ₐ[k] k, x.comp f = x.comp g) → f = g) ∧
    ∀ (A B : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A]
      [CommRing B] [Algebra k B] (I : Ideal B) (f : B →ₐ[k] A),
        (∀ x : A →ₐ[k] k, ∀ b ∈ I, x (f b) = 0) →
          ∃! g : (B ⧸ I) →ₐ[k] A, g.comp (Ideal.Quotient.mkₐ k I) = f := by
  refine ⟨fun A _ _ _ _ => evaluation_injective k A,
    fun A _ _ _ Z hZ hne => exists_algHom_mem_of_isLocallyClosed k A hZ hne,
    fun A B _ _ _ _ _ _ _ _ => isReduced_tensorProduct k A B,
    fun A B _ _ _ _ _ _ _ _ hA hB => ?_, fun A B _ _ _ _ _ _ f g hfg => ?_,
    fun A B _ _ _ _ _ _ I f hf => ?_⟩
  ·
    have : IsDomain A := by
      have h1 := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.1 hA
      rw [nilradical_eq_zero] at h1
      exact IsDomain.of_bot_isPrime A
    have : IsDomain B := by
      have h1 := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.1 hB
      rw [nilradical_eq_zero] at h1
      exact IsDomain.of_bot_isPrime B
    have := isDomain_tensorProduct k A B
    infer_instance
  ·
    ext b
    exact evaluation_injective k A (funext fun x => congrArg (fun φ : B →ₐ[k] k => φ b) (hfg x))
  ·
    have hI : ∀ b ∈ I, f b = 0 := fun b hb =>
      eq_zero_of_forall_algHom k A _ fun x => hf x b hb
    refine ⟨Ideal.Quotient.liftₐ I f hI, ?_, fun g hg => ?_⟩
    · ext b
      rfl
    · refine Ideal.Quotient.algHom_ext k ?_
      rw [hg]
      ext b
      rfl

end CFSG.LieType.AlgebraicGroups
