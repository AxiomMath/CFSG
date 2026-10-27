module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.LinearAlgebra.Dual.Lemmas

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u v w

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V] {W : Type w} [AddCommGroup W] [Module k W]

variable (k) in
@[expose] def polyEval (v : V) : MvPolynomial (Module.Dual k V) k →ₐ[k] k :=
  MvPolynomial.aeval fun φ => φ v

@[simp]
theorem polyEval_X (v : V) (φ : Module.Dual k V) : polyEval k v (MvPolynomial.X φ) = φ v :=
  MvPolynomial.aeval_X _ _

variable (k) in
@[expose] def zeroSet (S : Set (MvPolynomial (Module.Dual k V) k)) : Set V :=
  {v | ∀ f ∈ S, polyEval k v f = 0}

theorem mem_zeroSet {S : Set (MvPolynomial (Module.Dual k V) k)} {v : V} :
    v ∈ zeroSet k S ↔ ∀ f ∈ S, polyEval k v f = 0 :=
  Iff.rfl

variable (k) in
@[expose] def IsZariskiClosed (C : Set V) : Prop :=
  ∃ S : Set (MvPolynomial (Module.Dual k V) k), C = zeroSet k S

variable (k) in
@[expose] def IsCone (C : Set V) : Prop :=
  ∀ c : k, ∀ v ∈ C, c • v ∈ C

theorem isZariskiClosed_zeroSet (S : Set (MvPolynomial (Module.Dual k V) k)) :
    IsZariskiClosed k (zeroSet k S) :=
  ⟨S, rfl⟩

theorem isZariskiClosed_iInter {ι : Sort*} {C : ι → Set V} (hC : ∀ i, IsZariskiClosed k (C i)) :
    IsZariskiClosed k (⋂ i, C i) := by
  choose S hS using hC
  refine ⟨⋃ i, S i, Set.ext fun v => ?_⟩
  simp only [Set.mem_iInter, hS, mem_zeroSet]
  constructor
  · intro h f hf
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hf
    exact h i f hi
  · intro h i f hf
    exact h f (Set.mem_iUnion.mpr ⟨i, hf⟩)

theorem IsZariskiClosed.inter {C D : Set V} (hC : IsZariskiClosed k C) (hD : IsZariskiClosed k D) :
    IsZariskiClosed k (C ∩ D) := by
  obtain ⟨S, rfl⟩ := hC
  obtain ⟨T, rfl⟩ := hD
  refine ⟨S ∪ T, Set.ext fun v => ?_⟩
  simp only [Set.mem_inter_iff, mem_zeroSet, Set.mem_union]
  constructor
  · rintro ⟨h₁, h₂⟩ f (hf | hf)
    exacts [h₁ f hf, h₂ f hf]
  · intro h
    exact ⟨fun f hf => h f (Or.inl hf), fun f hf => h f (Or.inr hf)⟩

theorem polyEval_rename_comp (f : W →ₗ[k] V) (w : W) (p : MvPolynomial (Module.Dual k V) k) :
    polyEval k w (MvPolynomial.rename (fun φ : Module.Dual k V => φ ∘ₗ f) p) =
      polyEval k (f w) p := by
  simp only [polyEval, MvPolynomial.aeval_rename]
  rfl

theorem IsZariskiClosed.preimage {C : Set V} (hC : IsZariskiClosed k C) (f : W →ₗ[k] V) :
    IsZariskiClosed k (f ⁻¹' C) := by
  obtain ⟨S, rfl⟩ := hC
  refine ⟨MvPolynomial.rename (fun φ : Module.Dual k V => φ ∘ₗ f) '' S, Set.ext fun w => ?_⟩
  simp only [Set.mem_preimage, mem_zeroSet, Set.forall_mem_image, polyEval_rename_comp]

theorem isZariskiClosed_submodule (U : Submodule k V) : IsZariskiClosed k (U : Set V) := by
  refine ⟨MvPolynomial.X '' {φ : Module.Dual k V | ∀ u ∈ U, φ u = 0}, Set.ext fun v => ?_⟩
  simp only [SetLike.mem_coe, mem_zeroSet, Set.forall_mem_image, polyEval_X, Set.mem_setOf_eq]
  constructor
  · intro hv φ hφ
    exact hφ v hv
  · intro h
    by_contra hv
    obtain ⟨φ, hφv, hφU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
    refine hφv (@h φ fun u hu => ?_)
    have hmem : φ u ∈ U.map φ := Submodule.mem_map_of_mem hu
    rwa [hφU, Submodule.mem_bot] at hmem

theorem mem_zeroLocus_span_iff {σ : Type*} {T : Set (MvPolynomial σ k)} {x : σ → k} :
    x ∈ MvPolynomial.zeroLocus k (Ideal.span T) ↔ ∀ p ∈ T, MvPolynomial.aeval x p = 0 := by
  rw [MvPolynomial.mem_zeroLocus_iff]
  constructor
  · exact fun h p hp => h p (Ideal.subset_span hp)
  · intro h p hp
    have hle : Ideal.span T ≤ RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] k) :=
      Ideal.span_le.mpr fun q hq => RingHom.mem_ker.mpr (h q hq)
    exact RingHom.mem_ker.mp (hle hp)

theorem aeval_equivFun_aeval_coordinates {σ : Type*} [Fintype σ] (b : Module.Basis σ k V) (v : V)
    (p : MvPolynomial (Module.Dual k V) k) :
    MvPolynomial.aeval (b.equivFun v)
        (MvPolynomial.aeval (fun φ : Module.Dual k V =>
          ∑ i, MvPolynomial.C (φ (b i)) * MvPolynomial.X i) p) =
      polyEval k v p := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun φ => ?_
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, polyEval, map_sum, map_mul,
    MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  conv_rhs => rw [← b.sum_equivFun v]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

theorem IsZariskiClosed.exists_eq_preimage_zeroLocus {C : Set V} (hC : IsZariskiClosed k C)
    {σ : Type*} [Fintype σ] (b : Module.Basis σ k V) :
    ∃ I : Ideal (MvPolynomial σ k), C = b.equivFun ⁻¹' MvPolynomial.zeroLocus k I := by
  obtain ⟨S, rfl⟩ := hC
  let ψ : MvPolynomial (Module.Dual k V) k →ₐ[k] MvPolynomial σ k :=
    MvPolynomial.aeval fun φ => ∑ i, MvPolynomial.C (φ (b i)) * MvPolynomial.X i
  refine ⟨Ideal.span (ψ '' S), Set.ext fun v => ?_⟩
  rw [Set.mem_preimage, mem_zeroLocus_span_iff, Set.forall_mem_image, mem_zeroSet]
  exact forall₂_congr fun p _ => by rw [aeval_equivFun_aeval_coordinates]

theorem isZariskiClosed_preimage_zeroLocus {σ : Type*} [Fintype σ] (b : Module.Basis σ k V)
    (I : Ideal (MvPolynomial σ k)) :
    IsZariskiClosed k (b.equivFun ⁻¹' MvPolynomial.zeroLocus k I) := by
  refine ⟨MvPolynomial.rename b.coord '' (I : Set (MvPolynomial σ k)), Set.ext fun v => ?_⟩
  simp only [Set.mem_preimage, MvPolynomial.mem_zeroLocus_iff, mem_zeroSet, Set.forall_mem_image,
    SetLike.mem_coe, polyEval, MvPolynomial.aeval_rename]
  refine forall₂_congr fun p _ => ?_
  rw [show ((fun φ : Module.Dual k V => φ v) ∘ b.coord) = b.equivFun v from
    funext fun i => by simp [Module.Basis.equivFun_apply]]

end CFSG.LieType.AlgebraicGroups.ClosedCone
