module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDMain
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDDesc
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDDim

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

section Uniq

variable {p n : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F] [CharP F p]
  {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
  {W' : Type} [AddCommGroup W'] [Module (ZMod p) W'] [Module.Finite (ZMod p) W']
  (σ : Representation (ZMod p) (SLm F) W) (σ' : Representation (ZMod p) (SLm F) W')

omit [Module.Finite (ZMod p) W] [CharP F p] in
theorem embedding_of_hasConstituent (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n) {A : ℕ} (hA : A < p ^ n) (h : HasConstituent p F σ A) :
    ∃ f : (stRep F A).asModule →ₗ[MonoidAlgebra F (SLm F)] (repXT σ).asModule,
      Function.Injective f := by
  obtain ⟨f, hf⟩ := h
  have hsimple := stRep_simple hS hp2 hn hF hA
  let f' : (stRep F A).asModule →ₗ[MonoidAlgebra F (SLm F)] (repXT σ).asModule :=
    (xEquiv σ).toLinearMap ∘ₗ f ∘ₗ (stEquiv F A).symm.toLinearMap
  have hf'0 : f' ≠ 0 := by
    intro h0
    apply hf
    ext x
    have h1 := LinearMap.congr_fun h0 ((stEquiv F A) x)
    have h2 : (xEquiv σ) (f x) = 0 := by simpa [f'] using h1
    exact (xEquiv σ).map_eq_zero_iff.mp h2
  exact ⟨f', (LinearMap.injective_or_eq_zero f').resolve_right hf'0⟩

omit [Module.Finite (ZMod p) W] in
theorem hasConstituent_rot (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n) {B : ℕ} (hB : B < p ^ n) (h : HasConstituent p F σ B) :
    HasConstituent p F σ (rot p n B) := by
  obtain ⟨f', hinj⟩ := embedding_of_hasConstituent σ hS hp2 hn hF hB h
  let N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule := LinearMap.range f'
  let ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F B).asModule :=
    (LinearEquiv.ofInjective f' hinj).symm
  obtain ⟨e⟩ := map_phi_label σ hS hp2 hn hF N hB ι
  exact hasConstituent_of_label σ hS hp2 hn hF
    (mix11cD_rot_lt (Nat.Prime.one_lt Fact.out) hn hB) e

omit [Module.Finite (ZMod p) W] in
theorem hasConstituent_iterate_rot (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n) {B : ℕ} (hB : B < p ^ n) (h : HasConstituent p F σ B) (k : ℕ) :
    HasConstituent p F σ ((rot p n)^[k] B) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hasConstituent_rot σ hS hp2 hn hF
      (mix11cD_iterate_rot_lt (Nat.Prime.one_lt Fact.out) hn hB k) ih

theorem uniq_core (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule)
    (hW' : IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ'.asModule)
    {A : ℕ} (hA : A < p ^ n) (h : HasConstituent p F σ A) (h' : HasConstituent p F σ' A) :
    Nonempty (σ.asModule ≃ₗ[MonoidAlgebra (ZMod p) (SLm F)] σ'.asModule) := by
  obtain ⟨f₁, hf₁⟩ := embedding_of_hasConstituent σ hS hp2 hn hF hA h
  obtain ⟨f₂, hf₂⟩ := embedding_of_hasConstituent σ' hS hp2 hn hF hA h'
  obtain ⟨-, -, -, -, -, -, -, hsemi⟩ := orbit_structure σ hS hp2 hn hF hW
  obtain ⟨H, hH⟩ := IsSemisimpleModule.extension_property f₁ hf₁ f₂
  have hH0 : H ≠ 0 := by
    intro h0
    have := stRep_simple hS hp2 hn hF hA
    have hnt : Nontrivial (stRep F A).asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra F (SLm F)) (stRep F A).asModule
    obtain ⟨x, hx⟩ := exists_ne (0 : (stRep F A).asModule)
    apply hx
    apply hf₂
    have := LinearMap.congr_fun hH x
    rw [LinearMap.comp_apply, h0, LinearMap.zero_apply] at this
    rw [← this, map_zero]
  let f : (CFSG.Theory.Representation.extendScalars F σ).asModule →ₗ[MonoidAlgebra F (SLm F)]
      (CFSG.Theory.Representation.extendScalars F σ').asModule :=
    (xEquiv σ').symm.toLinearMap ∘ₗ H ∘ₗ (xEquiv σ).toLinearMap
  have hf0 : f ≠ 0 := by
    intro h0
    apply hH0
    ext x
    have h1 := LinearMap.congr_fun h0 ((xEquiv σ).symm x)
    have h2 : (xEquiv σ').symm (H x) = 0 := by simpa [f] using h1
    exact (xEquiv σ').symm.map_eq_zero_iff.mp h2
  obtain ⟨g, hg⟩ := exists_ne_zero_hom_of_extendScalars σ σ' f hf0
  exact ⟨LinearEquiv.ofBijective g (LinearMap.bijective_of_ne_zero hg)⟩

theorem uniq_of_rot (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule)
    (hW' : IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ'.asModule)
    {A A' : ℕ} (hA : A < p ^ n) (h : HasConstituent p F σ A) (h' : HasConstituent p F σ' A')
    (s : ℕ) (hs : A' = (rot p n)^[s] A) :
    Nonempty (σ.asModule ≃ₗ[MonoidAlgebra (ZMod p) (SLm F)] σ'.asModule) := by
  have hp : 1 < p := Nat.Prime.one_lt Fact.out
  have hA' : A' < p ^ n := hs ▸ mix11cD_iterate_rot_lt hp hn hA s
  have hperA : (rot p n)^[rotPeriod p n A] A = A := Function.iterate_minimalPeriod
  have hrpos : 0 < rotPeriod p n A := mix11cD_rotPeriod_pos hp hn hA
  have hmul : ∀ m, (rot p n)^[rotPeriod p n A * m] A = A := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, hperA, ih]
  have hk : (rotPeriod p n A * s - s) + s = rotPeriod p n A * s := by
    have : s ≤ rotPeriod p n A * s := Nat.le_mul_of_pos_left s hrpos
    omega
  have hback : (rot p n)^[rotPeriod p n A * s - s] A' = A := by
    rw [hs, ← Function.iterate_add_apply, hk, hmul]
  have h'' : HasConstituent p F σ' A := by
    have := hasConstituent_iterate_rot σ' hS hp2 hn hF hA' h' (rotPeriod p n A * s - s)
    rwa [hback] at this
  exact uniq_core σ σ' hS hp2 hn hF hW hW' hA h h''

end Uniq

end CFSG.GH74.GLS.Stage4.Rest
