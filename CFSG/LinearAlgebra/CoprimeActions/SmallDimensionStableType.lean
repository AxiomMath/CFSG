module

public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import CFSG.LinearAlgebra.CoprimeActions.PrimeNormalizerStableIrreducibleType

public section

open Submodule

open scoped MonoidAlgebra

namespace CFSG.LinearAlgebra.CoprimeActions.SmallDimensionStableType

open CFSG.LinearAlgebra.CoprimeActions.PrimeNormalizerStableIrreducibleType

theorem twist_iso {F : Type*} [Field F]
    {E : Type*} [Group E] [Finite E]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F E V) (hcard : (Nat.card E : F) ≠ 0)
    (α : MulAut E) (T : V ≃ₗ[F] V) (q : ℕ) [hq : Fact q.Prime] (hT : T ^ q = 1)
    (hcov : ∀ e v, T (ρ e v) = ρ (α e) (T v))
    (hdim : Module.finrank F V < q)
    (S : Submodule F[E] ρ.asModule) [IsSimpleModule F[E] S] :
    Nonempty (S ≃ₗ[F[E]] tw (mkSLEquiv ρ α T hcov) S) := by
  by_contra hA
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : NeZero (Nat.card E : F) := ⟨hcard⟩
  haveI : IsSemisimpleModule F[E] ρ.asModule := inferInstance
  set T' := mkSLEquiv ρ α T hcov with hT'
  have hit : ∀ n x, (⇑T')^[n] x = ρ.asModuleEquiv.symm ((⇑T)^[n] (ρ.asModuleEquiv x)) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl
  have hTn : ∀ x, (⇑T)^[q] x = x := by
    intro x
    rw [← LinearEquiv.coe_pow, hT]; rfl
  have hmem : ∀ n (X : Submodule F[E] ρ.asModule) y,
      y ∈ (tw T')^[n] X ↔ ∃ x ∈ X, (⇑T')^[n] x = y := by
    intro n
    induction n with
    | zero => intro X y; simp
    | succ n ih =>
      intro X y
      simp only [Function.iterate_succ_apply']
      constructor
      · intro hy
        obtain ⟨z, hz, rfl⟩ := hy
        obtain ⟨x, hx, rfl⟩ := (ih X z).1 hz
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, (ih X _).2 ⟨x, hx, rfl⟩, rfl⟩
  have hid : (tw T')^[q] = id := by
    funext X
    ext y
    rw [hmem]
    simp only [hit, hTn, LinearEquiv.symm_apply_apply, id]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy; exact ⟨y, hy, rfl⟩
  have hind := clifford_indep T' q hid S hA
  let W : Fin q → Submodule F ρ.asModule := fun i =>
    (isotypicComponent F[E] ρ.asModule ((tw T')^[i.val] S)).restrictScalars F
  have hWind : iSupIndep W := by
    intro i
    have h1 := hind i
    simp only [W]
    simp only [← Submodule.restrictScalars_iSup]
    rw [Submodule.disjoint_def] at h1 ⊢
    intro x hx hx'
    exact h1 x hx hx'
  have hsimple : ∀ n : ℕ, IsSimpleModule F[E] ((tw T')^[n] S) := fun n =>
    tw_iter_simple T' ‹_› n
  have hne : ∀ i : Fin q, ∃ v : ρ.asModule, v ∈ W i ∧ v ≠ 0 := by
    intro i
    haveI := hsimple i.val
    haveI := IsSimpleModule.nontrivial F[E] ((tw T')^[i.val] S)
    obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : ((tw T')^[i.val] S))
    exact ⟨v, Submodule.le_isotypicComponent _ hv, fun h => hv0 (by ext; simpa using h)⟩
  choose v hvW hv0 using hne
  have hli : LinearIndependent F v := hWind.linearIndependent W hvW hv0
  have := hli.fintype_card_le_finrank
  have h2 : Module.finrank F ρ.asModule = Module.finrank F V := rfl
  simp only [Fintype.card_fin] at this
  omega

end CFSG.LinearAlgebra.CoprimeActions.SmallDimensionStableType
