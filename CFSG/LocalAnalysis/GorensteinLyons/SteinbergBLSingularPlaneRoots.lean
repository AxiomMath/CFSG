module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalElementary
public import Mathlib.Algebra.Field.ZMod

public noncomputable section

namespace CFSG.LocalAnalysis.GorensteinLyons

namespace SingularPlaneRoots

open Module QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (q : QuadraticForm (ZMod 2) V)

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

omit [Module (ZMod 2) V] in
theorem neg_eq_self' [Module (ZMod 2) V] (x : V) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

@[expose] def singularPlanes : Set (Submodule (ZMod 2) V) :=
  {U | finrank (ZMod 2) U = 2 ∧ ∀ x ∈ U, q x = 0}

theorem mem_singularPlanes {U : Submodule (ZMod 2) V} :
    U ∈ singularPlanes q ↔ finrank (ZMod 2) U = 2 ∧ ∀ x ∈ U, q x = 0 :=
  Iff.rfl

@[expose] def rootMap (u v : V) : V →ₗ[ZMod 2] V :=
  LinearMap.id + (polarBilin q v).smulRight u + (polarBilin q u).smulRight v

theorem rootMap_apply (u v x : V) :
    rootMap q u v x = x + polar q v x • u + polar q u x • v := by
  simp [rootMap]

theorem rootMap_eq_of_mem_span {u v u' v' : V} (hli : LinearIndependent (ZMod 2) ![u', v'])
    (hu' : u' ∈ Submodule.span (ZMod 2) {u, v}) (hv' : v' ∈ Submodule.span (ZMod 2) {u, v}) :
    rootMap q u' v' = rootMap q u v := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hu'
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.1 hv'
  have hdet : α * δ + β * γ = 1 := by
    rcases zmod_two_cases (α * δ + β * γ) with hd | hd
    · exfalso
      have h1 : δ • (α • u + β • v) + β • (γ • u + δ • v) = 0 := by
        have e : δ • (α • u + β • v) + β • (γ • u + δ • v) =
            (α * δ + β * γ) • u + (β * δ + β * δ) • v := by module
        rw [e, hd, CharTwo.add_self_eq_zero, zero_smul, zero_smul, add_zero]
      have h2 : γ • (α • u + β • v) + α • (γ • u + δ • v) = 0 := by
        have e : γ • (α • u + β • v) + α • (γ • u + δ • v) =
            (α * γ + α * γ) • u + (α * δ + β * γ) • v := by module
        rw [e, hd, CharTwo.add_self_eq_zero, zero_smul, zero_smul, add_zero]
      obtain ⟨hδ, hβ⟩ := LinearIndependent.pair_iff.1 hli δ β h1
      obtain ⟨hγ, hα⟩ := LinearIndependent.pair_iff.1 hli γ α h2
      have h0 : α • u + β • v = 0 := by rw [hα, hβ, zero_smul, zero_smul, add_zero]
      exact hli.ne_zero 0 (by simpa using h0)
    · exact hd
  refine LinearMap.ext fun x => ?_
  have key : polar q (γ • u + δ • v) x • (α • u + β • v) +
      polar q (α • u + β • v) x • (γ • u + δ • v) =
      (α * δ + β * γ) • (polar q v x • u + polar q u x • v) +
        (α * γ + α * γ) • (polar q u x • u) + (β * δ + β * δ) • (polar q v x • v) := by
    rw [polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, polar_smul_left,
      polar_smul_left]
    simp only [smul_eq_mul]
    module
  rw [rootMap_apply, rootMap_apply, add_assoc, key, hdet, CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, zero_smul, zero_smul, add_zero, add_zero, one_smul, add_assoc]

@[expose] def planeRoot (U : Submodule (ZMod 2) V) : V →ₗ[ZMod 2] V :=
  open Classical in
  if h : ∃ u v : V, u ∈ U ∧ v ∈ U ∧ LinearIndependent (ZMod 2) ![u, v] then
    rootMap q h.choose h.choose_spec.choose
  else LinearMap.id

theorem span_pair_eq {U : Submodule (ZMod 2) V} (hU : finrank (ZMod 2) U = 2) {u v : V}
    (hu : u ∈ U) (hv : v ∈ U) (hli : LinearIndependent (ZMod 2) ![u, v]) :
    Submodule.span (ZMod 2) {u, v} = U := by
  have : Module.Finite (ZMod 2) U := Module.finite_of_finrank_eq_succ hU
  have hle : Submodule.span (ZMod 2) {u, v} ≤ U := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    exacts [hu, hv]
  apply Submodule.eq_of_le_of_finrank_eq hle
  have h := finrank_span_eq_card hli
  rw [Fintype.card_fin, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
    Set.union_empty, Set.singleton_union] at h
  rw [h, hU]

theorem planeRoot_eq_rootMap {U : Submodule (ZMod 2) V} (hU : finrank (ZMod 2) U = 2) {u v : V}
    (hu : u ∈ U) (hv : v ∈ U) (hli : LinearIndependent (ZMod 2) ![u, v]) :
    planeRoot q U = rootMap q u v := by
  have hex : ∃ u v : V, u ∈ U ∧ v ∈ U ∧ LinearIndependent (ZMod 2) ![u, v] := ⟨u, v, hu, hv, hli⟩
  rw [planeRoot, dite_eq_left hex]
  obtain ⟨hu₀, hv₀, hli₀⟩ := hex.choose_spec.choose_spec
  have hUspan := (span_pair_eq hU hu hv hli).ge
  exact rootMap_eq_of_mem_span q hli₀ (hUspan hu₀) (hUspan hv₀)

theorem rootMap_eq_orthElementaryMap {u v : V} (hv : q v = 0) :
    rootMap q u v = CFSG.LocalAnalysis.ComponentInitial.orthElementaryMap q u v := by
  refine LinearMap.ext fun x => ?_
  rw [rootMap_apply, CFSG.LocalAnalysis.ComponentInitial.orthElementaryMap_apply, hv, zero_mul,
    zero_smul, sub_zero, sub_eq_add_neg, neg_eq_self', polar_comm q x u, polar_comm q x v]
  abel

theorem exists_basis_of_finrank_eq_two {U : Submodule (ZMod 2) V} (hU : finrank (ZMod 2) U = 2) :
    ∃ u v : V, u ∈ U ∧ v ∈ U ∧ LinearIndependent (ZMod 2) ![u, v] := by
  have : Module.Finite (ZMod 2) U := Module.finite_of_finrank_eq_succ hU
  let e := Module.finBasisOfFinrankEq (ZMod 2) U hU
  refine ⟨(e 0 : V), (e 1 : V), (e 0).2, (e 1).2, ?_⟩
  have h := e.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  convert h using 1
  funext i
  fin_cases i <;> rfl

@[expose] def rootSet : Set (V ≃ₗ[ZMod 2] V) :=
  {s | s ∈ TauCeti.QuadraticMap.orthogonalGroup q ∧ s * s = 1 ∧
    finrank (ZMod 2) (LinearMap.range ((s : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2 ∧
    ∀ x ∈ LinearMap.range ((s : V →ₗ[ZMod 2] V) - LinearMap.id), q x = 0}

@[expose] def rootsIn (H : Subgroup (V ≃ₗ[ZMod 2] V)) : Set (V ≃ₗ[ZMod 2] V) :=
  (H : Set (V ≃ₗ[ZMod 2] V)) ∩ rootSet q

@[expose] def rootPlanes (H : Subgroup (V ≃ₗ[ZMod 2] V)) : Set (Submodule (ZMod 2) V) :=
  (fun s : V ≃ₗ[ZMod 2] V => LinearMap.range ((s : V →ₗ[ZMod 2] V) - LinearMap.id)) ''
    rootsIn q H

theorem mem_rootSet {s : V ≃ₗ[ZMod 2] V} :
    s ∈ rootSet q ↔ s ∈ TauCeti.QuadraticMap.orthogonalGroup q ∧ s * s = 1 ∧
      finrank (ZMod 2) (LinearMap.range ((s : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2 ∧
      ∀ x ∈ LinearMap.range ((s : V →ₗ[ZMod 2] V) - LinearMap.id), q x = 0 :=
  Iff.rfl

theorem mem_rootsIn {H : Subgroup (V ≃ₗ[ZMod 2] V)} {s : V ≃ₗ[ZMod 2] V} :
    s ∈ rootsIn q H ↔ s ∈ H ∧ s ∈ rootSet q :=
  Iff.rfl

theorem mem_rootPlanes {H : Subgroup (V ≃ₗ[ZMod 2] V)} {L : Submodule (ZMod 2) V} :
    L ∈ rootPlanes q H ↔
      ∃ s ∈ rootsIn q H, LinearMap.range ((s : V →ₗ[ZMod 2] V) - LinearMap.id) = L :=
  Iff.rfl

end SingularPlaneRoots

section Transpositions

variable {A : Type*} [Group A]

@[expose] def IsThreeFourPlusTranspositions (D : Set A) : Prop :=
  (∀ g : A, ∀ x ∈ D, g * x * g⁻¹ ∈ D) ∧ (∀ x ∈ D, orderOf x = 2) ∧ Subgroup.closure D = ⊤ ∧
    (∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) ≤ 4) ∧
    ∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) = 4 → x * y * x⁻¹ * y⁻¹ ∈ D

@[expose] def IsThreeTranspositions (D : Set A) : Prop :=
  IsThreeFourPlusTranspositions D ∧ ∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) ≤ 3

end Transpositions

open SingularPlaneRoots Module QuadraticMap in
theorem binary_singular_plane_root_and_transposition_set_data {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (q : QuadraticForm (ZMod 2) V) :
    (∀ U ∈ singularPlanes q, ∃ u v : V, u ∈ U ∧ v ∈ U ∧ LinearIndependent (ZMod 2) ![u, v]) ∧
    ∀ U ∈ singularPlanes q, ∀ u ∈ U, ∀ v ∈ U, LinearIndependent (ZMod 2) ![u, v] →
      (∀ x, planeRoot q U x = x + polar q v x • u + polar q u x • v) ∧
      planeRoot q U = CFSG.LocalAnalysis.ComponentInitial.orthElementaryMap q u v := by
  refine ⟨fun U hU => exists_basis_of_finrank_eq_two hU.1, fun U hU u hu v hv hli => ?_⟩
  rw [planeRoot_eq_rootMap q hU.1 hu hv hli]
  exact ⟨rootMap_apply q u v, rootMap_eq_orthElementaryMap q (hU.2 v hv)⟩

end CFSG.LocalAnalysis.GorensteinLyons
