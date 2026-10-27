module

public import CFSG.LieType.AlgebraicGroups.AffinePointGeometry
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct Topology

theorem eq_univ_of_isConstructible_of_closedPoints_subset {R : Type} [CommRing R]
    [IsJacobsonRing R] {s : Set (PrimeSpectrum R)} (hs : IsConstructible s)
    (hcl : closedPoints (PrimeSpectrum R) ⊆ s) : s = Set.univ := by
  by_contra hne
  have key : ∀ t (ht : IsConstructible t), t.Nonempty →
      (t ∩ closedPoints (PrimeSpectrum R)).Nonempty := by
    intro t ht
    induction t, ht using IsConstructible.induction_of_isTopologicalBasis
      (fun r : R => (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)))
      PrimeSpectrum.isTopologicalBasis_basic_opens
      (fun r => PrimeSpectrum.isCompact_basicOpen r) with
    | sdiff i s hs =>
      intro hne
      refine nonempty_inter_closedPoints hne ?_
      have h1 : IsOpen (⋃ j ∈ s, (PrimeSpectrum.basicOpen j : Set (PrimeSpectrum R))) :=
        isOpen_biUnion fun j _ => (PrimeSpectrum.basicOpen j).2
      exact (PrimeSpectrum.basicOpen i).2.isLocallyClosed.inter h1.isClosed_compl.isLocallyClosed
    | union s hs t ht ihs iht =>
      rintro ⟨p, hp | hp⟩
      · obtain ⟨q, hq, hqc⟩ := ihs ⟨p, hp⟩
        exact ⟨q, Or.inl hq, hqc⟩
      · obtain ⟨q, hq, hqc⟩ := iht ⟨p, hp⟩
        exact ⟨q, Or.inr hq, hqc⟩
  obtain ⟨p, hp⟩ : sᶜ.Nonempty := Set.nonempty_compl.2 hne
  obtain ⟨q, hq, hqc⟩ := key _ hs.compl ⟨p, hp⟩
  exact hq (hcl hqc)

theorem exists_algHom_of_mem_range_comap {k L B A : Type} [Field k] [Field L] [IsAlgClosed L]
    [CommRing B] [CommRing A] [Algebra k B] [Algebra k A] [Algebra k L] [Algebra B A]
    [IsScalarTower k B A] [Algebra.FiniteType k A] (y : B →ₐ[k] L)
    (hp : (⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B A))) :
    ∃ x : A →ₐ[k] L, x.comp (IsScalarTower.toAlgHom k B A) = y := by
  classical
  set p : PrimeSpectrum B := ⟨RingHom.ker y, RingHom.ker_isPrime y⟩ with hpdef
  have : p.asIdeal.IsPrime := p.2
  have h1 := (PrimeSpectrum.nontrivial_iff_mem_rangeComap (S := A) p).2 hp
  let : Algebra B L := y.toRingHom.toAlgebra
  have : IsScalarTower k B L := IsScalarTower.of_algebraMap_eq fun c => (y.commutes c).symm
  let ι : p.asIdeal.ResidueField →+* L := Ideal.ResidueField.lift p.asIdeal y.toRingHom le_rfl
    (fun b hb => by
      change IsUnit (y b)
      refine isUnit_iff_ne_zero.2 fun h0 => hb ?_
      change b ∈ RingHom.ker y
      exact h0)
  let : Algebra p.asIdeal.ResidueField L := ι.toAlgebra
  have : IsScalarTower B p.asIdeal.ResidueField L :=
    IsScalarTower.of_algebraMap_eq fun b => by
      change y b = ι (algebraMap B p.asIdeal.ResidueField b)
      exact (Ideal.ResidueField.lift_algebraMap _ _ _ _ b).symm
  have h2 : Nontrivial (L ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[B] A)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _
      (RingHom.injective _)
  have e := Algebra.TensorProduct.cancelBaseChange B p.asIdeal.ResidueField L L A
  have h3 : Nontrivial (L ⊗[B] A) := e.injective.nontrivial
  have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType k B A
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (L ⊗[B] A)
  obtain ⟨ψ, -⟩ := exists_algHom_ker_eq L (L ⊗[B] A) m
  let xr : A →+* L := ψ.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := B) (A := L) (B := A)).toRingHom
  have hx : ∀ b : B, xr (algebraMap B A b) = y b := fun b => by
    change ψ (1 ⊗ₜ algebraMap B A b) = y b
    have h4 : (1 : L) ⊗ₜ[B] algebraMap B A b = algebraMap L (L ⊗[B] A) (algebraMap B L b) := by
      rw [Algebra.algebraMap_eq_smul_one (A := A), TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Algebra.TensorProduct.algebraMap_apply,
        Algebra.smul_def, mul_one]
      rfl
    rw [h4, AlgHom.commutes]
    rfl
  refine ⟨{ xr with commutes' := fun c => ?_ }, AlgHom.ext fun b => hx b⟩
  change xr (algebraMap k A c) = algebraMap k L c
  rw [IsScalarTower.algebraMap_apply k B A, hx, AlgHom.commutes]

theorem exceptional_Lang_constructible_point_surjectivity_field_extension {k L : Type} [Field k]
    [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L] {B : Type} [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] {J : Type} [Finite J] (A : J → Type) [∀ j, CommRing (A j)]
    [∀ j, Algebra k (A j)] [∀ j, Algebra.FiniteType k (A j)] (φ : ∀ j, B →ₐ[k] A j)
    (hsurj : ∀ y : B →ₐ[k] k, ∃ j, ∃ x : A j →ₐ[k] k, x.comp (φ j) = y) :
    ∀ y : B →ₐ[k] L, ∃ j, ∃ x : A j →ₐ[k] L, x.comp (φ j) = y := by
  classical
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hfp : ∀ j, (φ j : B →+* A j).FinitePresentation := fun j => by
    refine RingHom.FinitePresentation.of_finiteType.1 ?_
    refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k B) ?_
    rw [(φ j).comp_algebraMap]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hcons : IsConstructible (⋃ j, Set.range (PrimeSpectrum.comap (φ j : B →+* A j))) :=
    IsConstructible.iUnion fun j => PrimeSpectrum.isConstructible_range_comap (hfp j)
  have hcl : closedPoints (PrimeSpectrum B) ⊆
      ⋃ j, Set.range (PrimeSpectrum.comap (φ j : B →+* A j)) := by
    intro q hq
    have : q.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).1 hq
    obtain ⟨y₀, hy₀⟩ := exists_algHom_ker_eq k B q.asIdeal
    obtain ⟨j, x, hx⟩ := hsurj y₀
    refine Set.mem_iUnion.2 ⟨j, ⟨⟨RingHom.ker x, RingHom.ker_isPrime x⟩, ?_⟩⟩
    ext b
    change (φ j) b ∈ RingHom.ker x ↔ b ∈ q.asIdeal
    rw [← hy₀, RingHom.mem_ker, RingHom.mem_ker, ← hx]
    rfl
  have huniv := eq_univ_of_isConstructible_of_closedPoints_subset hcons hcl
  intro y
  have hmem : (⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum B) ∈
      ⋃ j, Set.range (PrimeSpectrum.comap (φ j : B →+* A j)) := by
    rw [huniv]
    exact Set.mem_univ _
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
  let : Algebra B (A j) := (φ j : B →+* A j).toAlgebra
  have : IsScalarTower k B (A j) :=
    IsScalarTower.of_algebraMap_eq fun c => ((φ j).commutes c).symm
  obtain ⟨x, hx⟩ := exists_algHom_of_mem_range_comap y hj
  exact ⟨j, x, AlgHom.ext fun b => congrArg (fun g : B →ₐ[k] L => g b) hx⟩

end CFSG.LieType.AlgebraicGroups
