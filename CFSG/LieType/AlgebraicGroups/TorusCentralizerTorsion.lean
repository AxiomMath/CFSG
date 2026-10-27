module

public import CFSG.LinearAlgebra.TorusPrimeTorsion
public import CFSG.LieType.AlgebraicGroups.TorusCoordinates
public import CFSG.LieType.AlgebraicGroups.EquivariantAffineEmbedding

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CategoryTheory TauCeti WithConv

universe u

private theorem splitTorus_centralizer_detector_of_comodule
    {k H V : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
    {r : ℕ} [AddCommGroup V] [Module k V] [Module.Finite k V] [Comodule k H V]
    (π : H →ₐc[k] MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)))
    (hfaith : Function.Injective (Comodule.basePointsRepresentation (R := k) (H := H) V))
    (m : ℕ) (F0 : Subgroup (Fin r → kˣ)) (hF0 : Finite F0)
    (hmem : ∀ s : Fin r → kˣ, s ∈ F0 ↔ s ^ m = 1)
    (hcomm : letI : Comodule k (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V :=
        Comodule.Corestrict π.toCoalgHom
      ∀ A : V →ₗ[k] V,
        (∀ s ∈ F0, A.comp (Comodule.basePointsRepresentation (R := k)
            (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V (SplitTorus.pointsMulEquiv.symm s)) =
          (Comodule.basePointsRepresentation (R := k)
            (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V (SplitTorus.pointsMulEquiv.symm s)).comp A) ↔
        (∀ s : Fin r → kˣ, A.comp (Comodule.basePointsRepresentation (R := k)
            (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V (SplitTorus.pointsMulEquiv.symm s)) =
          (Comodule.basePointsRepresentation (R := k)
            (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V (SplitTorus.pointsMulEquiv.symm s)).comp A)) :
    ∃ F : Subgroup (WithConv (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)) →ₐ[k] k)),
      Finite F ∧ (∀ t, t ∈ F ↔ t ^ m = 1) ∧
      Subgroup.centralizer (Set.range (fun t : F => AlgHom.mapDomain (A := k) π t.val)) =
        Subgroup.centralizer (Set.range (AlgHom.mapDomain (A := k) π)) := by
  classical
  let : Comodule k (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V :=
    Comodule.Corestrict π.toCoalgHom
  let E : WithConv (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)) →ₐ[k] k) ≃*
      (Fin r → kˣ) := SplitTorus.pointsMulEquiv (R := k) (A := k) (σ := Fin r)
  let F : Subgroup (WithConv (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)) →ₐ[k] k)) :=
    F0.comap E.toMonoidHom
  let : Finite F0 := hF0
  let j : F → F0 := fun t => ⟨E t.val, t.property⟩
  let : Finite F := Finite.of_injective j (by
    intro x y h
    exact Subtype.ext (E.injective (congrArg Subtype.val h)))
  have hFm (t) : t ∈ F ↔ t ^ m = 1 := by
    change E t ∈ F0 ↔ t ^ m = 1
    rw [hmem, ← map_pow, ← map_one E]
    exact E.injective.eq_iff
  have heq (s : Fin r → kˣ) : Comodule.basePointsRepresentation
      (R := k) (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V (E.symm s) =
      Comodule.basePointsRepresentation (R := k) (H := H) V (AlgHom.mapDomain π (E.symm s)) := by
    rw [Comodule.basePointsRepresentation_corestrict]
  refine ⟨F, inferInstance, hFm, ?_⟩
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    obtain ⟨t, rfl⟩ := hy
    apply hfaith
    let A := Comodule.basePointsRepresentation (R := k) (H := H) V x
    have hA : ∀ s ∈ F0, A.comp (Comodule.basePointsRepresentation
        (R := k) (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V (E.symm s)) =
        (Comodule.basePointsRepresentation (R := k)
          (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V (E.symm s)).comp A := by
      intro s hs
      rw [heq]
      have hsF : E.symm s ∈ F := by
        change E (E.symm s) ∈ F0
        rw [MulEquiv.apply_symm_apply]
        exact hs
      have hh := congrArg (Comodule.basePointsRepresentation (R := k) (H := H) V)
        (hx (AlgHom.mapDomain π (E.symm s)) ⟨⟨E.symm s, hsF⟩, rfl⟩)
      rw [map_mul, map_mul] at hh
      exact hh.symm
    have hh := (hcomm A).mp hA (E t)
    rw [heq, MulEquiv.symm_apply_apply] at hh
    rw [map_mul, map_mul]
    exact hh.symm
  · intro hx y hy
    obtain ⟨t, rfl⟩ := hy
    exact hx _ ⟨t.val, rfl⟩

theorem exists_primePower_splitTorus_centralizer_detector
    {k H V : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
    {r : ℕ} [AddCommGroup V] [Module k V] [Module.Finite k V] [Comodule k H V]
    (π : H →ₐc[k] MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)))
    (hfaith : Function.Injective (Comodule.basePointsRepresentation (R := k) (H := H) V)) {p : ℕ} (hp : p.Prime) (hpk : (p : k) ≠ 0) :
    ∃ (e : ℕ) (F : Subgroup
        (WithConv (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)) →ₐ[k] k))),
      0 < e ∧ Finite F ∧ (∀ t, t ∈ F ↔ t ^ (p ^ e) = 1) ∧
      Subgroup.centralizer (Set.range (fun t : F => AlgHom.mapDomain (A := k) π t.val)) =
        Subgroup.centralizer (Set.range (AlgHom.mapDomain (A := k) π)) := by
  classical
  let : Comodule k (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V :=
    Comodule.Corestrict π.toCoalgHom
  obtain ⟨e, F0, he, hF0, _, hmem, _, hcomm⟩ :=
    CFSG.LinearAlgebra.exists_primePower_basePointsRepresentation_detector (K := k) (r := r) (V := V) hp hpk
  obtain ⟨F, hF⟩ := splitTorus_centralizer_detector_of_comodule π hfaith (p ^ e) F0 hF0 hmem hcomm
  exact ⟨e, F, he, hF⟩

theorem exists_primePower_splitTorus_centralizer_detector_of_finiteType
    {k : Type u} [Field k] [IsAlgClosed k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {r : ℕ}
    (π : H →ₐc[k] MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) {p : ℕ} (hp : p.Prime) (hpk : (p : k) ≠ 0) :
    ∃ (e : ℕ) (F : Subgroup
        (WithConv (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)) →ₐ[k] k))),
      0 < e ∧ Finite F ∧ (∀ t, t ∈ F ↔ t ^ (p ^ e) = 1) ∧
      Subgroup.centralizer (Set.range (fun t : F => AlgHom.mapDomain (A := k) π t.val)) =
        Subgroup.centralizer (Set.range (AlgHom.mapDomain (A := k) π)) := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k H).out
  obtain ⟨D, hD, hsD⟩ := Subcoalgebra.exists_finiteDimensional_subcoalgebra_of_setFinite
    (k := k) (C := H) (s : Set H) s.finite_toSet
  have hgen : Algebra.adjoin k (D : Set H) = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Algebra.adjoin_mono hsD
  let : AddCommGroup D.toRegularSubcomodule := inferInstanceAs (AddCommGroup D.toSubmodule)
  let : Module.Finite k D.toRegularSubcomodule := hD
  exact exists_primePower_splitTorus_centralizer_detector (V := D.toRegularSubcomodule) π
    (basePointsRepresentation_injective_of_generating_subcoalgebra D hgen) hp hpk

private theorem torus_centralizer_detector_of_coordinates
    {k : Type u} [Field k] [IsAlgClosed k]
    (H T : FiniteTypeCommHopfAlgCat.{u,u} k) (π : H.obj ⟶ T.obj) {r : ℕ}
    (e : MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)) ≃ₐc[k] T)
    (m : ℕ) (F0 : Subgroup (WithConv
      (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)) →ₐ[k] k))) (hF0 : Finite F0)
    (hmem : ∀ t, t ∈ F0 ↔ t ^ m = 1)
    (hcent : let q := e.symm.toBialgHom.comp π.hom
      Subgroup.centralizer (Set.range (fun t : F0 => AlgHom.mapDomain (A := k) q t.val)) =
        Subgroup.centralizer (Set.range (AlgHom.mapDomain (A := k) q))) :
    ∃ F : Subgroup (WithConv (T →ₐ[k] k)), Finite F ∧ (∀ t, t ∈ F ↔ t ^ m = 1) ∧
      Subgroup.centralizer (Set.range (fun t : F => AlgHom.mapDomain (A := k) π.hom t.val)) =
        Subgroup.centralizer (Set.range (AlgHom.mapDomain (A := k) π.hom)) := by
  classical
  let q := e.symm.toBialgHom.comp π.hom
  let E := AlgHom.mapDomainMulEquiv (A := k) e
  let F := F0.comap E.toMonoidHom
  let : Finite F0 := hF0
  let j : F → F0 := fun t => ⟨E t.val, t.property⟩
  let : Finite F := Finite.of_injective j (by
    intro x y h
    exact Subtype.ext (E.injective (congrArg Subtype.val h)))
  have hFm (t) : t ∈ F ↔ t ^ m = 1 := by
    change E t ∈ F0 ↔ _
    rw [hmem, ← map_pow, ← map_one E]
    exact E.injective.eq_iff
  have heq (t) : AlgHom.mapDomain (A := k) q (E t) = AlgHom.mapDomain π.hom t := by
    change AlgHom.mapDomain π.hom (AlgHom.mapDomain e.symm.toBialgHom (E t)) = _
    change AlgHom.mapDomain π.hom (E.symm (E t)) = _
    rw [MulEquiv.symm_apply_apply]
  have hrange : Set.range (AlgHom.mapDomain (A := k) q) =
      Set.range (AlgHom.mapDomain (A := k) π.hom) := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨E.symm s, by rw [← heq, MulEquiv.apply_symm_apply]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨E t, heq t⟩
  have hFrange : Set.range (fun t : F => AlgHom.mapDomain (A := k) π.hom t.val) =
      Set.range (fun s : F0 => AlgHom.mapDomain (A := k) q s.val) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨⟨E t.val, t.property⟩, heq t.val⟩
    · rintro ⟨s, rfl⟩
      have hs : E.symm s.val ∈ F := by
        change E (E.symm s.val) ∈ F0
        rw [MulEquiv.apply_symm_apply]
        exact s.property
      refine ⟨⟨E.symm s.val, hs⟩, ?_⟩
      change AlgHom.mapDomain π.hom (E.symm s.val) = AlgHom.mapDomain q s.val
      rw [← heq, MulEquiv.apply_symm_apply]
  refine ⟨F, inferInstance, hFm, ?_⟩
  rw [hFrange, ← hrange]
  exact hcent

theorem exists_primePower_torus_centralizer_detector
    {k : Type u} [Field k] [IsAlgClosed k]
    (H T : FiniteTypeCommHopfAlgCat.{u, u} k) (hT : torusCommHopfAlgProperty k T)
    (π : H.obj ⟶ T.obj) {p : ℕ} (hp : p.Prime) (hpk : (p : k) ≠ 0) :
    ∃ (e : ℕ) (F : Subgroup (WithConv (T →ₐ[k] k))),
      0 < e ∧ Finite F ∧ (∀ t, t ∈ F ↔ t ^ (p ^ e) = 1) ∧
      Subgroup.centralizer (Set.range (fun t : F => AlgHom.mapDomain (A := k) π.hom t.val)) =
        Subgroup.centralizer (Set.range (AlgHom.mapDomain (A := k) π.hom)) := by
  classical
  obtain ⟨r, ⟨e⟩⟩ := exists_coordinateEquiv_of_torus T hT
  let q := e.symm.toBialgHom.comp π.hom
  obtain ⟨n, F0, hn, hF0, hmem, hcent⟩ :=
    exists_primePower_splitTorus_centralizer_detector_of_finiteType H q hp hpk
  obtain ⟨F, hF⟩ := torus_centralizer_detector_of_coordinates H T π e (p ^ n) F0 hF0 hmem hcent
  exact ⟨n, F, hn, hF⟩

end CFSG.LieType.AlgebraicGroups
