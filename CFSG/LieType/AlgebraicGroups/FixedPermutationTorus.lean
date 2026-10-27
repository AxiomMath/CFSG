module

public import CFSG.LieType.AlgebraicGroups.FixedConnectedGenerators
public import TauCeti.GroupTheory.Perm.Partition
public import TauCeti.GroupTheory.Perm.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u

variable {k : Type u} [Field k] {ι : Type u} [Finite ι]

private abbrev PermGroup (π : Equiv.Perm ι) : Subgroup (Equiv.Perm ι) :=
  Subgroup.zpowers π

private abbrev OrbitQuot (π : Equiv.Perm ι) : Type u :=
  MulAction.orbitRel.Quotient (PermGroup π) ι

private abbrev permutationRepFinsupp (π : Equiv.Perm ι) :
    (ι →₀ ℤ) →ₗ[ℤ] (ι →₀ ℤ) :=
  Finsupp.lmapDomain (M := ℤ) (R := ℤ) (π : ι → ι)

private abbrev orbitSumF (π : Equiv.Perm ι) :
    (ι →₀ ℤ) →ₗ[ℤ] (OrbitQuot π →₀ ℤ) :=
  Finsupp.lmapDomain (M := ℤ) (R := ℤ)
    (Quotient.mk (MulAction.orbitRel (PermGroup π) ι))

omit [Finite ι] in
private theorem preimage_eq_permutationRep
    (π : Equiv.Perm ι)
    (σ : MonoidAlgebra k (Multiplicative (ι →₀ ℤ)) →ₐc[k]
      MonoidAlgebra k (Multiplicative (ι →₀ ℤ)))
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1) :
    TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage k σ =
      AddMonoidHom.toMultiplicative (permutationRepFinsupp π).toAddMonoidHom := by
  let G := PermGroup π
  let g : G := ⟨π, Subgroup.mem_zpowers π⟩
  have hpre : ∀ i : ι,
      TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage k σ
          (Multiplicative.ofAdd (Finsupp.single i 1)) =
        Multiplicative.ofAdd (Finsupp.single (π i) 1) := by
    intro i
    apply (TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage_apply_eq_iff k σ _ _).mpr
    simpa using hσ i
  refine MonoidHom.ext fun x => ?_
  obtain ⟨f, rfl⟩ := Multiplicative.ofAdd.surjective x
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [ofAdd_add, map_mul, h₁, h₂]
  | single i n =>
      have hleft : TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage k σ
          (Multiplicative.ofAdd (Finsupp.single i n)) =
          Multiplicative.ofAdd (Finsupp.single (π i) n) := by
        rw [show Finsupp.single i n = n • Finsupp.single i 1 by simp]
        rw [ofAdd_zsmul, map_zpow, hpre i]
        rw [show Finsupp.single (π i) n = n • Finsupp.single (π i) 1 by simp, ofAdd_zsmul]
      have hright : AddMonoidHom.toMultiplicative
          (permutationRepFinsupp π).toAddMonoidHom
            (Multiplicative.ofAdd (Finsupp.single i n)) =
          Multiplicative.ofAdd (Finsupp.single (π i) n) := by
        change Multiplicative.ofAdd ((permutationRepFinsupp π) (Finsupp.single i n)) =
          Multiplicative.ofAdd (Finsupp.single (π i) n)
        rw [show Finsupp.single i n = n • Finsupp.single i 1 by simp]
        rw [map_smul]
        rw [show (permutationRepFinsupp π) (Finsupp.single i 1) =
            Finsupp.single (π i) 1 by simp [permutationRepFinsupp]]
        rw [show Finsupp.single (π i) n = n • Finsupp.single (π i) 1 by simp, ofAdd_zsmul]
      exact hleft.trans hright.symm




private abbrev SplitTorusRing (k : Type u) (ι : Type u) [Field k] [Finite ι] :=
  TauCeti.FiniteTypeCommHopfAlgCat.of k (MonoidAlgebra k (Multiplicative (ι →₀ ℤ)))

private abbrev OrbitTorusRing (k : Type u) (π : Equiv.Perm ι) [Field k] :=
  TauCeti.FiniteTypeCommHopfAlgCat.of k
    (MonoidAlgebra k (Multiplicative (OrbitQuot π →₀ ℤ)))

private noncomputable def orbitQuotHom (π : Equiv.Perm ι) :
    Multiplicative (ι →₀ ℤ) →* Multiplicative (OrbitQuot π →₀ ℤ) :=
  AddMonoidHom.toMultiplicative (orbitSumF π)

private noncomputable def orbitCoordinateMap (k : Type u) [Field k] {ι : Type u} [Finite ι]
    (π : Equiv.Perm ι) : (SplitTorusRing k ι).obj ⟶ (OrbitTorusRing k π).obj :=
  _root_.CommHopfAlgCat.ofHom
    (MonoidAlgebra.mapDomainBialgHom k (orbitQuotHom π))

private theorem orbitQuotHom_comp_preimage
    (π : Equiv.Perm ι)
    (σ : SplitTorusRing k ι →ₐc[k] SplitTorusRing k ι)
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1) :
    (orbitQuotHom π).comp (TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage k σ) =
      orbitQuotHom π := by
  have hfun : (fun i : ι => Quotient.mk (MulAction.orbitRel (PermGroup π) ι) (π i)) =
      Quotient.mk (MulAction.orbitRel (PermGroup π) ι) := by
    funext i
    apply Quotient.sound
    exact ⟨⟨π, Subgroup.mem_zpowers π⟩, rfl⟩
  apply MonoidHom.ext
  intro m
  obtain ⟨a, rfl⟩ : ∃ a : ι →₀ ℤ, Multiplicative.ofAdd a = m :=
    Multiplicative.ofAdd.surjective m
  rw [MonoidHom.comp_apply, preimage_eq_permutationRep π σ hσ]
  apply Multiplicative.ofAdd.injective
  change Finsupp.mapDomain (Quotient.mk (MulAction.orbitRel (PermGroup π) ι))
      (Finsupp.mapDomain (π : ι → ι) a) =
    Finsupp.mapDomain (Quotient.mk (MulAction.orbitRel (PermGroup π) ι)) a
  rw [← Finsupp.mapDomain_comp,
    show (Quotient.mk (MulAction.orbitRel (PermGroup π) ι)) ∘ (π : ι → ι) =
      Quotient.mk (MulAction.orbitRel (PermGroup π) ι) by
        simpa [Function.comp_def] using hfun]

private theorem orbitCoordinateMap_comp_sigma
    (π : Equiv.Perm ι)
    (σ : SplitTorusRing k ι →ₐc[k] SplitTorusRing k ι)
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1) :
    (_root_.CommHopfAlgCat.ofHom σ) ≫ orbitCoordinateMap k π = orbitCoordinateMap k π := by
  apply _root_.CommHopfAlgCat.hom_ext
  change (MonoidAlgebra.mapDomainBialgHom k (orbitQuotHom π)).comp σ =
    MonoidAlgebra.mapDomainBialgHom k (orbitQuotHom π)
  rw [show σ = MonoidAlgebra.mapDomainBialgHom k
      (TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage k σ) from
    (TauCeti.MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHomPreimage k σ).symm]
  rw [← MonoidAlgebra.mapDomainBialgHom_comp, orbitQuotHom_comp_preimage π σ hσ]


private noncomputable def orbitCoordinateMapFT (π : Equiv.Perm ι) :
    SplitTorusRing k ι ⟶ OrbitTorusRing k π :=
  ObjectProperty.homMk (orbitCoordinateMap k π)

private theorem fixedHopfIdeal_le_ker_orbitCoordinateMap
    (π : Equiv.Perm ι)
    (σ : SplitTorusRing k ι →ₐc[k] SplitTorusRing k ι)
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1) :
    (fixedHopfIdeal (SplitTorusRing k ι) σ).toIdeal ≤
      RingHom.ker (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (orbitCoordinateMapFT π)).toAlgHom.toRingHom := by
  rw [fixedHopfIdeal, TauCeti.HopfIdeal.equalizer_le_ker_iff]
  intro a
  have h := congrArg (fun φ : (SplitTorusRing k ι).obj ⟶ (OrbitTorusRing k π).obj =>
    φ.hom a) (orbitCoordinateMap_comp_sigma π σ hσ)
  change (orbitCoordinateMap k π).hom (σ a) = (orbitCoordinateMap k π).hom a
  exact h

private noncomputable def fixedCoordinateToOrbit
    (π : Equiv.Perm ι)
    (σ : SplitTorusRing k ι →ₐc[k] SplitTorusRing k ι)
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1) :
    fixedCoordinate (SplitTorusRing k ι) σ ⟶ OrbitTorusRing k π :=
  TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient (fixedHopfIdeal (SplitTorusRing k ι) σ)
    (orbitCoordinateMapFT π) (fixedHopfIdeal_le_ker_orbitCoordinateMap π σ hσ)

private theorem fixedCoordinateToOrbit_point_surjective
    (π : Equiv.Perm ι)
    (σ : SplitTorusRing k ι →ₐc[k] SplitTorusRing k ι)
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1)
    (x : TauCeti.HopfAlgebra.points (R := k)
      (H := fixedCoordinate (SplitTorusRing k ι) σ) (CommAlgCat.of k k)) :
    ∃ t : TauCeti.HopfAlgebra.points (R := k)
      (H := OrbitTorusRing k π) (CommAlgCat.of k k),
      TauCeti.AlgHom.mapDomain (fixedCoordinateToOrbit π σ hσ).hom.hom t = x := by
  classical
  let T := SplitTorusRing k ι
  let O := OrbitTorusRing k π
  let F := fixedCoordinate T σ
  let qF : T ⟶ F := TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient T (fixedHopfIdeal T σ)
  let y : WithConv (MonoidAlgebra k (Multiplicative (ι →₀ ℤ)) →ₐ[k] k) :=
    TauCeti.AlgHom.mapDomain qF.hom.hom x
  have hy : TauCeti.AlgHom.mapDomain σ y = y :=
    fixedCoordinate_point_fixed T σ x
  let u : ι → kˣ := TauCeti.SplitTorus.pointsMulEquiv (R := k) (A := k) y
  have hu : ∀ i : ι, u (π i) = u i := by
    intro i
    have h := congrArg (fun p : WithConv
        (MonoidAlgebra k (Multiplicative (ι →₀ ℤ)) →ₐ[k] k) =>
          p.ofConv (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1)) hy
    rw [TauCeti.AlgHom.mapDomain_apply_apply] at h
    rw [hσ i] at h
    dsimp only [u]
    apply Units.ext
    rw [TauCeti.SplitTorus.pointsMulEquiv_apply_coe,
      TauCeti.SplitTorus.pointsMulEquiv_apply_coe]
    exact h
  have hu_const : ∀ i j : ι, MulAction.orbitRel (PermGroup π) ι i j → u i = u j := by
    intro i j hij
    rw [Equiv.Perm.orbitRel_zpowers_apply] at hij
    exact Equiv.Perm.SameCycle.apply_eq_of_apply_eq hij hu
  let v : OrbitQuot π → kˣ := Quotient.lift u hu_const
  let t : TauCeti.HopfAlgebra.points (R := k) (H := O) (CommAlgCat.of k k) :=
    (TauCeti.SplitTorus.pointsMulEquiv (R := k) (A := k)
      (σ := OrbitQuot π)).symm v
  have hq_point : TauCeti.AlgHom.mapDomain (orbitCoordinateMap k π).hom t = y := by
    apply (TauCeti.SplitTorus.pointsMulEquiv (R := k) (A := k) (σ := ι)).injective
    funext i
    apply Units.ext
    rw [TauCeti.SplitTorus.pointsMulEquiv_apply_coe]
    rw [TauCeti.AlgHom.mapDomain_apply_apply]
    rw [show (orbitCoordinateMap k π).hom
        (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
      MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.single
          (Quotient.mk (MulAction.orbitRel (PermGroup π) ι) i) 1)) 1 by
        simp [orbitCoordinateMap, orbitQuotHom]]
    dsimp only [t, v]
    rw [TauCeti.SplitTorus.pointsMulEquiv_symm_apply_single]
    rw [Quotient.lift_mk]
  refine ⟨t, ?_⟩
  apply TauCeti.CommHopfAlgCat.mapPointsFunctor_app_injective_of_surjective
    qF.hom (TauCeti.CommHopfAlgCat.mkQuotient_surjective T.obj (fixedHopfIdeal T σ))
  simp only [TauCeti.CommHopfAlgCat.mapPointsFunctor_app_apply]
  have hcomp : (fixedCoordinateToOrbit π σ hσ).hom.hom.toAlgHom.comp
        qF.hom.hom.toAlgHom = (orbitCoordinateMap k π).hom.toAlgHom := by
    have h := TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_comp_liftQuotient
      (fixedHopfIdeal T σ) (orbitCoordinateMapFT π)
      (fixedHopfIdeal_le_ker_orbitCoordinateMap π σ hσ)
    exact congrArg (fun f : T ⟶ O => f.hom.hom.toAlgHom) h
  apply WithConv.ofConv_injective
  simp only [TauCeti.AlgHom.mapDomain_apply]
  rw [AlgHom.comp_assoc, hcomp]
  have hq := congrArg WithConv.ofConv hq_point
  rw [TauCeti.AlgHom.mapDomain_apply] at hq
  change t.ofConv.comp (orbitCoordinateMap k π).hom.toAlgHom = y.ofConv at hq
  rw [hq]
  dsimp only [y]
  rw [TauCeti.AlgHom.mapDomain_apply]


theorem connectedSpace_fixedCoordinate_permutation_torus
    [IsAlgClosed k]
    (π : Equiv.Perm ι)
    (σ : TauCeti.FiniteTypeCommHopfAlgCat.of k
        (MonoidAlgebra k (Multiplicative (ι →₀ ℤ))) →ₐc[k]
      TauCeti.FiniteTypeCommHopfAlgCat.of k
        (MonoidAlgebra k (Multiplicative (ι →₀ ℤ))))
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1) :
    ConnectedSpace (PrimeSpectrum (fixedCoordinate
      (TauCeti.FiniteTypeCommHopfAlgCat.of k
        (MonoidAlgebra k (Multiplicative (ι →₀ ℤ)))) σ)) := by
  classical
  let T := SplitTorusRing k ι
  let O := OrbitTorusRing k π
  let F := fixedCoordinate T σ
  have hO : ConnectedSpace (PrimeSpectrum O) := by
    have hsplit : TauCeti.splitTorusCommHopfAlgProperty k O := by
      change TauCeti.splitTorusCommHopfAlgProperty k
        (TauCeti.DiagonalizableGroup.coordinateRing k
          (TauCeti.SplitTorus.characterGroup (OrbitQuot π)))
      exact TauCeti.splitTorusCommHopfAlgProperty_coordinateRing k
        (TauCeti.SplitTorus.characterGroup (OrbitQuot π))
    have htor : TauCeti.torusCommHopfAlgProperty k O :=
      hsplit.torus k O
    exact (TauCeti.torusCommHopfAlgProperty.geometricallyConnected k O htor).connectedSpace k O.obj
  apply connectedSpace_of_componentPointsHom_eq_one F
  intro x
  obtain ⟨t, ht⟩ := fixedCoordinateToOrbit_point_surjective π σ hσ x
  rw [← ht]
  exact componentPointsHom_map_eq_one F O (fixedCoordinateToOrbit π σ hσ).hom hO t

end CFSG.LieType.AlgebraicGroups
