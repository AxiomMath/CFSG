module

public import CFSG.LieType.AlgebraicGroups.UnipotentCoprimeTorsor
public import CFSG.LieType.AlgebraicGroups.SplitKernelGeometry
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Torus.Reductive
public import CFSG.GroupTheory.FiniteNilpotentCentralizerLift
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup

public noncomputable section

open CategoryTheory WithConv TauCeti

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem quotientPointsSubgroup_vanishingIdeal_ker_mapDomain
    (H T : FiniteTypeCommHopfAlgCat.{u,u} k) (p : T →ₐc[k] H) :
    CommHopfAlgCat.quotientPointsSubgroup H.obj
      (HopfIdeal.vanishingIdeal (AlgHom.mapDomain (A := k) p).ker)
      (CommAlgCat.of k k) = (AlgHom.mapDomain (A := k) p).ker := by
  let K := (AlgHom.mapDomain (A := k) p).ker
  let I := CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p)
  have hI : CommHopfAlgCat.quotientPointsSubgroup H.obj I
      (CommAlgCat.of k k) = K := by
    exact CommHopfAlgCat.quotientPointsSubgroup_kernelHopfIdeal_eq_ker_mapPointsFunctor
      (_root_.CommHopfAlgCat.ofHom p) (CommAlgCat.of k k)
  apply le_antisymm
  · have hle : I ≤ HopfIdeal.vanishingIdeal K :=
      (HopfIdeal.le_vanishingIdeal_iff K I).mpr hI.symm.le
    exact (CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj hle
      (CommAlgCat.of k k)).trans hI.le
  · exact (HopfIdeal.le_vanishingIdeal_iff K (HopfIdeal.vanishingIdeal K)).mp le_rfl

theorem nilpotent_and_pow_bijective_ker_of_unipotent
    (H T : FiniteTypeCommHopfAlgCat.{u,u} k) (p : T →ₐc[k] H)
    (hker : ∀ g : WithConv (H →ₐ[k] k),
      AlgHom.mapDomain p g = 1 → HopfAlgebra.IsUnipotentPoint g)
    {m : ℕ} (hm : (m : k) ≠ 0) :
    Group.IsNilpotent (AlgHom.mapDomain (A := k) p).ker ∧
      Function.Bijective (fun g : (AlgHom.mapDomain (A := k) p).ker => g ^ m) := by
  let N := (AlgHom.mapDomain (A := k) p).ker
  let I := HopfIdeal.vanishingIdeal N
  let U := FiniteTypeCommHopfAlgCat.quotient H I
  let q : H →ₐc[k] U := (CommHopfAlgCat.mkQuotient H.obj I).hom
  have hUN : CommHopfAlgCat.quotientPointsSubgroup H.obj I
      (CommAlgCat.of k k) = N := quotientPointsSubgroup_vanishingIdeal_ker_mapDomain H T p
  have hU : ∀ u : WithConv (U →ₐ[k] k), HopfAlgebra.IsUnipotentPoint u := by
    intro u
    have hu : AlgHom.mapDomain q u ∈ N := by
      rw [← hUN]
      exact CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj I
        (CommAlgCat.of k k) u
    have h := hker (AlgHom.mapDomain q u) hu
    exact (HopfAlgebra.isUnipotentPoint_mapDomain_iff_of_surjective q
      (CommHopfAlgCat.mkQuotient_surjective H.obj I) u).mp h
  let : IsReduced U := inferInstanceAs (IsReduced (CommHopfAlgCat.quotient H.obj I))
  let : Group.IsNilpotent (WithConv (U →ₐ[k] k)) :=
    isNilpotent_points_of_forall_isUnipotentPoint U hU
  let e₀ := CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)
  let e : WithConv (U →ₐ[k] k) ≃* N :=
    (MulEquiv.ofBijective e₀.hom.hom
      (ConcreteCategory.bijective_of_isIso e₀.hom)).trans (MulEquiv.subgroupCongr hUN)
  have hnil : Group.IsNilpotent N := Group.nilpotent_of_mulEquiv e
  have hp := pow_bijective_of_unipotent U hU hm
  refine ⟨hnil, ?_⟩
  constructor
  · intro x y hxy
    apply e.symm.injective
    apply hp.1
    simpa using congrArg e.symm hxy
  · intro y
    obtain ⟨x, hx⟩ := hp.2 (e.symm y)
    refine ⟨e x, ?_⟩
    change x ^ m = e.symm y at hx
    change (e x) ^ m = y
    rw [← map_pow, hx, e.apply_symm_apply]

theorem exists_finite_torus_lift_centralizer_surjective
    (H T : FiniteTypeCommHopfAlgCat.{u,u} k)
    (hT : torusCommHopfAlgProperty k T) (p : T →ₐc[k] H)
    (hps : Function.Surjective (AlgHom.mapDomain (A := k) p))
    (hker : ∀ g : WithConv (H →ₐ[k] k),
      AlgHom.mapDomain p g = 1 → HopfAlgebra.IsUnipotentPoint g)
    (F : Subgroup (WithConv (T →ₐ[k] k))) [Finite F]
    (hF : (Nat.card F : k) ≠ 0) :
    ∃ (s : F →* WithConv (H →ₐ[k] k)) (L : Subgroup (WithConv (H →ₐ[k] k))),
      (∀ f : F, AlgHom.mapDomain p (s f) = (f : WithConv (T →ₐ[k] k))) ∧
      Function.Injective s ∧ L = s.range ∧ Finite L ∧
      Subgroup.map (AlgHom.mapDomain (A := k) p)
        (Subgroup.centralizer (L : Set (WithConv (H →ₐ[k] k)))) = ⊤ := by
  let : Coalgebra.IsCocomm k T := hT.isCocomm k T
  let : CommGroup (WithConv (T →ₐ[k] k)) := inferInstance
  obtain ⟨hnil, hdiv⟩ := nilpotent_and_pow_bijective_ker_of_unipotent H T p hker hF
  let := hnil
  exact CFSG.GroupTheory.exists_finite_section_centralizer_surjective
    (AlgHom.mapDomain (A := k) p) hps hdiv

theorem kernelHopfIdeal_eq_unipotentRadical_of_torus_section
    (H T : FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)]
    (hT : torusCommHopfAlgProperty k T)
    (p : T →ₐc[k] H) (hp : Function.Injective p)
    (hker : ∀ g : WithConv (H →ₐ[k] k),
      AlgHom.mapDomain p g = 1 → HopfAlgebra.IsUnipotentPoint g)
    (j : H →ₐc[k] T) (hj : j.comp p = BialgHom.id k T) :
    CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p) =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H := by
  let I := CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p)
  let U := FiniteTypeCommHopfAlgCat.quotient H I
  let : IsReduced U := splitKernelQuotient_isReduced p j hj
  have hsm : Algebra.Smooth k U :=
    (smoothCommHopfAlgProperty_iff U.obj).mp (splitKernelQuotient_smooth p j hj)
  have hc : geometricallyConnectedCommHopfAlgProperty k U.obj :=
    splitKernelQuotient_geometricallyConnected p j hj
  have hU : ∀ u : WithConv (U →ₐ[k] k), HopfAlgebra.IsUnipotentPoint u := by
    intro u
    let q : H →ₐc[k] U := (CommHopfAlgCat.mkQuotient H.obj I).hom
    have hpoint : AlgHom.mapDomain p (AlgHom.mapDomain q u) = 1 := by
      apply (CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff
        (_root_.CommHopfAlgCat.ofHom p) (CommAlgCat.of k k) _).mpr
      exact CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj I
        (CommAlgCat.of k k) u
    exact (HopfAlgebra.isUnipotentPoint_mapDomain_iff_of_surjective q
      (CommHopfAlgCat.mkQuotient_surjective H.obj I) u).mp
        (hker (AlgHom.mapDomain q u) hpoint)
  have hgeom : geometricallyUnipotentPointsCommHopfAlgProperty k U.obj :=
    (geometricallyUnipotentPointsCommHopfAlgProperty.iff_forall_isUnipotentPoint k).mpr hU
  have hcandidate : HopfIdeal.IsUnipotentRadicalCandidate H I :=
    HopfIdeal.IsUnipotentRadicalCandidate.mk
      (CommHopfAlgCat.isNormal_kernelHopfIdeal _) hc
      ((smoothUnipotentCommHopfAlgProperty_iff k U).mpr ⟨hsm,
        (geometricallyUnipotentPointsCommHopfAlgProperty_iff k U.obj).mp hgeom⟩)
  exact (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_reductive
    H T hT.reductive (_root_.CommHopfAlgCat.ofHom p) hp hcandidate).symm

end CFSG.LieType.AlgebraicGroups
