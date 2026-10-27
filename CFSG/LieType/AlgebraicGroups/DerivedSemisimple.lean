module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Construction
public import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Isomorphism
import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.Invariants
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Faithful
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Reduced
import TauCeti.Algebra.AlgebraicGroup.Derived.PointClosure
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import TauCeti.RingTheory.FiniteType.Tensor.Product
import TauCeti.RingTheory.Smooth.GeometricallyReduced

public section

noncomputable section

open CategoryTheory WithConv TauCeti
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.DerivedSemisimple

universe u

section Normality

variable {K : Type u} [Field K] {H : Type u} [CommRing H] [HopfAlgebra K H]

theorem le_conjugate_of_isNormal {I : HopfIdeal K H} (hI : I.IsNormal)
    (g : WithConv (H →ₐ[K] K)) : I ≤ I.conjugate g := by
  intro x hx
  rw [HopfIdeal.mem_conjugate]
  let A : CommAlgCat K := CommAlgCat.of K (H ⧸ I.toIdeal)
  let y : HopfAlgebra.points (R := K) (H := H) A := toConv (Ideal.Quotient.mkₐ K I.toIdeal)
  have hy : y ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of K H) I A := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro h hh
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr hh)
  have hnorm := CommHopfAlgCat.quotientPointsSubgroup_normal (_root_.CommHopfAlgCat.of K H) I hI A
  have hconj := hnorm.conj_mem y hy (AlgHom.mapValue (H := H) (Algebra.ofId K A) g)
  rw [← HopfAlgebra.comp_pointConjugationAlgHom] at hconj
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hconj
  have h0 := hconj x hx
  simp only [AlgHom.comp_apply, y] at h0
  exact HopfIdeal.mem_toIdeal.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)

theorem conjugate_eq_of_isNormal {I : HopfIdeal K H} (hI : I.IsNormal)
    (g : WithConv (H →ₐ[K] K)) : I.conjugate g = I := by
  apply le_antisymm _ (le_conjugate_of_isNormal hI g)
  have h := HopfIdeal.conjugate_mono g (le_conjugate_of_isNormal hI g⁻¹)
  rwa [HopfIdeal.conjugate_conjugate_inv] at h

variable [IsAlgClosed K] [Algebra.FiniteType K H]

theorem isNormal_of_forall_le_conjugate (I : HopfIdeal K H)
    [IsReduced (H ⊗[K] (H ⧸ I.toIdeal))]
    (hI : ∀ g : WithConv (H →ₐ[K] K), I ≤ I.conjugate g) : I.IsNormal := by
  let _ : Algebra.FiniteType K (H ⊗[K] (H ⧸ I.toIdeal)) :=
    FiniteTypeCommHopfAlgCat.tensorProduct_finiteType H (H ⧸ I.toIdeal)
  rw [HopfIdeal.isNormal_iff_conjugation_mem]
  intro x hx
  rw [← HopfIdeal.ker_tensorProduct_map_id_quotient, RingHom.mem_ker]
  apply eq_of_forall_algHom_apply_eq (k := K) (K := K)
  intro f
  let g : H →ₐ[K] K := f.comp Algebra.TensorProduct.includeLeft
  let n : H →ₐ[K] K :=
    (f.comp Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ K I.toIdeal)
  have hf : f.comp (Algebra.TensorProduct.map (AlgHom.id K H)
      (Ideal.Quotient.mkₐ K I.toIdeal)) = Algebra.TensorProduct.productMap g n := by
    apply Algebra.TensorProduct.ext
    · ext a; simp [g]
    · ext a; simp [n]
  have hprod := congrArg (fun φ : H →ₐ[K] K => φ x)
    (HopfAlgebra.productMap_comp_conjugationAlgHom (toConv g) (toConv n))
  have hpc := HopfAlgebra.comp_pointConjugationAlgHom (A := K) (toConv g) (toConv n)
  have hcx : HopfAlgebra.pointConjugationAlgHom (toConv g) x ∈ I :=
    HopfIdeal.mem_conjugate.mp (hI (toConv g) hx)
  have hnx : n (HopfAlgebra.pointConjugationAlgHom (toConv g) x) = 0 := by
    simp only [n, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr hcx), map_zero]
  have hid : AlgHom.mapValue (H := H) (Algebra.ofId K K) (toConv g) = toConv g := by
    apply WithConv.ofConv_injective
    ext a
    simp
  have key : (toConv g * toConv n * (toConv g)⁻¹ : WithConv (H →ₐ[K] K)).ofConv x = 0 := by
    rw [hid] at hpc
    rw [← hpc]
    simpa using hnx
  simp only [map_zero]
  rw [← AlgHom.comp_apply, hf]
  simpa using hprod.trans key

end Normality


section Naturality

variable {R H M N : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M] [AddCommMonoid N] [Module R N] [Comodule R H N]

theorem hom_basePointsRepresentation (f : Comodule.Hom R H M N) (g : WithConv (H →ₐ[R] R))
    (m : M) :
    f (Comodule.basePointsRepresentation M g m) = Comodule.basePointsRepresentation N g (f m) := by
  rw [Comodule.basePointsRepresentation_apply, Comodule.basePointsRepresentation_apply,
    Comodule.endOfPoint_tmul, Comodule.endOfPoint_tmul, ← Comodule.Hom.map_coact_apply,
    ← Comodule.Hom.coe_toLinearMap]
  generalize f.toLinearMap = φ
  induction Comodule.coact (R := R) (C := H) (M := M) m using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, smul_add] at hx hy ⊢; rw [hx, hy]

end Naturality

section Radical

variable {K : Type u} [Field K] (G : FiniteTypeCommHopfAlgCat.{u,u} K) (J : HopfIdeal K G)

def radicalPullback : HopfIdeal K G :=
  (FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal
      (FiniteTypeCommHopfAlgCat.quotient G J)).comapOfSurjective
    (CommHopfAlgCat.mkQuotient G.obj J).hom (CommHopfAlgCat.mkQuotient_surjective G.obj J)

theorem mem_radicalPullback {x : G} :
    x ∈ radicalPullback G J ↔
      (CommHopfAlgCat.mkQuotient G.obj J).hom x ∈
        FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal
          (FiniteTypeCommHopfAlgCat.quotient G J) :=
  HopfIdeal.mem_comapOfSurjective

theorem radicalPullback_le_conjugate (hJ : J.IsNormal) (g : WithConv (G →ₐ[K] K)) :
    radicalPullback G J ≤ (radicalPullback G J).conjugate g := by
  let e : G.obj ≅ G.obj := _root_.CommHopfAlgCat.isoMk (HopfAlgebra.pointConjugationBialgEquiv g)
  have he : ∀ y : G, e.hom.hom y = HopfAlgebra.pointConjugationAlgHom g y := by
    intro y
    have h1 := congrArg (fun f : G →ₐ[K] G => f y)
      (HopfAlgebra.pointConjugationBialgEquiv_toAlgHom g)
    simp only [BialgHom.coe_toAlgHom] at h1
    rw [← h1]
    simp [e]
  have hJe : J.comapOfSurjective e.hom.hom
      (ConcreteCategory.bijective_of_isIso e.hom).2 = J := by
    ext y
    rw [HopfIdeal.mem_comapOfSurjective, he, ← HopfIdeal.mem_conjugate,
      conjugate_eq_of_isNormal hJ]
  let φ := CommHopfAlgCat.quotientIsoOfComapEq e J hJe
  let φ' : FiniteTypeCommHopfAlgCat.quotient G J ≅ FiniteTypeCommHopfAlgCat.quotient G J :=
    ObjectProperty.isoMk _ φ
  have hR := FiniteTypeCommHopfAlgCat.comapOfSurjective_solvableRadicalDefiningIdeal φ'
  intro x hx
  rw [HopfIdeal.mem_conjugate, mem_radicalPullback]
  rw [mem_radicalPullback] at hx
  have hcomm := congrArg (fun f => f.hom x)
    (CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom e J hJe)
  rw [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.comp_apply] at hcomm
  rw [← he, ← hcomm]
  rw [← hR, HopfIdeal.mem_comapOfSurjective] at hx
  exact hx

end Radical

section Unipotence

variable {K : Type u} [Field K] [IsAlgClosed K]
variable (G : FiniteTypeCommHopfAlgCat.{u,u} K) [IsReduced G] [ConnectedSpace (PrimeSpectrum G)]
variable (I : HopfIdeal K G)

abbrev ratPoints : Subgroup (WithConv (G →ₐ[K] K)) :=
  CommHopfAlgCat.quotientPointsSubgroup G.obj I (CommAlgCat.of K K)

theorem exists_ne_zero_forall_fixed (hI : I.IsNormal)
    (hder : CommHopfAlgCat.derivedDefiningIdeal (R := K) G ≤ I)
    [IsReduced (G ⧸ I.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty K (CommHopfAlgCat.quotient G.obj I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty K (CommHopfAlgCat.quotient G.obj I))
    (W : Type u) [AddCommGroup W] [Module K W] [Comodule K G W] [FiniteDimensional K W]
    [Nontrivial W] :
    ∃ w : W, w ≠ 0 ∧ ∀ s ∈ ratPoints G I, Comodule.basePointsRepresentation W s w = w := by
  classical
  let π : G →ₐc[K] (G ⧸ I.toIdeal) := (CommHopfAlgCat.mkQuotient G.obj I).hom
  have hπ : Function.Surjective π := CommHopfAlgCat.mkQuotient_surjective G.obj I
  let : Comodule K (G ⧸ I.toIdeal) W := Comodule.Corestrict π.toCoalgHom
  obtain ⟨v, c, hv0, hc, hcoact⟩ := Comodule.hasNonzeroWeightVector_iff.mp
    (Comodule.hasNonzeroWeightVector_of_geometricallySolvable (k := K) (H := G ⧸ I.toIdeal)
      (M := W) hconn hsolv)
  obtain ⟨c', rfl⟩ := hπ c
  have hact : ∀ s ∈ ratPoints G I,
      Comodule.basePointsRepresentation W s v = s.ofConv c' • v := by
    intro s hs
    have hker : ∀ x ∈ I.toIdeal, s.ofConv x = 0 := fun x hx =>
      (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hs x
        (HopfIdeal.mem_toIdeal.mp hx)
    let t : WithConv ((G ⧸ I.toIdeal) →ₐ[K] K) :=
      toConv (Ideal.Quotient.liftₐ I.toIdeal s.ofConv hker)
    have hts : AlgHom.mapDomain π t = s := by
      apply WithConv.ofConv_injective
      ext x
      simp only [AlgHom.mapDomain_apply, t, π, ofConv_toConv, AlgHom.comp_apply,
        BialgHom.coe_toAlgHom]
      exact Ideal.Quotient.lift_mk _ _ _
    have h := congrArg (fun f => f v)
      (Comodule.basePointsRepresentation_corestrict (M := W) π t)
    rw [hts] at h
    rw [← h, Comodule.basePointsRepresentation_apply, Comodule.endOfPoint_tmul, hcoact]
    have htc : t.ofConv (π c') = s.ofConv c' := by
      rw [← hts, AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
      rfl
    simp only [LinearMap.lTensor_tmul, TensorProduct.comm_tmul, one_smul, TensorProduct.lid_tmul,
      AlgHom.toLinearMap_apply, htc]
  let N := ratPoints G I
  have : N.Normal :=
    CommHopfAlgCat.quotientPointsSubgroup_normal G.obj I hI (CommAlgCat.of K K)
  let ρN : N →* Module.End K W := (Comodule.basePointsRepresentation W).comp N.subtype
  have hmem : ∀ n : N, v ∈ (ρN n).eigenspace ((n : WithConv (G →ₐ[K] K)).ofConv c') := by
    intro n
    rw [Module.End.mem_eigenspace_iff]
    exact hact n n.2
  let χ : N →* Kˣ := MonoidHom.unitHomOfJointEigenvector ρN
    (fun n => (n : WithConv (G →ₐ[K] K)).ofConv c') v hv0 hmem
  have hχ : ∀ n : N, (χ n : K) = (n : WithConv (G →ₐ[K] K)).ofConv c' := fun n =>
    MonoidHom.unitHomOfJointEigenvector_apply _ _ _ _ _ n
  let χw : NonzeroJointWeight N (Comodule.basePointsRepresentation W) := ⟨χ, by
    rw [Submodule.ne_bot_iff]
    refine ⟨v, ?_, hv0⟩
    rw [Submodule.mem_iInf]
    intro n
    rw [hχ]
    exact hmem n⟩
  let U := Comodule.normalWeightSubcomodule N χw
  have hUne : U ≠ ⊥ := Comodule.normalWeightSubcomodule_ne_bot N χw
  have hscalar : ∀ n : N, ∀ u : U,
      Comodule.basePointsRepresentation U (n : WithConv (G →ₐ[K] K)) u = (χ n : K) • u := by
    intro n u
    apply Subtype.ext
    have h1 := hom_basePointsRepresentation (Subcomodule.subtype U) (n : WithConv _) u
    rw [Subcomodule.subtype_apply, Subcomodule.subtype_apply] at h1
    rw [h1, Submodule.coe_smul]
    exact (Comodule.mem_normalWeightSubcomodule N χw (u : W)).mp u.2 n
  let : AddCommGroup U := Module.addCommMonoidToAddCommGroup K
  have : Module.Free K U := Module.Free.of_divisionRing K U
  have : Module.Finite K U := U.finite
  let b := Module.finBasis K U
  let a : G := (Comodule.coefficientMatrix (C := G) b).det
  have hdet : ∀ g : WithConv (G →ₐ[K] K),
      LinearMap.det (Comodule.basePointsRepresentation U g) = g.ofConv a := by
    intro g
    have hconj : Comodule.basePointsRepresentation U g =
        (TensorProduct.lid K U).toLinearMap ∘ₗ (Comodule.endOfPoint U g.ofConv) ∘ₗ
          (TensorProduct.lid K U).symm.toLinearMap := by
      ext u
      simp [Comodule.basePointsRepresentation_apply]
    rw [hconj, LinearMap.det_conj, ← LinearMap.det_toMatrix (b.baseChange K),
      Comodule.toMatrix_endOfPoint]
    simp only [a, AlgHom.map_det, AlgHom.mapMatrix_apply]
  let Δ : WithConv (G →ₐ[K] K) →* Kˣ :=
    (LinearMap.det.comp (Comodule.basePointsRepresentation U)).toHomUnits
  have hΔ : ∀ g, (Δ g : K) = g.ofConv a := fun g => hdet g
  have haJ : a - 1 ∈ CommHopfAlgCat.derivedDefiningIdeal (R := K) G := by
    rw [CommHopfAlgCat.mem_derivedDefiningIdeal_iff_forall_commutator_apply_eq_zero]
    intro g
    have hg : (g : WithConv (G →ₐ[K] K)) ∈ Δ.ker :=
      Abelianization.commutator_subset_ker Δ g.2
    rw [MonoidHom.mem_ker] at hg
    rw [map_sub, map_one, ← hΔ, hg, Units.val_one, sub_self]
  have hN1 : ∀ n : N, ((χ n : K)) ^ Module.finrank K U = 1 := by
    intro n
    have h1 : (n : WithConv (G →ₐ[K] K)).ofConv (a - 1) = 0 :=
      (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp n.2 _ (hder haJ)
    rw [map_sub, map_one, sub_eq_zero, ← hdet] at h1
    have hsm : Comodule.basePointsRepresentation U (n : WithConv (G →ₐ[K] K)) =
        (χ n : K) • (1 : Module.End K U) := by
      ext u
      simp [hscalar n u]
    rw [hsm, LinearMap.det_smul, map_one, mul_one] at h1
    exact h1
  have hd : 0 < Module.finrank K U := by
    obtain ⟨m, hm, hm0⟩ := Subcomodule.ne_bot_iff.mp hUne
    have : Nontrivial U := ⟨⟨⟨m, hm⟩, 0, fun h => hm0 (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  have : ConnectedSpace (PrimeSpectrum (G ⧸ I.toIdeal)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace K
      (CommHopfAlgCat.quotient G.obj I) hconn
  have hfin : (Set.range fun f : (G ⧸ I.toIdeal) →ₐ[K] K ↦ f (π c')).Finite := by
    apply (Polynomial.nthRootsFinset (Module.finrank K U) (1 : K)).finite_toSet.subset
    rintro _ ⟨f, rfl⟩
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hd]
    let n : N := ⟨toConv (f.comp π.toAlgHom), by
      rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
      intro x hx
      simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom]
      rw [(CommHopfAlgCat.mkQuotient_eq_zero_iff G.obj I x).2 hx, map_zero]⟩
    have := hN1 n
    rw [hχ] at this
    simpa [n] using this
  have hc1 : π c' = 1 := by
    rw [eq_algebraMap_of_finite_range_eval (π c') hfin (Bialgebra.counitAlgHom K _)]
    simp [hc.counit_eq_one]
  have hc'I : c' - 1 ∈ I := by
    apply (CommHopfAlgCat.mkQuotient_eq_zero_iff G.obj I _).1
    change π (c' - 1) = 0
    rw [map_sub, map_one, hc1, sub_self]
  refine ⟨v, hv0, fun s hs => ?_⟩
  rw [hact s hs]
  have h0 : s.ofConv (c' - 1) = 0 :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hs _ hc'I
  rw [map_sub, map_one, sub_eq_zero] at h0
  rw [h0, one_smul]

theorem isNilpotent_sub_one_of_le_derived (hI : I.IsNormal)
    (hder : CommHopfAlgCat.derivedDefiningIdeal (R := K) G ≤ I)
    [IsReduced (G ⧸ I.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty K (CommHopfAlgCat.quotient G.obj I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty K (CommHopfAlgCat.quotient G.obj I))
    (n : ℕ) (W : Type u) [AddCommGroup W] [Module K W] [Comodule K G W] [FiniteDimensional K W]
    (hn : Module.finrank K W = n) (s : WithConv (G →ₐ[K] K)) (hs : s ∈ ratPoints G I) :
    IsNilpotent (Comodule.basePointsRepresentation W s - 1) := by
  induction n using Nat.strong_induction_on generalizing W with
  | _ n ih =>
  rcases subsingleton_or_nontrivial W with hW | hW
  · exact ⟨1, Subsingleton.elim _ _⟩
  obtain ⟨w, hw0, hw⟩ := exists_ne_zero_forall_fixed G I hI hder hconn hsolv W
  let F : Subcomodule K G W :=
    Subcomodule.ofEndOfPointStable (K := K) (HopfIdeal.basePointFixedSubmodule W I)
      (fun g m hm => by
        simpa using HopfIdeal.IsNormal.endOfPoint_one_tmul_mem_basePointFixedSubmodule_baseChange
          hI (toConv g) hm)
  have hmemF : ∀ x, x ∈ F ↔ x ∈ HopfIdeal.basePointFixedSubmodule W I := fun x => by
    rw [← Subcomodule.mem_toSubmodule, Subcomodule.ofEndOfPointStable_toSubmodule]
  have hF : ∀ x ∈ F, Comodule.basePointsRepresentation W s x = x := by
    intro x hx
    exact (HopfIdeal.mem_basePointFixedSubmodule I x).mp ((hmemF x).mp hx) ⟨s, hs⟩
  have hwF : w ∈ F := by
    rw [hmemF, HopfIdeal.mem_basePointFixedSubmodule]
    intro t
    exact hw t t.2
  have hFne : F.toSubmodule ≠ ⊥ := by
    intro h
    have : w ∈ F.toSubmodule := Subcomodule.mem_toSubmodule.mpr hwF
    rw [h, Submodule.mem_bot] at this
    exact hw0 this
  have hlt : Module.finrank K (W ⧸ F.toSubmodule) < n := by
    have h1 := Submodule.finrank_quotient_add_finrank F.toSubmodule
    have h2 : Module.finrank K F.toSubmodule ≠ 0 := by
      rw [ne_eq, Submodule.finrank_eq_zero]
      exact hFne
    omega
  obtain ⟨m, hm⟩ := ih _ hlt (W ⧸ F.toSubmodule) rfl
  have hstep : ∀ y : W, F.mkQ ((Comodule.basePointsRepresentation W s - 1) y) =
      (Comodule.basePointsRepresentation (W ⧸ F.toSubmodule) s - 1) (F.mkQ y) := by
    intro y
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      ← hom_basePointsRepresentation F.mkQ s y, Subcomodule.mkQ_apply, Subcomodule.mkQ_apply,
      Subcomodule.mkQ_apply, Submodule.Quotient.mk_sub]
  have hcomm : ∀ (j : ℕ) (y : W),
      F.mkQ (((Comodule.basePointsRepresentation W s - 1) ^ j) y) =
        ((Comodule.basePointsRepresentation (W ⧸ F.toSubmodule) s - 1) ^ j) (F.mkQ y) := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ihj =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ihj, hstep]
  refine ⟨m + 1, ?_⟩
  ext x
  rw [pow_succ', Module.End.mul_apply, LinearMap.zero_apply]
  have hxF : ((Comodule.basePointsRepresentation W s - 1) ^ m) x ∈ F := by
    rw [← Subcomodule.mkQ_eq_zero_iff, hcomm, hm, LinearMap.zero_apply]
  rw [LinearMap.sub_apply, Module.End.one_apply, hF _ hxF, sub_self]

theorem smoothUnipotent_of_le_derived (hI : I.IsNormal)
    (hder : CommHopfAlgCat.derivedDefiningIdeal (R := K) G ≤ I)
    (hconn : geometricallyConnectedCommHopfAlgProperty K (CommHopfAlgCat.quotient G.obj I))
    (hsm : Algebra.Smooth K (G ⧸ I.toIdeal))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty K (CommHopfAlgCat.quotient G.obj I)) :
    smoothUnipotentCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.quotient G I) := by
  have : IsReduced (G ⧸ I.toIdeal) := TauCeti.isReduced_of_smooth K _
  rw [smoothUnipotentCommHopfAlgProperty.iff_smooth_and_forall_isUnipotentPoint K]
  refine ⟨hsm, fun t => ?_⟩
  obtain ⟨V, d, b, hb⟩ := Comodule.exists_coordinateBialgHom_surjective (k := K) (H := G)
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  have : Module.Free K V := Module.Free.of_divisionRing K V
  have : Module.Finite K V := Module.Finite.of_basis b
  have hV : Comodule.IsFaithful (k := K) (H := G) (V := V) := by
    rw [Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b,
      Comodule.isClosedImmersion_coordinateGroupSchemeHom_iff]
    exact hb
  let π : G →ₐc[K] (G ⧸ I.toIdeal) := (CommHopfAlgCat.mkQuotient G.obj I).hom
  have hπ : Function.Surjective π := CommHopfAlgCat.mkQuotient_surjective G.obj I
  let : Comodule K (G ⧸ I.toIdeal) V := Comodule.Corestrict π.toCoalgHom
  have hVQ : Comodule.IsFaithful (k := K) (H := G ⧸ I.toIdeal) (V := V) :=
    Comodule.isFaithful_corestrict_of_surjective π hπ hV
  rw [HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful
    (FGComoduleCat.of (R := K) (C := G ⧸ I.toIdeal) V) hVQ]
  rw [LinearMap.GeneralLinearGroup.isUnipotent_def]
  let s : WithConv (G →ₐ[K] K) := AlgHom.mapDomain π t
  have hs : s ∈ ratPoints G I := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    simp only [s, AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom]
    rw [(CommHopfAlgCat.mkQuotient_eq_zero_iff G.obj I x).2 hx, map_zero]
  have hnil := isNilpotent_sub_one_of_le_derived G I hI hder hconn hsolv _ V rfl s hs
  have hρ : Comodule.basePointsRepresentation (H := G ⧸ I.toIdeal) V t =
      (TensorProduct.lid K V).conjAlgEquiv K (Comodule.endOfPoint V t.ofConv) := by
    ext m
    rw [LinearEquiv.conjAlgEquiv_apply, Comodule.basePointsRepresentation_apply]
    simp
  rw [← Comodule.basePointsRepresentation_corestrict (M := V) π t, hρ] at hnil
  have h2 := hnil.map ((TensorProduct.lid K V).conjAlgEquiv K).symm
  rw [map_sub, map_one, AlgEquiv.symm_apply_apply] at h2
  convert h2 using 2
  exact Comodule.pointsAction_toLinearMap (V := V) t

end Unipotence

section RadicalNormal

variable {K : Type u} [Field K]

def radicalPullbackQuotientIso (G : FiniteTypeCommHopfAlgCat.{u,u} K) (J : HopfIdeal K G) :
    CommHopfAlgCat.quotient G.obj (radicalPullback G J) ≅
      (FiniteTypeCommHopfAlgCat.solvableRadical (FiniteTypeCommHopfAlgCat.quotient G J)).obj :=
  CommHopfAlgCat.quotientIsoOfSurjective (CommHopfAlgCat.mkQuotient G.obj J)
    (CommHopfAlgCat.mkQuotient_surjective G.obj J) _

theorem geometricallyConnected_radicalPullback (G : FiniteTypeCommHopfAlgCat.{u,u} K)
    (J : HopfIdeal K G) :
    geometricallyConnectedCommHopfAlgProperty K
      (CommHopfAlgCat.quotient G.obj (radicalPullback G J)) :=
  (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso
    (radicalPullbackQuotientIso G J).symm
    (FiniteTypeCommHopfAlgCat.geometricallyConnected_solvableRadical _)

theorem smooth_radicalPullback (G : FiniteTypeCommHopfAlgCat.{u,u} K) (J : HopfIdeal K G) :
    Algebra.Smooth K (G ⧸ (radicalPullback G J).toIdeal) :=
  (smoothCommHopfAlgProperty_iff _).mp
    ((smoothCommHopfAlgProperty K).prop_of_iso (radicalPullbackQuotientIso G J).symm
      ((smoothCommHopfAlgProperty_iff _).mpr
        (FiniteTypeCommHopfAlgCat.smooth_solvableRadical _)))

theorem geometricallySolvable_radicalPullback (G : FiniteTypeCommHopfAlgCat.{u,u} K)
    (J : HopfIdeal K G) :
    geometricallySolvablePointsCommHopfAlgProperty K
      (CommHopfAlgCat.quotient G.obj (radicalPullback G J)) :=
  (geometricallySolvablePointsCommHopfAlgProperty K).prop_of_iso
    (radicalPullbackQuotientIso G J).symm
    (FiniteTypeCommHopfAlgCat.geometricallySolvable_solvableRadical _)

theorem le_radicalPullback (G : FiniteTypeCommHopfAlgCat.{u,u} K) (J : HopfIdeal K G) :
    J ≤ radicalPullback G J := by
  intro x hx
  rw [mem_radicalPullback, (CommHopfAlgCat.mkQuotient_eq_zero_iff G.obj J x).2 hx]
  exact (FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal _).toIdeal.zero_mem

variable [IsAlgClosed K]

theorem isNormal_radicalPullback (G : FiniteTypeCommHopfAlgCat.{u,u} K) [Algebra.Smooth K G]
    (J : HopfIdeal K G) (hJ : J.IsNormal) : (radicalPullback G J).IsNormal := by
  have : IsReduced G := TauCeti.isReduced_of_smooth K G
  have := smooth_radicalPullback G J
  have : IsReduced (G ⧸ (radicalPullback G J).toIdeal) := TauCeti.isReduced_of_smooth K _
  exact isNormal_of_forall_le_conjugate _ (radicalPullback_le_conjugate G J hJ)

theorem solvableRadicalDefiningIdeal_quotient_eq_augmentation
    (G : FiniteTypeCommHopfAlgCat.{u,u} K) [Algebra.Smooth K G] [ConnectedSpace (PrimeSpectrum G)]
    (hred : ∀ J : HopfIdeal K G, J.IsNormal →
      geometricallyConnectedCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.quotient G J).obj →
      smoothUnipotentCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.quotient G J) →
      J = HopfIdeal.augmentation K G)
    (J : HopfIdeal K G) (hJ : J.IsNormal)
    (hder : CommHopfAlgCat.derivedDefiningIdeal (R := K) G ≤ J) :
    FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal (FiniteTypeCommHopfAlgCat.quotient G J) =
      HopfIdeal.augmentation K (FiniteTypeCommHopfAlgCat.quotient G J) := by
  have : IsReduced G := TauCeti.isReduced_of_smooth K G
  have hnormal := isNormal_radicalPullback G J hJ
  have hU := smoothUnipotent_of_le_derived G (radicalPullback G J) hnormal
    (hder.trans (le_radicalPullback G J)) (geometricallyConnected_radicalPullback G J)
    (smooth_radicalPullback G J) (geometricallySolvable_radicalPullback G J)
  have htriv := hred _ hnormal (geometricallyConnected_radicalPullback G J) hU
  apply (HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff
    (CommHopfAlgCat.mkQuotient G.obj J).hom (CommHopfAlgCat.mkQuotient_surjective G.obj J)).mp
  rw [HopfIdeal.comapOfSurjective_augmentation]
  exact htriv

end RadicalNormal

section BaseChange

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem exists_one_tmul_eq {H : Type u} [AddCommGroup H] [Module k H]
    (x : AlgebraicClosure k ⊗[k] H) : ∃ h : H, (1 : AlgebraicClosure k) ⊗ₜ[k] h = x := by
  have hsurj : Function.Surjective (algebraMap k (AlgebraicClosure k)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := AlgebraicClosure k)).2
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul a h =>
    obtain ⟨b, rfl⟩ := hsurj a
    refine ⟨b • h, ?_⟩
    rw [TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨h', rfl⟩ := hy
    exact ⟨h + h', TensorProduct.tmul_add _ _ _⟩

theorem derivedDefiningIdeal_baseChange_le (M : FiniteTypeCommHopfAlgCat.{u,u} k)
    [Algebra.Smooth k M] :
    CommHopfAlgCat.derivedDefiningIdeal (R := AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) M) ≤
      CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k)
        (CommHopfAlgCat.derivedDefiningIdeal (R := k) M) := by
  have : IsReduced M := TauCeti.isReduced_of_smooth k M
  have : IsReduced (AlgebraicClosure k ⊗[k] M) :=
    TauCeti.isReduced_of_smooth (AlgebraicClosure k) _
  intro x hx
  obtain ⟨m, rfl⟩ := exists_one_tmul_eq (k := k) (H := M) x
  apply CommHopfAlgCat.one_tmul_mem_baseChangeHopfIdeal
  have hx' := (CommHopfAlgCat.mem_derivedDefiningIdeal_iff_forall_commutator_apply_eq_zero
    (k := AlgebraicClosure k) (H := AlgebraicClosure k ⊗[k] M) _).mp hx
  rw [CommHopfAlgCat.mem_derivedDefiningIdeal_iff_forall_commutator_apply_eq_zero]
  intro c
  let P : WithConv (M →ₐ[k] k) →* WithConv ((AlgebraicClosure k ⊗[k] M) →ₐ[AlgebraicClosure k]
      AlgebraicClosure k) :=
    (AlgHom.baseChangePointsMulEquiv (k := k) (K := AlgebraicClosure k) (A := M)
      (R := AlgebraicClosure k)).toMonoidHom.comp
      (AlgHom.mapValue (H := M) (Algebra.ofId k (AlgebraicClosure k)))
  have hP : ∀ p : WithConv (M →ₐ[k] k),
      (P p).ofConv (1 ⊗ₜ[k] m) = algebraMap k (AlgebraicClosure k) (p.ofConv m) := by
    intro p
    have h1 := AlgHom.baseChangePointsMulEquiv_symm_apply (k := k) (K := AlgebraicClosure k)
      (A := M) (R := AlgebraicClosure k) (P p) m
    simp only [P, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] at h1
    have hPp : P p = AlgHom.baseChangePointsMulEquiv (k := k) (K := AlgebraicClosure k) (A := M)
        (R := AlgebraicClosure k) (toConv ((Algebra.ofId k (AlgebraicClosure k)).comp p.ofConv)) := by
      simp only [P, MonoidHom.comp_apply, AlgHom.mapValue_apply, MulEquiv.coe_toMonoidHom]
    rw [hPp, ← h1, Algebra.ofId_apply]
  have hPc : P c ∈ commutator _ := by
    have h1 := Subgroup.mem_map_of_mem P c.2
    rw [map_commutator_eq] at h1
    exact Subgroup.commutator_mono le_top le_top h1
  have h2 := hx' ⟨P c, hPc⟩
  rw [hP] at h2
  exact (FaithfulSMul.algebraMap_eq_zero_iff k (AlgebraicClosure k)).mp h2

end BaseChange

section Main

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem solvableRadicalDefiningIdeal_baseChange_derived_eq_augmentation
    (M : FiniteTypeCommHopfAlgCat.{u,u} k) (hM : reductiveCommHopfAlgProperty k M) :
    FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
          (FiniteTypeCommHopfAlgCat.quotient M (CommHopfAlgCat.derivedDefiningIdeal (R := k) M))) =
      HopfIdeal.augmentation (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
          (FiniteTypeCommHopfAlgCat.quotient M (CommHopfAlgCat.derivedDefiningIdeal (R := k) M))) := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) M
  have : Algebra.Smooth k M := hM.smooth
  have : Algebra.Smooth K G := Algebra.Smooth.baseChange k M K
  have : ConnectedSpace (PrimeSpectrum G) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace K G.obj
      (geometricallyConnectedCommHopfAlgProperty.baseChange k K M.obj hM.geometricallyConnected)
  let J := CommHopfAlgCat.baseChangeHopfIdeal (K := K) (CommHopfAlgCat.derivedDefiningIdeal (R := k) M)
  have hJ : J.IsNormal := CommHopfAlgCat.isNormal_baseChangeHopfIdeal
    (CommHopfAlgCat.isNormal_derivedDefiningIdeal M.obj)
  have hR := solvableRadicalDefiningIdeal_quotient_eq_augmentation G hM.eq_augmentation J hJ
    (derivedDefiningIdeal_baseChange_le M)
  let e : FiniteTypeCommHopfAlgCat.quotient G J ≅ FiniteTypeCommHopfAlgCat.baseChange (K := K)
      (FiniteTypeCommHopfAlgCat.quotient M (CommHopfAlgCat.derivedDefiningIdeal (R := k) M)) :=
    ObjectProperty.isoMk _
      (CommHopfAlgCat.quotientBaseChangeIso (K := K) (CommHopfAlgCat.derivedDefiningIdeal (R := k) M))
  have he := FiniteTypeCommHopfAlgCat.comapOfSurjective_solvableRadicalDefiningIdeal e
  rw [hR, ← HopfIdeal.comapOfSurjective_augmentation (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
    (ConcreteCategory.bijective_of_isIso e.hom).2] at he
  exact (HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff _ _).mp he

end Main

end CFSG.LieType.AlgebraicGroups.DerivedSemisimple
