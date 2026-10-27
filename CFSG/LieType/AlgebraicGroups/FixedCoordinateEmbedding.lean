module

public import CFSG.LieType.AlgebraicGroups.FixedComponentCentralIsogeny
public import CFSG.LieType.AlgebraicGroups.FixedConnectedGenerators
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem fixedCoordinateMap_range_eq_comap_range
    (H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σ : H →ₐc[k] H) (τ : K →ₐc[k] K) (f : H.obj ⟶ K.obj)
    (hf : f.hom.comp σ = τ.comp f.hom) (hfs : Function.Surjective f.hom) :
    (TauCeti.AlgHom.mapDomain (A := k) (fixedCoordinateMap H K σ τ f hf).hom.hom).range =
      (TauCeti.AlgHom.mapDomain (A := k) f.hom).range.comap
        (TauCeti.AlgHom.mapDomain (A := k)
          (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom) := by
  let qH := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  let qK := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient K (fixedHopfIdeal K τ)).hom.hom
  let F := (fixedCoordinateMap H K σ τ f hf).hom.hom
  have hcomp : F.comp qH = qK.comp f.hom := fixedCoordinateMap_comp H K σ τ f hf
  have hinj : Function.Injective (TauCeti.AlgHom.mapDomain (A := k) f.hom) :=
    TauCeti.CommHopfAlgCat.mapPointsFunctor_app_injective_of_surjective f hfs
      (CommAlgCat.of k k)
  ext x
  change (∃ y, TauCeti.AlgHom.mapDomain F y = x) ↔
    ∃ y, TauCeti.AlgHom.mapDomain f.hom y = TauCeti.AlgHom.mapDomain qH x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨TauCeti.AlgHom.mapDomain qK y, ?_⟩
    rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp,
      ← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, hcomp]
  · rintro ⟨y, hy⟩
    have hfix : TauCeti.AlgHom.mapDomain τ y = y := by
      apply hinj
      rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, ← hf,
        TauCeti.AlgHom.mapDomain_comp, MonoidHom.comp_apply, hy]
      exact fixedCoordinate_point_fixed H σ x
    have hyq : y ∈ (TauCeti.AlgHom.mapDomain (A := k) qK).range := by
      rw [fixedCoordinate_points_range]
      exact hfix
    obtain ⟨z, rfl⟩ := hyq
    refine ⟨z, ?_⟩
    apply TauCeti.CommHopfAlgCat.quotientPointsHom_injective H.obj (fixedHopfIdeal H σ)
      (CommAlgCat.of k k)
    change TauCeti.AlgHom.mapDomain qH (TauCeti.AlgHom.mapDomain F z) =
      TauCeti.AlgHom.mapDomain qH x
    rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, hcomp,
      TauCeti.AlgHom.mapDomain_comp, MonoidHom.comp_apply]
    exact hy

omit [IsAlgClosed k] in
theorem fixedCoordinateMap_range_map_eq_inf
    (H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σ : H →ₐc[k] H) (τ : K →ₐc[k] K) (f : H.obj ⟶ K.obj)
    (hf : f.hom.comp σ = τ.comp f.hom) (hfs : Function.Surjective f.hom) :
    ((TauCeti.AlgHom.mapDomain (A := k) (fixedCoordinateMap H K σ τ f hf).hom.hom).range).map
        (TauCeti.AlgHom.mapDomain (A := k)
          (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom) =
      (TauCeti.AlgHom.mapDomain (A := k) f.hom).range ⊓
        TauCeti.fixedSubgroup (TauCeti.AlgHom.mapDomain (A := k) σ) := by
  rw [fixedCoordinateMap_range_eq_comap_range H K σ τ f hf hfs,
    Subgroup.map_comap_eq, fixedCoordinate_points_range, inf_comm]

theorem fixed_image_le_component_kernel
    (H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σ : H →ₐc[k] H) (τ : K →ₐc[k] K) (f : H.obj ⟶ K.obj)
    (hf : f.hom.comp σ = τ.comp f.hom) (hfs : Function.Surjective f.hom)
    (hK : ConnectedSpace (PrimeSpectrum (fixedCoordinate K τ))) :
    (TauCeti.AlgHom.mapDomain (A := k) f.hom).range ⊓
        TauCeti.fixedSubgroup (TauCeti.AlgHom.mapDomain (A := k) σ) ≤
      ((TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom (fixedCoordinate H σ)
        (CommAlgCat.of k k)).ker).map
          (TauCeti.AlgHom.mapDomain (A := k)
            (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom) := by
  rw [← fixedCoordinateMap_range_map_eq_inf H K σ τ f hf hfs]
  apply Subgroup.map_mono
  rintro x ⟨y, rfl⟩
  exact componentPointsHom_map_eq_one (fixedCoordinate H σ) (fixedCoordinate K τ)
    (fixedCoordinateMap H K σ τ f hf).hom hK y

theorem componentPointsHom_of_image_le_closed_subgroup
    (H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (I : TauCeti.HopfIdeal k H) (f : H.obj ⟶ K.obj)
    (hK : ConnectedSpace (PrimeSpectrum K))
    (hf : (TauCeti.AlgHom.mapDomain (A := k) f.hom).range ≤
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k))
    [IsReduced K]
    (x : TauCeti.HopfAlgebra.points (R := k)
      (H := TauCeti.FiniteTypeCommHopfAlgCat.quotient H I) (CommAlgCat.of k k))
    (hx : TauCeti.AlgHom.mapDomain
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom x ∈
      (TauCeti.AlgHom.mapDomain (A := k) f.hom).range) :
    TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I) (CommAlgCat.of k k) x = 1 := by
  have hker : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom := by
    intro a ha
    change f.hom a = 0
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
    intro p
    have hp := hf ⟨toConv p, rfl⟩
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hp
    exact (hp a ha).trans (map_zero p).symm
  let g := TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient I (ObjectProperty.homMk f) hker
  obtain ⟨y, hy⟩ := hx
  have hg : TauCeti.AlgHom.mapDomain g.hom.hom y = x := by
    apply TauCeti.CommHopfAlgCat.quotientPointsHom_injective H.obj I (CommAlgCat.of k k)
    change TauCeti.AlgHom.mapDomain
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom
        (TauCeti.AlgHom.mapDomain g.hom.hom y) =
      TauCeti.AlgHom.mapDomain (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom x
    have hcomp := congrArg TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_comp_liftQuotient I
        (ObjectProperty.homMk f) hker)
    change g.hom.hom.comp (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom = f.hom at hcomp
    rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, hcomp]
    exact hy
  rw [← hg]
  exact componentPointsHom_map_eq_one _ _ g.hom hK y

theorem connectedSpace_closed_subgroup_of_sup_images
    (H K L : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (I : TauCeti.HopfIdeal k H) (f : H.obj ⟶ K.obj) (g : H.obj ⟶ L.obj)
    [IsReduced K] [IsReduced L]
    (hK : ConnectedSpace (PrimeSpectrum K)) (hL : ConnectedSpace (PrimeSpectrum L))
    (hgen : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) =
      (TauCeti.AlgHom.mapDomain (A := k) f.hom).range ⊔
        (TauCeti.AlgHom.mapDomain (A := k) g.hom).range) :
    ConnectedSpace (PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)) := by
  let F := TauCeti.FiniteTypeCommHopfAlgCat.quotient H I
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom
  let c := TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom F (CommAlgCat.of k k)
  let P := c.ker.map (TauCeti.AlgHom.mapDomain (A := k) q)
  have hfactor (N : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced N]
      (hN : ConnectedSpace (PrimeSpectrum N)) (φ : H.obj ⟶ N.obj)
      (hφ : (TauCeti.AlgHom.mapDomain (A := k) φ.hom).range ≤
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
      (TauCeti.AlgHom.mapDomain (A := k) φ.hom).range ≤ P := by
    intro y hy
    obtain ⟨x, hx⟩ := hφ hy
    refine ⟨x, ?_, hx⟩
    exact componentPointsHom_of_image_le_closed_subgroup H N I φ hN hφ x
      (hx.symm ▸ hy)
  have hf : (TauCeti.AlgHom.mapDomain (A := k) f.hom).range ≤
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) := by
    rw [hgen]
    exact le_sup_left
  have hg : (TauCeti.AlgHom.mapDomain (A := k) g.hom).range ≤
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) := by
    rw [hgen]
    exact le_sup_right
  have hle : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) ≤ P := by
    rw [hgen]
    exact sup_le (hfactor K hK f hf) (hfactor L hL g hg)
  apply connectedSpace_of_componentPointsHom_eq_one F
  intro x
  have hx : TauCeti.AlgHom.mapDomain q x ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) := ⟨x, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hle hx
  exact (TauCeti.CommHopfAlgCat.quotientPointsHom_injective H.obj I (CommAlgCat.of k k) hxy) ▸ hy

omit [IsAlgClosed k] in
theorem fixedHopfIdeal_map_of_equivariant
    (H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σ : H →ₐc[k] H) (τ : K →ₐc[k] K) (f : H.obj ⟶ K.obj)
    (hf : f.hom.comp σ = τ.comp f.hom) (hfs : Function.Surjective f.hom) :
    (fixedHopfIdeal H σ).map f.hom = fixedHopfIdeal K τ := by
  apply TauCeti.HopfIdeal.ext
  intro x
  rw [TauCeti.HopfIdeal.mem_map_iff_of_surjective hfs]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hle : (fixedHopfIdeal H σ).toIdeal ≤
        RingHom.ker ((TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient K (fixedHopfIdeal K τ)).hom.hom.comp
          f.hom).toAlgHom.toRingHom := by
      apply (TauCeti.HopfIdeal.equalizer_le_ker_iff _).2
      intro a
      have h' : ((TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient K (fixedHopfIdeal K τ)).hom.hom.comp
          f.hom).comp σ =
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient K (fixedHopfIdeal K τ)).hom.hom.comp f.hom := by
        rw [BialgHom.comp_assoc, hf, ← BialgHom.comp_assoc, fixedCoordinateHom_comp]
      exact congrArg (fun g : H →ₐc[k] _ => g a) h'
    exact (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff K
      (fixedHopfIdeal K τ) (f.hom y)).mp (hle hy)
  · intro hx
    have hle : (fixedHopfIdeal K τ).toIdeal ≤
        ((fixedHopfIdeal H σ).map f.hom).toIdeal := by
      rw [fixedHopfIdeal, TauCeti.HopfIdeal.equalizer_toIdeal]
      apply TauCeti.HopfIdeal.equalizerIdeal_le_iff.2
      intro a
      obtain ⟨a, rfl⟩ := hfs a
      have ha := TauCeti.HopfIdeal.sub_mem_equalizer (f := σ) (g := BialgHom.id k H) a
      have hmap := TauCeti.HopfIdeal.mem_map_of_mem f.hom ha
      have he := congrArg (fun g : H →ₐc[k] K => g a) hf
      change f.hom (σ a) = τ (f.hom a) at he
      have hmap' := TauCeti.HopfIdeal.mem_toIdeal.2 hmap
      simpa only [fixedHopfIdeal, BialgHom.id_apply, map_sub, he] using hmap'
    have hx' := hle hx
    exact (TauCeti.HopfIdeal.mem_map_iff_of_surjective hfs).mp hx'


def fixedCoordinateQuotientAlgEquiv
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (I : TauCeti.HopfIdeal k H)
    (σ : H →ₐc[k] H) (τ : TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐc[k]
      TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)
    (hf : (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom.comp σ =
      τ.comp (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom) :
    fixedCoordinate (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I) τ ≃ₐ[k]
      TauCeti.FiniteTypeCommHopfAlgCat.quotient (fixedCoordinate H σ)
        (I.map (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom) := by
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H I
  have he := fixedHopfIdeal_map_of_equivariant H Q σ τ
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom hf
    (TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj I)
  have he' : (fixedHopfIdeal Q τ).toIdeal =
      Ideal.map (Ideal.Quotient.mkₐ k I.toIdeal).toRingHom (fixedHopfIdeal H σ).toIdeal := by
    rw [← he, TauCeti.HopfIdeal.map_toIdeal]
    rfl
  have hi : (I.map (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H
        (fixedHopfIdeal H σ)).hom.hom).toIdeal =
      Ideal.map (Ideal.Quotient.mkₐ k (fixedHopfIdeal H σ).toIdeal).toRingHom I.toIdeal := by
    rw [TauCeti.HopfIdeal.map_toIdeal]
    rfl
  exact ((Ideal.quotientEquivAlgOfEq k he').trans
    (DoubleQuot.quotQuotEquivCommₐ k I.toIdeal (fixedHopfIdeal H σ).toIdeal)).trans
      (Ideal.quotientEquivAlgOfEq k hi.symm)

def quotientCoordinateEnd
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (I : TauCeti.HopfIdeal k H)
    (σ : H →ₐc[k] H) (hI : ∀ x ∈ I, σ x ∈ I) :
    TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐc[k]
      TauCeti.FiniteTypeCommHopfAlgCat.quotient H I :=
  TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient I
      (TauCeti.FiniteTypeCommHopfAlgCat.ofHom
        ((TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom.comp σ)) (by
          intro x hx
          exact (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff H I (σ x)).2 (hI x hx)))

omit [IsAlgClosed k] in
theorem quotientCoordinateEnd_equivariant
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (I : TauCeti.HopfIdeal k H)
    (σ : H →ₐc[k] H) (hI : ∀ x ∈ I, σ x ∈ I) :
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom.comp σ =
      (quotientCoordinateEnd H I σ hI).comp
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom := by
  exact (congrArg TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_comp_liftQuotient I
      (TauCeti.FiniteTypeCommHopfAlgCat.ofHom
        ((TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom.comp σ))
      (by
        intro x hx
        exact (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff H I (σ x)).2 (hI x hx)))).symm

theorem mem_ideal_map_of_points_stable
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (I : TauCeti.HopfIdeal k H)
    [IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)] (σ : H →ₐc[k] H)
    (hstable : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      TauCeti.AlgHom.mapDomain σ x ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    ∀ x ∈ I, σ x ∈ I := by
  intro a ha
  apply (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff H I (σ a)).1
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro p
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom
  have h := hstable (TauCeti.AlgHom.mapDomain q (toConv p)) ⟨toConv p, rfl⟩
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at h
  exact (h a ha).trans (map_zero p).symm

omit [IsAlgClosed k] in
theorem geometricallySolvable_intersection_quotient
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (I J : TauCeti.HopfIdeal k H)
    (hJ : TauCeti.geometricallySolvablePointsCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J).obj) :
    TauCeti.geometricallySolvablePointsCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)
        (J.map (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom)).obj := by
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H I
  let K := TauCeti.FiniteTypeCommHopfAlgCat.quotient Q
    (J.map (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom)
  let qI := TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I
  let qJ := TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient Q (J.map qI.hom.hom)
  let f : H ⟶ K := qI ≫ qJ
  have hf : J.toIdeal ≤ RingHom.ker (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom f).toAlgHom.toRingHom := by
    intro a ha
    change qJ.hom.hom (qI.hom.hom a) = 0
    exact (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff Q _ _).2
      (TauCeti.HopfIdeal.mem_map_of_mem qI.hom.hom ha)
  let g := TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient J f hf
  have hfs : Function.Surjective (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom f) :=
    (TauCeti.CommHopfAlgCat.mkQuotient_surjective Q.obj _).comp
      (TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj I)
  have hgs : Function.Surjective g.hom.hom := by
    intro x
    obtain ⟨a, rfl⟩ := hfs x
    refine ⟨(TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H J).hom.hom a, ?_⟩
    exact congrArg (fun f : H ⟶ K => f.hom.hom a)
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_comp_liftQuotient J f hf)
  exact TauCeti.geometricallySolvablePointsCommHopfAlgProperty_of_surjective k g.hom hgs hJ

end CFSG.LieType.AlgebraicGroups
