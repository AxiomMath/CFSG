module

public import CFSG.LieType.AlgebraicGroups.CentralTorusSolvable

public noncomputable section

open WithConv
open scoped commutatorElement

namespace CFSG.LieType.AlgebraicGroups.CanonicalReductive

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem pow_length_eq_prod_conj_mul_prod_commutatorElement {G : Type*} [Group G]
    (T : Subgroup G) (hT : ∀ x ∈ T, ∀ y ∈ T, Commute x y) {s : G} (hs : s ∈ T)
    (ns : List G) (hns : ∀ n ∈ ns, n ∈ Subgroup.normalizer (T : Set G)) :
    s ^ ns.length = (ns.map fun n => n * s * n⁻¹).prod * (ns.map fun n => ⁅s, n⁆).prod ∧
      (ns.map fun n => n * s * n⁻¹).prod ∈ T ∧ (ns.map fun n => ⁅s, n⁆).prod ∈ T := by
  induction ns with
  | nil => simp [T.one_mem]
  | cons n ns ih =>
    obtain ⟨heq, hA, hB⟩ := ih fun m hm => hns m (List.mem_cons_of_mem n hm)
    have hn := hns n List.mem_cons_self
    have ha : n * s * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn s).mp hs
    have hc : ⁅s, n⁆ = s * (n * s * n⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    have hcT : ⁅s, n⁆ ∈ T := by
      rw [hc]
      exact T.mul_mem hs (T.inv_mem ha)
    have hac : n * s * n⁻¹ * ⁅s, n⁆ = s := by
      rw [hc, ← mul_assoc, (hT _ ha _ hs).eq, mul_inv_cancel_right]
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨?_, T.mul_mem ha hA, T.mul_mem hcT hB⟩
    set A := (ns.map fun n => n * s * n⁻¹).prod
    set B := (ns.map fun n => ⁅s, n⁆).prod
    calc s ^ (ns.length + 1) = s * (A * B) := by rw [pow_succ', heq]
      _ = n * s * n⁻¹ * ⁅s, n⁆ * (A * B) := by rw [hac]
      _ = n * s * n⁻¹ * (⁅s, n⁆ * A) * B := by group
      _ = n * s * n⁻¹ * (A * ⁅s, n⁆) * B := by rw [(hT _ hcT _ hA).eq]
      _ = n * s * n⁻¹ * A * (⁅s, n⁆ * B) := by group

omit [IsAlgClosed k] in
theorem commutatorElement_mem_range_derivedCoordinateMap
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (g h : WithConv (M →ₐ[k] k)) :
    ⁅g, h⁆ ∈ (TauCeti.AlgHom.mapDomain (A := k) (derivedCoordinateMap M)).range := by
  have hc := TauCeti.CommHopfAlgCat.commutator_mem_derivedPointsSubgroup M.obj
    (CommAlgCat.of k k) g h
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hc
  obtain ⟨d, hd⟩ := exists_derivedCoordinateMap_point_of_forall M (g := ⁅g, h⁆) fun x hx => hc x hx
  exact ⟨d, hd⟩

theorem exists_connectedCenter_cocharacter_lift
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced M]
    (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, ∀ g : WithConv (M →ₐ[k] k),
      Commute (TauCeti.Cocharacter.pointsHom k μ t) g) :
    ∃ μZ : connectedCenter M →ₐc[k] LaurentPolynomial k,
      μZ.comp (connectedCenterCoordinateMap M) = μ := by
  apply exists_connectedCenter_lift M (LaurentPolynomial k) μ
  intro a ha
  apply RegularCocharacter.laurentPolynomial_eq_zero_of_forall_point
  intro t
  have hcentral : TauCeti.HopfAlgebra.IsCentralPoint
      (TauCeti.Cocharacter.pointsHom k μ t) := by
    apply isCentralPoint_of_commute_base_points M (A := CommAlgCat.of k k)
      (TauCeti.Cocharacter.pointsHom k μ t)
    intro g
    have he : TauCeti.AlgHom.mapValue (Algebra.ofId k k) g = g := by
      apply WithConv.ofConv_injective
      ext b
      rw [TauCeti.AlgHom.mapValue_apply]
      exact (Algebra.ofId k k).commutes (g.ofConv b)
    rw [he]
    exact hμ t g
  have hmem := (TauCeti.CommHopfAlgCat.mem_centerPointsSubgroup_iff M.obj
    (CommAlgCat.of k k) (TauCeti.Cocharacter.pointsHom k μ t)).2 hcentral
  have h := (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff M.obj _ _ _).1 hmem a ha
  simpa only [TauCeti.Cocharacter.pointsHom_apply, TauCeti.AlgHom.mapDomain_apply_apply] using h

theorem pointsHom_mem_connectedCenter_of_commute
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced M]
    (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, ∀ g : WithConv (M →ₐ[k] k),
      Commute (TauCeti.Cocharacter.pointsHom k μ t) g) :
    ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      (TauCeti.AlgHom.mapDomain (A := k) (connectedCenterCoordinateMap M)).range := by
  obtain ⟨μZ, hμZ⟩ := exists_connectedCenter_cocharacter_lift M μ hμ
  intro t
  refine ⟨TauCeti.Cocharacter.pointsHom k μZ t, ?_⟩
  have h := congrArg (fun ν : M →ₐc[k] LaurentPolynomial k =>
    TauCeti.Cocharacter.pointsHom k ν t) hμZ
  simpa only [TauCeti.Cocharacter.pointsHom_apply,
    TauCeti.AlgHom.mapDomain_comp, MonoidHom.comp_apply] using h

theorem scalar_action_of_normalizer_fixed_on_simple
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k))
    (hfixed : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ t : kˣ, g * TauCeti.Cocharacter.pointsHom k μ t * g⁻¹ =
        TauCeti.Cocharacter.pointsHom k μ t)
    (V : TauCeti.FGComoduleCat.{u,u,u} k M)
    (hV : ∀ N : TauCeti.Subcomodule k M V, N = ⊥ ∨ N = ⊤) :
    ∀ t : kˣ, ∃ c : k, ∀ v : V,
      TauCeti.Comodule.basePointsRepresentation V (TauCeti.Cocharacter.pointsHom k μ t) v = c • v := by
  intro t
  exact NormalizerFixedScalar.exists_smul_of_reductive M hM I hI μ hμ hfixed V hV t

theorem exists_faithful_scalar_filtration_of_normalizer_fixed
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k))
    (hfixed : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ t : kˣ, g * TauCeti.Cocharacter.pointsHom k μ t * g⁻¹ =
        TauCeti.Cocharacter.pointsHom k μ t) :
    ∃ V : TauCeti.FGComoduleCat.{u,u,u} k M,
      TauCeti.Comodule.IsFaithful (k := k) (H := M) (V := V) ∧
      ∃ (d : ℕ) (F : ℕ →o Submodule k V), F 0 = ⊥ ∧ F d = ⊤ ∧
        (∀ (g : WithConv (M →ₐ[k] k)) i, ∀ v ∈ F i,
          TauCeti.Comodule.basePointsRepresentation V g v ∈ F i) ∧
        ∀ t : kˣ, ∀ i, ∃ c : k, ∀ v ∈ F (i + 1),
          TauCeti.Comodule.basePointsRepresentation V (TauCeti.Cocharacter.pointsHom k μ t) v -
            c • v ∈ F i := by
  obtain ⟨V,n,b,hb⟩ := TauCeti.Comodule.exists_coordinateBialgHom_surjective (k := k) (H := M)
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let : Module.Finite k V := Module.Finite.of_basis b
  have hV : TauCeti.Comodule.IsFaithful (k := k) (H := M) (V := V) := by
    rw [TauCeti.Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b,
      TauCeti.Comodule.isClosedImmersion_coordinateGroupSchemeHom_iff]
    exact hb
  refine ⟨TauCeti.FGComoduleCat.of (R := k) (C := M) V, hV, ?_⟩
  exact ScalarFiltration.exists_scalar_filtration M μ
    (fun W hW => scalar_action_of_normalizer_fixed_on_simple M hM I hI μ hμ hfixed W hW) V

theorem exists_normal_unipotent_commutators_of_normalizer_fixed
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k))
    (hfixed : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ t : kˣ, g * TauCeti.Cocharacter.pointsHom k μ t * g⁻¹ =
        TauCeti.Cocharacter.pointsHom k μ t) :
    ∃ J : TauCeti.HopfIdeal k M, J.IsNormal ∧
      (∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
        TauCeti.HopfAlgebra.IsUnipotentPoint x) ∧
      ∀ t : kˣ, ∀ g : WithConv (M →ₐ[k] k),
        TauCeti.Cocharacter.pointsHom k μ t * g *
          (TauCeti.Cocharacter.pointsHom k μ t)⁻¹ * g⁻¹ ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k) := by
  obtain ⟨V,hV,d,F,hF0,hFd,hstab,hscalar⟩ :=
    exists_faithful_scalar_filtration_of_normalizer_fixed M hM I hI μ hμ hfixed
  let : Algebra.Smooth k M := hM.smooth
  let : IsReduced M := TauCeti.isReduced_of_smooth k M
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  exact GradedKernel.exists_normal_unipotent_commutators_of_scalar_filtration
    M V F hstab hV d hF0 hFd μ hscalar

theorem pointsHom_commute_of_normalizer_fixed
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k))
    (hfixed : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ t : kˣ, g * TauCeti.Cocharacter.pointsHom k μ t * g⁻¹ =
        TauCeti.Cocharacter.pointsHom k μ t) :
    ∀ t : kˣ, ∀ g : WithConv (M →ₐ[k] k),
      Commute (TauCeti.Cocharacter.pointsHom k μ t) g := by
  obtain ⟨J,hJ,hu,hcomm⟩ :=
    exists_normal_unipotent_commutators_of_normalizer_fixed M hM I hI μ hμ hfixed
  exact pointsHom_commute_of_mem_normal_unipotent M hM μ J hJ hu hcomm

theorem pointsHom_mem_connectedCenter_of_normalizer_fixed
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k))
    (hfixed : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ t : kˣ, g * TauCeti.Cocharacter.pointsHom k μ t * g⁻¹ =
        TauCeti.Cocharacter.pointsHom k μ t) :
    ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      (TauCeti.AlgHom.mapDomain (A := k) (connectedCenterCoordinateMap M)).range := by
  let : Algebra.Smooth k M := hM.smooth
  let : IsReduced M := TauCeti.isReduced_of_smooth k M
  exact pointsHom_mem_connectedCenter_of_commute M μ
    (pointsHom_commute_of_normalizer_fixed M hM I hI μ hμ hfixed)

theorem exists_list_normalizer_conjugate_prod_mem_connectedCenter
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k)) :
    ∃ ns : List (WithConv (M →ₐ[k] k)), ns ≠ [] ∧
      (∀ n ∈ ns, n ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k)))) ∧
      ∀ t : kˣ, (ns.map fun n => n * TauCeti.Cocharacter.pointsHom k μ t * n⁻¹).prod ∈
        (TauCeti.AlgHom.mapDomain (A := k) (connectedCenterCoordinateMap M)).range := by
  have htor := ((TauCeti.HopfIdeal.isMaximalTorus_iff k M.obj I).mp hI).1
  obtain ⟨n,π,hπ,hker⟩ := RegularCocharacter.exists_splitCoordinates M I htor
  obtain ⟨ψ₀,hψ₀⟩ := RegularCocharacter.exists_eq_cocharacterOfAddHom π hπ μ
    (RegularCocharacter.eq_zero_of_forall_pointsHom_mem M I π hker μ hμ)
  rw [hψ₀]
  apply RegularCocharacter.exists_list_normalizer_conjugate_prod_of_fixed_cocharacter
    M I π hπ hker ψ₀
  intro ψ hfixed
  apply pointsHom_mem_connectedCenter_of_normalizer_fixed M hM I hI
    (RegularCocharacter.cocharacterOfAddHom ψ π) ?_ hfixed
  intro t
  rw [RegularCocharacter.mem_quotientPointsSubgroup_iff_exists_mapDomain M I π hπ hker,
    RegularCocharacter.pointsHom_cocharacterOfAddHom]
  exact ⟨_,rfl⟩

theorem quotientPointsSubgroup_le_connectedCenter_sup_derived
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I) :
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) ≤
      (TauCeti.AlgHom.mapDomain (A := k) (connectedCenterCoordinateMap M)).range ⊔
        (TauCeti.AlgHom.mapDomain (A := k) (derivedCoordinateMap M)).range := by
  have htorus := ((TauCeti.HopfIdeal.isMaximalTorus_iff k M.obj I).mp hI).1
  obtain ⟨n, π, hπ, hker⟩ := RegularCocharacter.exists_splitCoordinates M I htorus
  let T := TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k)
  have hmemT : ∀ s : WithConv (M →ₐ[k] k),
      s ∈ T ↔ ∃ σ, TauCeti.AlgHom.mapDomain (A := k) π σ = s :=
    RegularCocharacter.mem_quotientPointsSubgroup_iff_exists_mapDomain M I π hπ hker
  have hT : ∀ x ∈ T, ∀ y ∈ T, Commute x y := fun x hx y hy =>
    RegularCocharacter.commute_of_mem_range_mapDomain π ((hmemT x).mp hx) ((hmemT y).mp hy)
  intro s hs
  obtain ⟨σ, rfl⟩ := (hmemT s).mp hs
  refine RegularCocharacter.mapDomain_mem_of_pointsHom_mem π _ (fun i t => ?_) σ
  let μ := RegularCocharacter.cocharacterOfAddHom (Finsupp.applyAddHom i) π
  have hμT : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈ T := by
    intro t
    rw [hmemT, RegularCocharacter.pointsHom_cocharacterOfAddHom]
    exact ⟨_, rfl⟩
  obtain ⟨ns, hne, hnN, hprod⟩ :=
    exists_list_normalizer_conjugate_prod_mem_connectedCenter M hM I hI μ hμT
  have hlen : 0 < ns.length := List.length_pos_of_ne_nil hne
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (t : k) hlen
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hlen.ne'] at hz
    exact t.ne_zero hz.symm
  have ht : (Units.mk0 z hz0) ^ ns.length = t := Units.ext (by simpa using hz)
  rw [← ht, map_pow]
  obtain ⟨heq, -, -⟩ := pow_length_eq_prod_conj_mul_prod_commutatorElement T hT
    (hμT (Units.mk0 z hz0)) ns hnN
  rw [heq]
  refine mul_mem (Subgroup.mem_sup_left (hprod _)) (Subgroup.mem_sup_right ?_)
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨n', -, rfl⟩ := List.mem_map.mp hx
  exact commutatorElement_mem_range_derivedCoordinateMap M _ _

theorem quotientPointsSubgroup_closureIdentityComponent_centralizer_le
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I) :
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj
        (TorusConjugacy.closureIdentityComponent M (Subgroup.centralizer
          (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
            Set (WithConv (M →ₐ[k] k))))) (CommAlgCat.of k k) ≤
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :=
  CartanComponent.quotientPointsSubgroup_cartan_le M hM hI

theorem exists_isMaximalTorus_relIndex_centralizer_ne_zero
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M) :
    ∃ I : TauCeti.HopfIdeal k M, TauCeti.HopfIdeal.IsMaximalTorus k M.obj I ∧
      (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k)).relIndex
        (Subgroup.centralizer
          (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
            Set (WithConv (M →ₐ[k] k)))) ≠ 0 := by
  obtain ⟨I, hI⟩ := TauCeti.HopfIdeal.exists_isMaximalTorus M
  exact ⟨I, hI, mt (Subgroup.relIndex_eq_zero_of_le_left
    (quotientPointsSubgroup_closureIdentityComponent_centralizer_le M hM I hI))
    (TorusConjugacy.relIndex_closureIdentityComponent_ne_zero M _)⟩

end CFSG.LieType.AlgebraicGroups.CanonicalReductive
