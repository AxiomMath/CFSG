module

public import CFSG.LieType.AlgebraicGroups.SeminaireExp3Component

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.SeminaireExp3

open Topology Pointwise TopologicalSpace WithConv TensorProduct

namespace ZariskiGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : Type} [Field k]

section DomainImage

variable [IsAlgClosed k]

theorem exists_comorphism {D : Type} [CommRing D] [Algebra k D] [Algebra.FiniteType k D]
    (x : Matrix ι ι D) (hx : ∀ z : D →ₐ[k] k, (x.map z).det ≠ 0) :
    ∃ ψ : GLCoord k ι →ₐ[k] D, ∀ (z : D →ₐ[k] k) (g : ZariskiGL ι k),
      (toGL g : Matrix ι ι k) = x.map z → z.comp ψ = pt g := by
  have hd : ∀ z : D →ₐ[k] k, z x.det ≠ 0 := fun z => by
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply]
    exact hx z
  obtain ⟨u, hu⟩ := isUnit_of_forall_algHom_ne_zero hd
  refine ⟨GLCoord.lift k ι x ↑u⁻¹ (by rw [← hu, Units.mul_inv]), fun z g hg => ?_⟩
  refine GLCoord.algHom_ext k ι (fun i j => ?_) ?_
  · simp [hg]
  · have h1 : z x.det * z (↑u⁻¹ : D) = 1 := by rw [← map_mul, ← hu, Units.mul_inv, map_one]
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply, ← hg] at h1
    rw [AlgHom.comp_apply, GLCoord.lift_glDetInv, pt_glDetInv]
    exact eq_inv_of_mul_eq_one_right h1

theorem isDomainImage_range {A : Type} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    {X : Type} [TopologicalSpace X] {e : X ≃ (A →ₐ[k] k)}
    (he : IsInducing fun x => pointSpec (e x)) {V : Set X} (hVc : IsClosed V)
    (hVi : IsIrreducible V) (f : V → ZariskiGL ι k) (Q : Matrix ι ι A)
    (hQ : ∀ v : V, (toGL (f v) : Matrix ι ι k) = Q.map (e v)) :
    IsDomainImage k (pt '' Set.range f) := by
  set J := pointsIdeal (e '' V)
  have hJ : J.IsPrime := (SeminaireExp3.isIrreducible_iff_isPrime he).1 hVi
  have hpts := range_comp_mkₐ_pointsIdeal he hVc
  have hz : ∀ z : (A ⧸ J) →ₐ[k] k, ∃ v : V, z.comp (Ideal.Quotient.mkₐ k J) = e v := fun z => by
    have h : z.comp (Ideal.Quotient.mkₐ k J) ∈ e '' V := by
      rw [← hpts]
      exact ⟨z, rfl⟩
    obtain ⟨v, hv, hve⟩ := h
    exact ⟨⟨v, hv⟩, hve.symm⟩
  have hmap : ∀ (z : (A ⧸ J) →ₐ[k] k) (v : V), z.comp (Ideal.Quotient.mkₐ k J) = e v →
      (Q.map (Ideal.Quotient.mkₐ k J)).map z = (toGL (f v) : Matrix ι ι k) := by
    intro z v hzv
    rw [Matrix.map_map, hQ v, ← hzv]
    rfl
  obtain ⟨ψ, hψ⟩ := exists_comorphism (Q.map (Ideal.Quotient.mkₐ k J)) fun z => by
    obtain ⟨v, hv⟩ := hz z
    rw [hmap z v hv]
    exact (toGL (f v)).det_ne_zero
  refine ⟨A ⧸ J, inferInstance, inferInstance, inferInstance, inferInstance, ψ, ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    have h : e v ∈ Set.range fun z : (A ⧸ J) →ₐ[k] k => z.comp (Ideal.Quotient.mkₐ k J) := by
      rw [hpts]
      exact ⟨v, v.2, rfl⟩
    obtain ⟨z, hzv : z.comp (Ideal.Quotient.mkₐ k J) = e v⟩ := h
    exact ⟨z, hψ z (f v) (hmap z v hzv).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨v, hv⟩ := hz z
    exact ⟨f v, ⟨v, rfl⟩, (hψ z (f v) (hmap z v hv).symm).symm⟩

omit [IsAlgClosed k] in
theorem isDomainImage_one : IsDomainImage k (pt '' ({1} : Set (ZariskiGL ι k))) := by
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, pt 1, ?_⟩
  rw [Set.image_singleton]
  ext y
  constructor
  · rintro rfl
    exact ⟨AlgHom.id k k, AlgHom.id_comp _⟩
  · rintro ⟨z, rfl⟩
    have hz : z = AlgHom.id k k := AlgHom.ext fun c => z.commutes c
    show z.comp (pt 1) = pt 1
    rw [hz, AlgHom.id_comp]

theorem isDomainImage_mul {S T : Set (ZariskiGL ι k)} (hS : IsDomainImage k (pt '' S))
    (hT : IsDomainImage k (pt '' T)) : IsDomainImage k (pt '' (S * T)) := by
  obtain ⟨D₁, _, _, _, _, ψ₁, hψ₁⟩ := hS
  obtain ⟨D₂, _, _, _, _, ψ₂, hψ₂⟩ := hT
  have hdom : IsDomain (D₁ ⊗[k] D₂) := isDomain_tensorProduct k D₁ D₂
  let ψ : GLCoord k ι →ₐ[k] D₁ ⊗[k] D₂ :=
    (toConv (Algebra.TensorProduct.includeLeft.comp ψ₁) *
      toConv (Algebra.TensorProduct.includeRight.comp ψ₂)).ofConv
  have hz : ∀ z : D₁ ⊗[k] D₂ →ₐ[k] k, z.comp ψ =
      (toConv ((z.comp Algebra.TensorProduct.includeLeft).comp ψ₁) *
        toConv ((z.comp Algebra.TensorProduct.includeRight).comp ψ₂)).ofConv := fun z => by
    rw [AlgHom.comp_convMul_distrib]
    rfl
  refine ⟨D₁ ⊗[k] D₂, inferInstance, inferInstance, inferInstance, hdom, ψ, ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    have h₁ : pt s ∈ Set.range fun z : D₁ →ₐ[k] k => z.comp ψ₁ := by
      rw [← hψ₁]
      exact ⟨s, hs, rfl⟩
    have h₂ : pt t ∈ Set.range fun z : D₂ →ₐ[k] k => z.comp ψ₂ := by
      rw [← hψ₂]
      exact ⟨t, ht, rfl⟩
    obtain ⟨z₁, hz₁ : z₁.comp ψ₁ = pt s⟩ := h₁
    obtain ⟨z₂, hz₂ : z₂.comp ψ₂ = pt t⟩ := h₂
    refine ⟨Algebra.TensorProduct.productMap z₁ z₂, ?_⟩
    show (Algebra.TensorProduct.productMap z₁ z₂).comp ψ = pt (s * t)
    rw [hz, Algebra.TensorProduct.productMap_left, Algebra.TensorProduct.productMap_right, hz₁,
      hz₂, pt_mul]
  · rintro ⟨z, rfl⟩
    have h₁ : (z.comp Algebra.TensorProduct.includeLeft).comp ψ₁ ∈ pt '' S := by
      rw [hψ₁]
      exact ⟨_, rfl⟩
    have h₂ : (z.comp Algebra.TensorProduct.includeRight).comp ψ₂ ∈ pt '' T := by
      rw [hψ₂]
      exact ⟨_, rfl⟩
    obtain ⟨s, hs, hzs⟩ := h₁
    obtain ⟨t, ht, hzt⟩ := h₂
    refine ⟨s * t, Set.mul_mem_mul hs ht, ?_⟩
    show pt (s * t) = z.comp ψ
    rw [hz, ← hzs, ← hzt, pt_mul]

omit [IsAlgClosed k] in
theorem isDomainImage_inv {S : Set (ZariskiGL ι k)} (hS : IsDomainImage k (pt '' S)) :
    IsDomainImage k (pt '' S⁻¹) := by
  obtain ⟨D, _, _, _, _, ψ, hψ⟩ := hS
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance,
    ψ.comp (HopfAlgebra.antipodeAlgHom k (GLCoord k ι)), ?_⟩
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    have h : pt g⁻¹ ∈ Set.range fun z : D →ₐ[k] k => z.comp ψ := by
      rw [← hψ]
      exact ⟨g⁻¹, hg, rfl⟩
    obtain ⟨z, hz : z.comp ψ = pt g⁻¹⟩ := h
    refine ⟨z, ?_⟩
    show z.comp (ψ.comp (HopfAlgebra.antipodeAlgHom k (GLCoord k ι))) = pt g
    rw [← AlgHom.comp_assoc, hz, ← pt_inv, inv_inv]
  · rintro ⟨z, rfl⟩
    have h : z.comp ψ ∈ pt '' S := by
      rw [hψ]
      exact ⟨z, rfl⟩
    obtain ⟨g, hg, hzg⟩ := h
    refine ⟨g⁻¹, Set.inv_mem_inv.2 hg, ?_⟩
    show pt g⁻¹ = z.comp (ψ.comp (HopfAlgebra.antipodeAlgHom k (GLCoord k ι)))
    rw [pt_inv, hzg, AlgHom.comp_assoc]

omit [IsAlgClosed k] in
theorem isDomainImage_zpow_units {S : Set (ZariskiGL ι k)} (hS : IsDomainImage k (pt '' S))
    (e : ℤˣ) : IsDomainImage k (pt '' (S ^ (e : ℤ))) := by
  rcases Int.units_eq_one_or e with rfl | rfl
  · simpa using hS
  · simpa using isDomainImage_inv hS

theorem isClosed_of_isDomainImage {H : Subgroup (ZariskiGL ι k)}
    (h : IsDomainImage k (pt '' (H : Set (ZariskiGL ι k)))) :
    IsClosed (H : Set (ZariskiGL ι k)) :=
  (isClosed_iff_isPointClosed isInducing_pt).2
    (isConnectedAlgebraicSubgroup_map point H h.isPointConstructible h.isPointIrreducible).1

theorem isIrreducible_of_isDomainImage {S : Set (ZariskiGL ι k)}
    (h : IsDomainImage k (pt '' S)) : IsIrreducible S :=
  (isIrreducible_iff_isPointIrreducible isInducing_pt).2 h.isPointIrreducible

end DomainImage

section Morphism

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : Subgroup (ZariskiGL ι k)}
  {H : Subgroup (ZariskiGL κ k)}

@[expose] def IsMorphism (φ : G →* H) : Prop :=
  ∀ a b : κ, ∃ P : MvPolynomial (ι × ι ⊕ Unit) k, ∀ g : G,
    (toGL (φ g : ZariskiGL κ k) : Matrix κ κ k) a b = eval (g : ZariskiGL ι k) P

@[expose] def mapSubgroup (φ : G →* H) (L : Subgroup (ZariskiGL ι k)) :
    Subgroup (ZariskiGL κ k) :=
  ((L.subgroupOf G).map φ).map H.subtype

theorem mem_mapSubgroup {φ : G →* H} {L : Subgroup (ZariskiGL ι k)} {y : ZariskiGL κ k} :
    y ∈ mapSubgroup φ L ↔ ∃ g : G, (g : ZariskiGL ι k) ∈ L ∧ (φ g : ZariskiGL κ k) = y := by
  simp only [mapSubgroup, Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩

theorem mapSubgroup_le (φ : G →* H) (L : Subgroup (ZariskiGL ι k)) : mapSubgroup φ L ≤ H := by
  intro y hy
  obtain ⟨g, -, rfl⟩ := mem_mapSubgroup.1 hy
  exact (φ g).2

theorem mapSubgroup_mono (φ : G →* H) {L L' : Subgroup (ZariskiGL ι k)} (h : L ≤ L') :
    mapSubgroup φ L ≤ mapSubgroup φ L' := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := mem_mapSubgroup.1 hy
  exact mem_mapSubgroup.2 ⟨g, h hg, rfl⟩

theorem coe_mapSubgroup_eq_iUnion (φ : G →* H) :
    (mapSubgroup φ G : Set (ZariskiGL κ k)) =
      ⋃ q : G ⧸ (identityComponent G).subgroupOf G,
        (φ q.out : ZariskiGL κ k) •
          (mapSubgroup φ (identityComponent G) : Set (ZariskiGL κ k)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨g, -, rfl⟩ := mem_mapSubgroup.1 hy
    set q : G ⧸ (identityComponent G).subgroupOf G := (g : G ⧸ (identityComponent G).subgroupOf G)
    have hh : q.out⁻¹ * g ∈ (identityComponent G).subgroupOf G :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' q)
    refine Set.mem_iUnion.2 ⟨q, (φ (q.out⁻¹ * g) : ZariskiGL κ k),
      mem_mapSubgroup.2 ⟨_, Subgroup.mem_subgroupOf.1 hh, rfl⟩, ?_⟩
    show (φ q.out : ZariskiGL κ k) * (φ (q.out⁻¹ * g) : ZariskiGL κ k) = φ g
    rw [← Subgroup.coe_mul, ← map_mul, mul_inv_cancel_left]
  · intro hy
    obtain ⟨q, x, hx, rfl⟩ := Set.mem_iUnion.1 hy
    obtain ⟨g, -, rfl⟩ := mem_mapSubgroup.1 hx
    refine mem_mapSubgroup.2 ⟨q.out * g, (q.out * g).2, ?_⟩
    rw [map_mul, Subgroup.coe_mul]
    rfl

variable [IsAlgClosed k]

theorem isDomainImage_mapSubgroup {φ : G →* H} (hφ : IsMorphism φ)
    {L : Subgroup (ZariskiGL ι k)} (hLG : L ≤ G) (hLc : IsClosed (L : Set (ZariskiGL ι k)))
    (hLi : IsIrreducible (L : Set (ZariskiGL ι k))) :
    IsDomainImage k (pt '' (mapSubgroup φ L : Set (ZariskiGL κ k))) := by
  choose P hP using hφ
  let f : ↥(L : Set (ZariskiGL ι k)) → ZariskiGL κ k := fun v =>
    (φ ⟨v, hLG v.2⟩ : ZariskiGL κ k)
  have hrange : Set.range f = (mapSubgroup φ L : Set (ZariskiGL κ k)) := by
    ext y
    rw [SetLike.mem_coe, mem_mapSubgroup]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨⟨v, hLG v.2⟩, v.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [← hrange]
  refine isDomainImage_range isInducing_pt hLc hLi f
    (Matrix.of fun a b => glMk (P a b)) fun v => ?_
  ext a b
  simp [f, pt_glMk, hP]

theorem seminaire_exp3_image {φ : G →* H} (hφ : IsMorphism φ)
    (hG : IsClosed (G : Set (ZariskiGL ι k))) :
    mapSubgroup φ G ≤ H ∧ IsClosed (mapSubgroup φ G : Set (ZariskiGL κ k)) ∧
    mapSubgroup φ (identityComponent G) = identityComponent (mapSubgroup φ G) ∧
    (IsConnected (G : Set (ZariskiGL ι k)) →
      IsConnected (mapSubgroup φ G : Set (ZariskiGL κ k))) := by
  set G0 := identityComponent G with hG0
  have hdom := isDomainImage_mapSubgroup hφ (identityComponent_le G)
    (isClosed_identityComponent hG) (isIrreducible_identityComponent G)
  have himg0c : IsClosed (mapSubgroup φ G0 : Set (ZariskiGL κ k)) :=
    isClosed_of_isDomainImage hdom
  have himgc : IsClosed (mapSubgroup φ G : Set (ZariskiGL κ k)) := by
    rw [coe_mapSubgroup_eq_iUnion]
    exact isClosed_iUnion_of_finite fun q => himg0c.leftCoset _
  set L := mapSubgroup φ G with hL
  have hle : mapSubgroup φ G0 ≤ L := mapSubgroup_mono φ (identityComponent_le G)
  have hfin : ((mapSubgroup φ G0).subgroupOf L).FiniteIndex := by
    let ψ : G →* L :=
      (H.subtype.comp φ).codRestrict L fun g => mem_mapSubgroup.2 ⟨g, g.2, rfl⟩
    have hψ : Function.Surjective ψ := by
      rintro ⟨y, hy⟩
      obtain ⟨g, -, rfl⟩ := mem_mapSubgroup.1 hy
      exact ⟨g, rfl⟩
    have heq : (G0.subgroupOf G).map ψ = (mapSubgroup φ G0).subgroupOf L := by
      ext y
      rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, mem_mapSubgroup]
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g, Subgroup.mem_subgroupOf.1 hg, rfl⟩
      · rintro ⟨g, hg, hgy⟩
        exact ⟨g, Subgroup.mem_subgroupOf.2 hg, Subtype.ext hgy⟩
    rw [← heq]
    exact ⟨ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero
      ((G0.subgroupOf G).index_map_dvd hψ)⟩
  have h1 : identityComponent L ≤ mapSubgroup φ G0 := identityComponent_le_of_isClosed himg0c
  have h2 : mapSubgroup φ G0 ≤ identityComponent L := by
    have himg : Subtype.val '' (Subtype.val ⁻¹' (mapSubgroup φ G0 : Set (ZariskiGL κ k)) :
        Set L) = (mapSubgroup φ G0 : Set (ZariskiGL κ k)) :=
      Set.image_preimage_eq_of_subset fun y hy => ⟨⟨y, hle hy⟩, rfl⟩
    have h0 : IsIrreducible (Subtype.val '' (Subtype.val ⁻¹' (mapSubgroup φ G0 :
        Set (ZariskiGL κ k)) : Set L)) := by
      rw [himg]
      exact isIrreducible_of_isDomainImage hdom
    have hirr' : IsIrreducible
        (Subtype.val ⁻¹' (mapSubgroup φ G0 : Set (ZariskiGL κ k)) : Set ↥L) :=
      (isIrreducible_image_iff_of_isInducing IsInducing.subtypeVal).1 h0
    have hsub := subset_identityComponent (G := ↥L) hirr' (one_mem (mapSubgroup φ G0))
    intro y hy
    exact ⟨⟨y, hle hy⟩, hsub hy, rfl⟩
  refine ⟨mapSubgroup_le φ G, himgc, le_antisymm h2 h1, fun hconn => ?_⟩
  have hGG0 : G0 = G := by
    refine SetLike.coe_injective ?_
    rw [hG0, coe_identityComponent_eq_connectedComponentIn,
      hconn.isPreconnected.connectedComponentIn G.one_mem]
  have hirr : IsIrreducible (L : Set (ZariskiGL κ k)) := by
    rw [hL, ← congrArg (mapSubgroup φ) hGG0]
    exact isIrreducible_of_isDomainImage hdom
  exact hirr.isConnected

end Morphism

end ZariskiGL

end CFSG.LieType.AlgebraicGroups.SeminaireExp3
