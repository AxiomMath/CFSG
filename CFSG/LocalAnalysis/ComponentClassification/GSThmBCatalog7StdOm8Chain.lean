module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedNormal

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

variable {X : Type*} [Group X] (N Z : Subgroup X) [Z.Normal] (ψ : MulAut X)
  (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z)

@[expose] def chainHom : N.subgroupOf (fixedSubgroup ψ) →*
    fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ) :=
  (fixedProjection (Z.subgroupOf N) (restrictAutomorphism N ψ hN)
    (restricted_central_invariant N Z ψ hN hZ)).comp (fixedNormalEquiv N ψ hN).symm.toMonoidHom

theorem chainHom_val (x : N.subgroupOf (fixedSubgroup ψ)) :
    (chainHom N Z ψ hN hZ x).val =
      QuotientGroup.mk' (Z.subgroupOf N) (⟨x.val.val, x.property⟩ : N) := rfl

theorem chainHom_eq_one_iff (x : N.subgroupOf (fixedSubgroup ψ)) :
    chainHom N Z ψ hN hZ x = 1 ↔ x.val.val ∈ Z := by
  rw [← Subtype.val_inj, chainHom_val, OneMemClass.coe_one, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem chainHom_ker_central (hcentral : Z ≤ center X) :
    (chainHom N Z ψ hN hZ).ker ≤ center (N.subgroupOf (fixedSubgroup ψ)) := by
  intro x hx
  have hxZ : x.val.val ∈ Z := (chainHom_eq_one_iff N Z ψ hN hZ x).mp hx
  refine mem_center_iff.mpr fun y => Subtype.ext (Subtype.ext ?_)
  exact (mem_center_iff.mp (hcentral hxZ) y.val.val)

theorem restrict_fixedImageProjection_ker_central (hcentral : Z ≤ center X) :
    (fixedImageProjection (Z.subgroupOf N) (restrictAutomorphism N ψ hN)
      (restricted_central_invariant N Z ψ hN hZ)).ker ≤
        center (fixedSubgroup (restrictAutomorphism N ψ hN)) :=
  fixedImageProjection_kernel_central _ _ _ (central_subgroupOf N Z hcentral)

variable [Finite X]

theorem chain_up (hcentral : Z ≤ center X) (M : Subgroup (N.subgroupOf (fixedSubgroup ψ)))
    (hM : IsPComponent 2 M) : IsPComponent 2 (M.map (chainHom N Z ψ hN hZ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψN := restrictAutomorphism N ψ hN
  set hinv := restricted_central_invariant N Z ψ hN hZ
  let ι := (fixedNormalEquiv N ψ hN).symm
  let f := fixedImageProjection (Z.subgroupOf N) ψN hinv
  have hM' := CatalogueBAlternating.pComponent_map_equiv 2 ι M hM
  have hM'' := CatalogueBCentralQuotient.pComponent_map 2 f
    (fixedImageProjection_surjective _ _ _)
    (restrict_fixedImageProjection_ker_central N Z ψ hN hZ hcentral) _ hM'
  have := fixedImage_normal (Z.subgroupOf N) ψN hinv (central_subgroupOf N Z hcentral)
  have h3 := CatalogueBAlternating.pComponent_of_normal_subgroup 2 _ _ hM''
  have heq : ((M.map ι.toMonoidHom).map f).map (fixedImage (Z.subgroupOf N) ψN hinv).subtype =
      M.map (chainHom N Z ψ hN hZ) := by
    rw [map_map, map_map]
    rfl
  rwa [heq] at h3

theorem chain_down (hcentral : Z ≤ center X)
    (L : Subgroup (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)))
    (hL : IsPComponent 2 L) :
    ∃ M : Subgroup (N.subgroupOf (fixedSubgroup ψ)), IsPComponent 2 M ∧
      M.map (chainHom N Z ψ hN hZ) = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψN := restrictAutomorphism N ψ hN
  set hinv := restricted_central_invariant N Z ψ hN hZ
  let ι := fixedNormalEquiv N ψ hN
  let f := fixedImageProjection (Z.subgroupOf N) ψN hinv
  have hc := central_subgroupOf N Z hcentral
  have := fixedImage_normal (Z.subgroupOf N) ψN hinv hc
  have : Group.IsSolvable (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ) ⧸
      fixedImage (Z.subgroupOf N) ψN hinv) := by
    have hcomm := fixed_quotient_abelian (Z.subgroupOf N) ψN hinv hc
    exact Group.isSolvable_of_comm fun a b => hcomm.is_comm.comm a b
  obtain ⟨hle, hLres⟩ :=
    pComponent_in_normal_of_solvable_quotient 2 (fixedImage (Z.subgroupOf N) ψN hinv) L hL
  obtain ⟨M', hM', hmap, -⟩ := CatalogueBCentralQuotient.pComponent_exists_lift 2 f
    (fixedImageProjection_surjective _ _ _)
    (restrict_fixedImageProjection_ker_central N Z ψ hN hZ hcentral) _ hLres
  refine ⟨M'.map ι.toMonoidHom, CatalogueBAlternating.pComponent_map_equiv 2 ι M' hM', ?_⟩
  have h1 : (M'.map f).map (fixedImage (Z.subgroupOf N) ψN hinv).subtype = L := by
    rw [hmap]
    exact map_subgroupOf_eq_of_le hle
  rw [← h1, map_map, map_map]
  congr 1

omit [Finite X] in
theorem chain_inj (hcentral : Z ≤ center X) (M₁ M₂ : Subgroup (N.subgroupOf (fixedSubgroup ψ)))
    (h₁ : IsPComponent 2 M₁) (h₂ : IsPComponent 2 M₂)
    (h : M₁.map (chainHom N Z ψ hN hZ) = M₂.map (chainHom N Z ψ hN hZ)) : M₁ = M₂ := by
  set ψN := restrictAutomorphism N ψ hN
  set hinv := restricted_central_invariant N Z ψ hN hZ
  let ι := (fixedNormalEquiv N ψ hN).symm
  let f := fixedImageProjection (Z.subgroupOf N) ψN hinv
  have h' : (M₁.map ι.toMonoidHom).map f = (M₂.map ι.toMonoidHom).map f := by
    apply map_injective (fixedImage (Z.subgroupOf N) ψN hinv).subtype_injective
    rw [map_map, map_map, map_map, map_map]
    exact h
  have := CatalogueBCentralQuotient.pComponent_lift_unique 2 f
    (restrict_fixedImageProjection_ker_central N Z ψ hN hZ hcentral) _ _
    (CatalogueBAlternating.pComponent_map_equiv 2 ι M₁ h₁)
    (CatalogueBAlternating.pComponent_map_equiv 2 ι M₂ h₂) h'
  exact map_injective ι.injective this

theorem chain_normal_iff (M : Subgroup (N.subgroupOf (fixedSubgroup ψ))) [N.Normal] :
    IsPComponent 2 M ↔ IsPComponent 2 (M.map (N.subgroupOf (fixedSubgroup ψ)).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMM : (M.map (N.subgroupOf (fixedSubgroup ψ)).subtype).subgroupOf
      (N.subgroupOf (fixedSubgroup ψ)) = M :=
    comap_map_eq_self_of_injective (subtype_injective _) M
  rw [← pComponent_normal_iff 2 (N.subgroupOf (fixedSubgroup ψ)) _ (map_subtype_le M), hMM]

theorem chain_le [N.Normal] (hab : commutator X ≤ N) (M : Subgroup (fixedSubgroup ψ))
    (hM : IsPComponent 2 M) : M ≤ N.subgroupOf (fixedSubgroup ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsSolvable (fixedSubgroup ψ ⧸ N.subgroupOf (fixedSubgroup ψ)) := by
    have hcomm : commutator (fixedSubgroup ψ) ≤ N.subgroupOf (fixedSubgroup ψ) := by
      intro x hx
      rw [mem_subgroupOf]
      apply hab
      have h1 := map_mono (f := (fixedSubgroup ψ).subtype) (le_refl (commutator (fixedSubgroup ψ)))
      have h2 : (commutator (fixedSubgroup ψ)).map (fixedSubgroup ψ).subtype ≤ commutator X := by
        rw [_root_.commutator_def, _root_.commutator_def, map_commutator]
        exact commutator_mono le_top le_top
      exact h2 ⟨x, hx, rfl⟩
    have := (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr hcomm
    exact Group.isSolvable_of_comm fun a b => this.is_comm.comm a b
  exact (pComponent_in_normal_of_solvable_quotient 2 _ M hM).1

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
