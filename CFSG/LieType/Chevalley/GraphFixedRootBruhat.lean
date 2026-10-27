module

public import CFSG.LieType.Chevalley.GraphFixedRootMonomialQuotient

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

@[expose] def graphFixedRootBruhatCell
    (w : WeylGroup t.tag) : Set (ModGL t.tag K) :=
  (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) * {canonicalRep (coxeterSystem t.tag) K w} *
    (graphFixedRootBorel t K σ : Set (ModGL t.tag K))

variable {t K σ}

theorem mem_graphFixedRootBruhatCell
    {w : WeylGroup t.tag} {x : ModGL t.tag K} :
    x ∈ graphFixedRootBruhatCell t K σ w ↔ ∃ b ∈ graphFixedRootBorel t K σ,
      ∃ b' ∈ graphFixedRootBorel t K σ, b * canonicalRep (coxeterSystem t.tag) K w * b' = x := by
  simp only [graphFixedRootBruhatCell, Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩
    exact ⟨b, hb, b', hb', rfl⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩

theorem graphFixedPosUnipotent_le_graphFixedRootBorel :
    graphFixedPosUnipotent t K σ ≤ graphFixedRootBorel t K σ :=
  le_inf graphFixedPosUnipotent_le_graphFixedBorel
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ)

theorem graphFixedRootTorus_le_graphFixedRootBorel :
    graphFixedRootTorus t K σ ≤ graphFixedRootBorel t K σ :=
  inf_le_inf_right _ graphFixedTorus_le_graphFixedBorel

theorem graphFixedRootBruhatCell_subset
    (w : WeylGroup t.tag) :
    graphFixedRootBruhatCell t K σ w ⊆ graphFixedBruhatCell t K σ w := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hx
  exact mem_graphFixedBruhatCell.2 ⟨b, (Subgroup.mem_inf.1 hb).1, b', (Subgroup.mem_inf.1 hb').1,
    rfl⟩

theorem graphFixedRootBruhatCell_subset_graphFixedRootGroup
    {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) :
    graphFixedRootBruhatCell t K σ w ⊆ (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hx
  exact mul_mem (mul_mem (graphFixedRootBorel_le t K σ hb)
    (canonicalRep_mem_graphFixedRootGroup hw)) (graphFixedRootBorel_le t K σ hb')

theorem disjoint_graphFixedRootBruhatCell
    {w w' : WeylGroup t.tag} (h : w ≠ w') :
    Disjoint (graphFixedRootBruhatCell t K σ w) (graphFixedRootBruhatCell t K σ w') :=
  (disjoint_graphFixedBruhatCell h).mono (graphFixedRootBruhatCell_subset w)
    (graphFixedRootBruhatCell_subset w')

theorem graphFixedRoot_mul_unique
    {h₁ h₂ u₁ u₂ : ModGL t.tag K}
    (hh₁ : h₁ ∈ graphFixedRootTorus t K σ) (hh₂ : h₂ ∈ graphFixedRootTorus t K σ)
    (hu₁ : u₁ ∈ graphFixedPosUnipotent t K σ) (hu₂ : u₂ ∈ graphFixedPosUnipotent t K σ)
    (h : h₁ * u₁ = h₂ * u₂) : h₁ = h₂ ∧ u₁ = u₂ :=
  graphFixed_mul_unique (Subgroup.mem_inf.1 hh₁).1 (Subgroup.mem_inf.1 hh₂).1 hu₁ hu₂ h

theorem graphFixedRoot_mul_unique'
    {h₁ h₂ u₁ u₂ : ModGL t.tag K}
    (hh₁ : h₁ ∈ graphFixedRootTorus t K σ) (hh₂ : h₂ ∈ graphFixedRootTorus t K σ)
    (hu₁ : u₁ ∈ graphFixedPosUnipotent t K σ) (hu₂ : u₂ ∈ graphFixedPosUnipotent t K σ)
    (h : u₁ * h₁ = u₂ * h₂) : u₁ = u₂ ∧ h₁ = h₂ :=
  graphFixed_mul_unique' (Subgroup.mem_inf.1 hh₁).1 (Subgroup.mem_inf.1 hh₂).1 hu₁ hu₂ h

theorem graphFixedRootTorus_mul_comm
    {g g' : ModGL t.tag K} (hg : g ∈ graphFixedRootTorus t K σ)
    (hg' : g' ∈ graphFixedRootTorus t K σ) : g * g' = g' * g :=
  graphFixedTorus_mul_comm (Subgroup.mem_inf.1 hg).1 (Subgroup.mem_inf.1 hg').1

theorem graphFixedPosUnipotent_subgroupOf_graphFixedRootBorel_normal :
    ((graphFixedPosUnipotent t K σ).subgroupOf (graphFixedRootBorel t K σ)).Normal := by
  have hN := graphFixedPosUnipotent_subgroupOf_normal (t := t) (K := K) (σ := σ)
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h := hN.conj_mem ⟨n, (Subgroup.mem_inf.1 n.2).1⟩ (Subgroup.mem_subgroupOf.2 hn)
    ⟨g, (Subgroup.mem_inf.1 g.2).1⟩
  exact Subgroup.mem_subgroupOf.1 h

variable (hσ : Function.Surjective σ)
include hσ

theorem graphFixedRootBorel_eq_mul :
    (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) =
      (graphFixedRootTorus t K σ : Set (ModGL t.tag K)) *
        (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) := by
  refine Set.Subset.antisymm (fun b hb => ?_) ?_
  · obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.1 hb
    have hb' : b ∈ (graphFixedBorel t K σ : Set (ModGL t.tag K)) := hbB
    rw [graphFixedBorel_eq_mul hσ] at hb'
    obtain ⟨h, hh, u, hu, rfl⟩ := hb'
    have huC := graphFixedPosUnipotent_le_graphFixedRootGroup t K σ hu
    have hhC : h ∈ graphFixedRootGroup t K σ := by
      have e : h = h * u * u⁻¹ := by group
      rw [e]
      exact mul_mem hbC (inv_mem huC)
    exact ⟨h, Subgroup.mem_inf.2 ⟨hh, hhC⟩, u, hu, rfl⟩
  · rintro _ ⟨h, hh, u, hu, rfl⟩
    exact mul_mem (graphFixedRootTorus_le_graphFixedRootBorel hh)
      (graphFixedPosUnipotent_le_graphFixedRootBorel hu)

theorem graphFixedRootBorel_eq_mul' :
    (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) =
      (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) *
        (graphFixedRootTorus t K σ : Set (ModGL t.tag K)) := by
  refine Set.Subset.antisymm (fun b hb => ?_) ?_
  · have hb' : b⁻¹ ∈ (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) := inv_mem hb
    rw [graphFixedRootBorel_eq_mul hσ] at hb'
    obtain ⟨h, hh, u, hu, hhu⟩ := hb'
    refine ⟨u⁻¹, inv_mem hu, h⁻¹, inv_mem hh, ?_⟩
    simp only at hhu ⊢
    rw [← mul_inv_rev, hhu, inv_inv]
  · rintro _ ⟨u, hu, h, hh, rfl⟩
    exact mul_mem (graphFixedPosUnipotent_le_graphFixedRootBorel hu)
      (graphFixedRootTorus_le_graphFixedRootBorel hh)

theorem isSolvable_graphFixedRootBorel
    : Group.IsSolvable (graphFixedRootBorel t K σ) := by
  set U : Subgroup (graphFixedRootBorel t K σ) :=
    (graphFixedPosUnipotent t K σ).subgroupOf (graphFixedRootBorel t K σ) with hUdef
  have : U.Normal := graphFixedPosUnipotent_subgroupOf_graphFixedRootBorel_normal
  have := isNilpotent_graphFixedPosUnipotent (t := t) (K := K) (σ := σ)
  have : Group.IsSolvable U := Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe graphFixedPosUnipotent_le_graphFixedRootBorel).toMonoidHom)
    (MulEquiv.injective _)
  have key : ∀ x : graphFixedRootBorel t K σ, ∃ h ∈ graphFixedRootTorus t K σ,
      ∃ hB : h ∈ graphFixedRootBorel t K σ,
        (QuotientGroup.mk x : graphFixedRootBorel t K σ ⧸ U) = QuotientGroup.mk ⟨h, hB⟩ := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) := hx
    rw [graphFixedRootBorel_eq_mul hσ] at hx'
    obtain ⟨h, hh, u, hu, rfl⟩ := hx'
    refine ⟨h, hh, graphFixedRootTorus_le_graphFixedRootBorel hh, ?_⟩
    rw [QuotientGroup.eq, hUdef, Subgroup.mem_subgroupOf]
    change (h * u)⁻¹ * h ∈ graphFixedPosUnipotent t K σ
    rw [show (h * u)⁻¹ * h = u⁻¹ by group]
    exact inv_mem hu
  have : Group.IsSolvable (graphFixedRootBorel t K σ ⧸ U) := Group.isSolvable_of_comm fun a b => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨h, hh, hB, hxh⟩ := key x
    obtain ⟨h', hh', hB', hyh⟩ := key y
    rw [hxh, hyh, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext (graphFixedRootTorus_mul_comm hh hh'))
  exact Group.isSolvable_of_subgroup_quotient U

theorem exists_root_bruhat_factor
    {w : WeylGroup t.tag} {g : ModGL t.tag K}
    (hg : g ∈ graphFixedRootGroup t K σ) (hw : w ∈ relWeylTwist t)
    (hgw : g ∈ graphFixedBruhatCell t K σ w) :
    ∃ b ∈ graphFixedRootBorel t K σ, ∃ u ∈ graphFixedInversionUnipotent t K σ w,
      b * canonicalRep (coxeterSystem t.tag) K w * u = g := by
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, rfl⟩ := (bijOn_graphFixedBruhatCell hσ hw).2.2 hgw
  simp only at hb hu hg ⊢
  have hnC := canonicalRep_mem_graphFixedRootGroup (K := K) (σ := σ) hw
  have huC := graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
    (graphFixedInversionUnipotent_le_graphFixedPosUnipotent w hu)
  have hbC : b ∈ graphFixedRootGroup t K σ := by
    have e : b = b * canonicalRep (coxeterSystem t.tag) K w * u * u⁻¹ *
        (canonicalRep (coxeterSystem t.tag) K w)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hg (inv_mem huC)) (inv_mem hnC)
  exact ⟨b, Subgroup.mem_inf.2 ⟨hb, hbC⟩, u, hu, rfl⟩

theorem graphFixedRootBruhatCell_eq_inter
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    graphFixedRootBruhatCell t K σ w =
      (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) ∩ graphFixedBruhatCell t K σ w := by
  refine Set.Subset.antisymm (fun x hx =>
    ⟨graphFixedRootBruhatCell_subset_graphFixedRootGroup hw hx,
      graphFixedRootBruhatCell_subset w hx⟩) fun x ⟨hxC, hxw⟩ => ?_
  obtain ⟨b, hb, u, hu, rfl⟩ := exists_root_bruhat_factor hσ hxC hw hxw
  exact mem_graphFixedRootBruhatCell.2 ⟨b, hb, u, graphFixedPosUnipotent_le_graphFixedRootBorel
    (graphFixedInversionUnipotent_le_graphFixedPosUnipotent w hu), rfl⟩

theorem bijOn_graphFixedRootBruhatCell
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    Set.BijOn (fun p : ModGL t.tag K × ModGL t.tag K =>
        p.1 * canonicalRep (coxeterSystem t.tag) K w * p.2)
      ((graphFixedRootBorel t K σ : Set (ModGL t.tag K)) ×ˢ
        (graphFixedInversionUnipotent t K σ w : Set (ModGL t.tag K)))
      (graphFixedRootBruhatCell t K σ w) := by
  refine ⟨fun p hp => mem_graphFixedRootBruhatCell.2 ⟨p.1, hp.1, p.2,
      graphFixedPosUnipotent_le_graphFixedRootBorel
        (graphFixedInversionUnipotent_le_graphFixedPosUnipotent w hp.2), rfl⟩,
    fun p hp q hq h => (bijOn_graphFixedBruhatCell hσ hw).2.1
      (Set.mem_prod.2 ⟨(Subgroup.mem_inf.1 hp.1).1, hp.2⟩)
      (Set.mem_prod.2 ⟨(Subgroup.mem_inf.1 hq.1).1, hq.2⟩) h,
    fun x hx => ?_⟩
  rw [graphFixedRootBruhatCell_eq_inter hσ hw] at hx
  obtain ⟨b, hb, u, hu, rfl⟩ := exists_root_bruhat_factor hσ hx.1 hw hx.2
  exact ⟨(b, u), ⟨hb, hu⟩, rfl⟩

theorem graphFixedRootGroup_eq_iUnion :
    (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) =
      ⋃ w : relWeylTwist t, graphFixedRootBruhatCell t K σ w := by
  refine Set.Subset.antisymm (fun g hg => ?_)
    (Set.iUnion_subset fun w => graphFixedRootBruhatCell_subset_graphFixedRootGroup w.2)
  have hgΓ : g ∈ twistedFixedGroup t K σ := graphFixedRootGroup_le t K σ hg
  have hgΓ' : g ∈ ⋃ w : relWeylTwist t, graphFixedBruhatCell t K σ w := by
    rw [← twistedFixedGroup_eq_iUnion_graphFixedBruhatCell hσ]
    exact hgΓ
  obtain ⟨⟨w, hwρ⟩, hw⟩ := Set.mem_iUnion.1 hgΓ'
  obtain ⟨b, hb, u, hu, rfl⟩ := exists_root_bruhat_factor hσ hg hwρ hw
  exact Set.mem_iUnion.2 ⟨⟨w, hwρ⟩, mem_graphFixedRootBruhatCell.2 ⟨b, hb, u,
    graphFixedPosUnipotent_le_graphFixedRootBorel
      (graphFixedInversionUnipotent_le_graphFixedPosUnipotent w hu), rfl⟩⟩

theorem graphFixedRootGroup_eq_sup_graphFixedRootMonomial :
    graphFixedRootGroup t K σ = graphFixedRootBorel t K σ ⊔ graphFixedRootMonomial t K σ := by
  refine le_antisymm (fun g hg => ?_)
    (sup_le (graphFixedRootBorel_le t K σ) (graphFixedRootMonomial_le t K σ))
  have hg' : g ∈ (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := hg
  rw [graphFixedRootGroup_eq_iUnion hσ] at hg'
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hw
  exact mul_mem (mul_mem (Subgroup.mem_sup_left hb)
    (Subgroup.mem_sup_right (canonicalRep_mem_graphFixedRootMonomial t K σ w.2)))
    (Subgroup.mem_sup_left hb')

theorem graphFixedRootGroup_eq_sup_closure :
    graphFixedRootGroup t K σ = graphFixedRootBorel t K σ ⊔ Subgroup.closure
      (Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) := by
  rw [graphFixedRootGroup_eq_sup_graphFixedRootMonomial hσ, graphFixedRootMonomial_eq_sup,
    ← sup_assoc, sup_eq_left.2 graphFixedRootTorus_le_graphFixedRootBorel]

omit hσ

theorem fixed_root_Bruhat_decomposition
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K) :
    ((graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) =
      (graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
        (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K))) ∧
    ((graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) =
      (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) *
        (graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K))) ∧
    (∀ h₁ ∈ graphFixedRootTorus t K σ.toRingHom, ∀ h₂ ∈ graphFixedRootTorus t K σ.toRingHom,
      ∀ u₁ ∈ graphFixedPosUnipotent t K σ.toRingHom,
      ∀ u₂ ∈ graphFixedPosUnipotent t K σ.toRingHom,
        h₁ * u₁ = h₂ * u₂ → h₁ = h₂ ∧ u₁ = u₂) ∧
    (∀ h₁ ∈ graphFixedRootTorus t K σ.toRingHom, ∀ h₂ ∈ graphFixedRootTorus t K σ.toRingHom,
      ∀ u₁ ∈ graphFixedPosUnipotent t K σ.toRingHom,
      ∀ u₂ ∈ graphFixedPosUnipotent t K σ.toRingHom,
        u₁ * h₁ = u₂ * h₂ → u₁ = u₂ ∧ h₁ = h₂) ∧
    graphFixedPosUnipotent t K σ.toRingHom ≤ graphFixedRootBorel t K σ.toRingHom ∧
    ((graphFixedPosUnipotent t K σ.toRingHom).subgroupOf
      (graphFixedRootBorel t K σ.toRingHom)).Normal ∧
    Group.IsNilpotent (graphFixedPosUnipotent t K σ.toRingHom) ∧
    (∀ g ∈ graphFixedRootTorus t K σ.toRingHom, ∀ g' ∈ graphFixedRootTorus t K σ.toRingHom,
      g * g' = g' * g) ∧
    Group.IsSolvable (graphFixedRootBorel t K σ.toRingHom) ∧
    (graphFixedRootGroup t K σ.toRingHom : Set (ModGL t.tag K)) =
      ⋃ w : relWeylTwist t, graphFixedRootBruhatCell t K σ.toRingHom w ∧
    (∀ w w' : WeylGroup t.tag, w ≠ w' →
      Disjoint (graphFixedRootBruhatCell t K σ.toRingHom w)
        (graphFixedRootBruhatCell t K σ.toRingHom w')) ∧
    (∀ w ∈ relWeylTwist t,
      Set.BijOn (fun p : ModGL t.tag K × ModGL t.tag K =>
          p.1 * canonicalRep (coxeterSystem t.tag) K w * p.2)
        ((graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) ×ˢ
          (graphFixedInversionUnipotent t K σ.toRingHom w : Set (ModGL t.tag K)))
        (graphFixedRootBruhatCell t K σ.toRingHom w) ∧
      graphFixedRootBruhatCell t K σ.toRingHom w =
        (graphFixedRootGroup t K σ.toRingHom : Set (ModGL t.tag K)) ∩
          graphFixedBruhatCell t K σ.toRingHom w) ∧
    graphFixedRootGroup t K σ.toRingHom =
      graphFixedRootBorel t K σ.toRingHom ⊔ graphFixedRootMonomial t K σ.toRingHom ∧
    graphFixedRootGroup t K σ.toRingHom = graphFixedRootBorel t K σ.toRingHom ⊔ Subgroup.closure
      (Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) :=
  ⟨graphFixedRootBorel_eq_mul σ.surjective, graphFixedRootBorel_eq_mul' σ.surjective,
    fun _ hh₁ _ hh₂ _ hu₁ _ hu₂ h => graphFixedRoot_mul_unique hh₁ hh₂ hu₁ hu₂ h,
    fun _ hh₁ _ hh₂ _ hu₁ _ hu₂ h => graphFixedRoot_mul_unique' hh₁ hh₂ hu₁ hu₂ h,
    graphFixedPosUnipotent_le_graphFixedRootBorel,
    graphFixedPosUnipotent_subgroupOf_graphFixedRootBorel_normal,
    isNilpotent_graphFixedPosUnipotent,
    fun _ hg _ hg' => graphFixedRootTorus_mul_comm hg hg',
    isSolvable_graphFixedRootBorel σ.surjective,
    graphFixedRootGroup_eq_iUnion σ.surjective,
    fun _ _ h => disjoint_graphFixedRootBruhatCell h,
    fun _ hw => ⟨bijOn_graphFixedRootBruhatCell σ.surjective hw,
      graphFixedRootBruhatCell_eq_inter σ.surjective hw⟩,
    graphFixedRootGroup_eq_sup_graphFixedRootMonomial σ.surjective,
    graphFixedRootGroup_eq_sup_closure σ.surjective⟩

end CFSG.LieType.Chevalley
