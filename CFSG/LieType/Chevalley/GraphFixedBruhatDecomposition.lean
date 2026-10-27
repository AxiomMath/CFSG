module

public import CFSG.LieType.Chevalley.GraphFixedMonomialQuotient
public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.LieType.Chevalley.HeightSeries

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

@[expose] def graphFixedBruhatCell
    (w : WeylGroup t.tag) : Set (ModGL t.tag K) :=
  (graphFixedBorel t K σ : Set (ModGL t.tag K)) * {canonicalRep (coxeterSystem t.tag) K w} *
    (graphFixedBorel t K σ : Set (ModGL t.tag K))

variable {t K σ}

theorem mem_graphFixedBruhatCell
    {w : WeylGroup t.tag} {x : ModGL t.tag K} :
    x ∈ graphFixedBruhatCell t K σ w ↔ ∃ b ∈ graphFixedBorel t K σ,
      ∃ b' ∈ graphFixedBorel t K σ, b * canonicalRep (coxeterSystem t.tag) K w * b' = x := by
  simp only [graphFixedBruhatCell, Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩
    exact ⟨b, hb, b', hb', rfl⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩

section Ambient

variable (hσ : Function.Surjective σ)
include hσ

theorem twistHom_mem_borelGroup
    {b : ModGL t.tag K} (hb : b ∈ borelGroup t.tag K) :
    twistHom t K σ b ∈ borelGroup t.tag K := by
  rw [← map_twistHom_borelGroup t K hσ]
  exact Subgroup.mem_map_of_mem _ hb

theorem twistHom_mem_torusGroup'
    {h : ModGL t.tag K} (hh : h ∈ torusGroup t.tag K) :
    twistHom t K σ h ∈ torusGroup t.tag K := by
  rw [← map_twistHom_torusGroup t K hσ]
  exact Subgroup.mem_map_of_mem _ hh

theorem twistHom_mem_posUnipotent
    {u : ModGL t.tag K} (hu : u ∈ posUnipotent t.tag K) :
    twistHom t K σ u ∈ posUnipotent t.tag K := by
  rw [← map_twistHom_posUnipotent t K hσ]
  exact Subgroup.mem_map_of_mem _ hu

theorem twistHom_mem_rootSpan_inversionSet
    {w : WeylGroup t.tag} (hw : weylTwist t w = w)
    {u : ModGL t.tag K} (hu : u ∈ rootSpan t.tag K (inversionSet w)) :
    twistHom t K σ u ∈ rootSpan t.tag K (inversionSet w) := by
  have himg : permLattice t.perm '' inversionSet w = inversionSet w := by
    ext β
    constructor
    · rintro ⟨α, ⟨hα, hpos, -, hneg⟩, rfl⟩
      refine ⟨hα.permLattice t.cartan_perm, by rwa [height_permLattice],
        IsRoot.smul (hα.permLattice t.cartan_perm) w, ?_⟩
      rw [← hw, weylTwist_smul_permLattice, height_permLattice]
      exact hneg
    · rintro ⟨hβ, hpos, -, hneg⟩
      refine ⟨permLattice t.perm.symm β, ⟨hβ.permLattice (cartan_perm_symm t.cartan_perm),
        by rwa [height_permLattice], IsRoot.smul (hβ.permLattice (cartan_perm_symm t.cartan_perm))
          w, ?_⟩, permLattice_permLattice_symm _ _⟩
      have h := weylTwist_smul_permLattice t w (permLattice t.perm.symm β)
      rw [hw, permLattice_permLattice_symm] at h
      rw [← height_permLattice t.perm, ← h]
      exact hneg
  rw [← himg, ← map_twistHom_rootSpan t K hσ fun α hα => hα.1]
  exact Subgroup.mem_map_of_mem _ hu

theorem twistHom_mem_bruhatCell
    {w : WeylGroup t.tag} {x : ModGL t.tag K}
    (hx : x ∈ bruhatCell t.tag K w) : twistHom t K σ x ∈ bruhatCell t.tag K (weylTwist t w) := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx
  refine mem_bruhatCell.2 ⟨twistHom t K σ b, twistHom_mem_borelGroup hσ hb,
    twistHom t K σ b', twistHom_mem_borelGroup hσ hb', ?_⟩
  rw [map_mul, map_mul, twistHom_canonicalRep]

end Ambient

theorem borelGroup_le_adjointGroup
    : borelGroup t.tag K ≤ adjointGroup t.tag K :=
  ((triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.2.2.2.2.2 K).1

theorem mem_twistedFixedGroup_of_mem_borelGroup
    {b : ModGL t.tag K}
    (hb : b ∈ borelGroup t.tag K) (hF : twistHom t K σ b = b) : b ∈ twistedFixedGroup t K σ :=
  (mem_twistedFixedGroup_iff_twistHom t K σ).2 ⟨borelGroup_le_adjointGroup hb, hF⟩

theorem twistHom_eq_of_mem_twistedFixedGroup {g : ModGL t.tag K}
    (hg : g ∈ twistedFixedGroup t K σ) : twistHom t K σ g = g :=
  ((mem_twistedFixedGroup_iff_twistHom t K σ).1 hg).2

theorem graphFixedTorus_le_graphFixedBorel :
    graphFixedTorus t K σ ≤ graphFixedBorel t K σ :=
  inf_le_inf_right _ torusGroup_le_borelGroup

theorem graphFixedPosUnipotent_le_graphFixedBorel :
    graphFixedPosUnipotent t K σ ≤ graphFixedBorel t K σ :=
  inf_le_inf_right _ le_sup_right

theorem graphFixedInversionUnipotent_le_graphFixedPosUnipotent
    (w : WeylGroup t.tag) :
    graphFixedInversionUnipotent t K σ w ≤ graphFixedPosUnipotent t K σ :=
  inf_le_inf_right _ (rootSpan_le_posUnipotent fun _ h => inversionSet_pos (w := w) h)

variable (hσ : Function.Surjective σ)
include hσ

theorem graphFixedBorel_eq_mul :
    (graphFixedBorel t K σ : Set (ModGL t.tag K)) =
      (graphFixedTorus t K σ : Set (ModGL t.tag K)) *
        (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) := by
  obtain ⟨-, -, -, -, hHU, -, huniq, -⟩ := triangular_borel_structure.{0, 0} t.tag K
  refine Set.Subset.antisymm (fun b hb => ?_) ?_
  · obtain ⟨hbB, hbΓ⟩ := Subgroup.mem_inf.1 hb
    have hb' : b ∈ (torusGroup t.tag K : Set (ModGL t.tag K)) *
        (posUnipotent t.tag K : Set (ModGL t.tag K)) := by
      rw [← hHU]
      exact hbB
    obtain ⟨h, hh, u, hu, rfl⟩ := hb'
    have hF := twistHom_eq_of_mem_twistedFixedGroup hbΓ
    rw [map_mul] at hF
    obtain ⟨h1, h2⟩ := huniq _ (twistHom_mem_torusGroup' hσ hh) _ hh _
      (twistHom_mem_posUnipotent hσ hu) _ hu hF
    exact ⟨h, Subgroup.mem_inf.2 ⟨hh, mem_twistedFixedGroup_of_mem_borelGroup
      (torusGroup_le_borelGroup hh) h1⟩, u, Subgroup.mem_inf.2 ⟨hu,
        mem_twistedFixedGroup_of_mem_borelGroup (Subgroup.mem_sup_right hu) h2⟩, rfl⟩
  · rintro _ ⟨h, hh, u, hu, rfl⟩
    exact mul_mem (graphFixedTorus_le_graphFixedBorel hh)
      (graphFixedPosUnipotent_le_graphFixedBorel hu)

theorem graphFixedBorel_eq_mul' :
    (graphFixedBorel t K σ : Set (ModGL t.tag K)) =
      (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) *
        (graphFixedTorus t K σ : Set (ModGL t.tag K)) := by
  refine Set.Subset.antisymm (fun b hb => ?_) ?_
  · have hb' : b⁻¹ ∈ (graphFixedBorel t K σ : Set (ModGL t.tag K)) := inv_mem hb
    rw [graphFixedBorel_eq_mul hσ] at hb'
    obtain ⟨h, hh, u, hu, hhu⟩ := hb'
    refine ⟨u⁻¹, inv_mem hu, h⁻¹, inv_mem hh, ?_⟩
    simp only at hhu ⊢
    rw [← mul_inv_rev, hhu, inv_inv]
  · rintro _ ⟨u, hu, h, hh, rfl⟩
    exact mul_mem (graphFixedPosUnipotent_le_graphFixedBorel hu)
      (graphFixedTorus_le_graphFixedBorel hh)

theorem exists_fixed_bruhat_factor
    {w : WeylGroup t.tag} {g : ModGL t.tag K}
    (hg : g ∈ twistedFixedGroup t K σ) (hgw : g ∈ bruhatCell t.tag K w) :
    weylTwist t w = w ∧ ∃ b ∈ graphFixedBorel t K σ, ∃ u ∈ graphFixedInversionUnipotent t K σ w,
      b * canonicalRep (coxeterSystem t.tag) K w * u = g := by
  have hF := twistHom_eq_of_mem_twistedFixedGroup hg
  have hδ : weylTwist t w = w := bruhatCell_injective (bruhatCell_eq_of_mem
    (hF ▸ twistHom_mem_bruhatCell hσ hgw) hgw)
  refine ⟨hδ, ?_⟩
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, rfl⟩ := (bijOn_bruhatCell (K := K) w).2.2 hgw
  simp only at hb hu hF ⊢
  rw [map_mul, map_mul, twistHom_canonicalRep, hδ] at hF
  have h := (bijOn_bruhatCell (K := K) w).2.1
    (Set.mk_mem_prod (twistHom_mem_borelGroup hσ hb)
      (twistHom_mem_rootSpan_inversionSet hσ hδ hu)) (Set.mk_mem_prod hb hu) hF
  simp only [Prod.mk.injEq] at h
  have hIB : rootSpan t.tag K (inversionSet w) ≤ borelGroup t.tag K :=
    (rootSpan_le_posUnipotent fun _ h => inversionSet_pos (w := w) h).trans le_sup_right
  exact ⟨b, Subgroup.mem_inf.2 ⟨hb, mem_twistedFixedGroup_of_mem_borelGroup hb h.1⟩, u,
    Subgroup.mem_inf.2 ⟨hu, mem_twistedFixedGroup_of_mem_borelGroup (hIB hu) h.2⟩, rfl⟩

omit hσ

theorem graphFixedBruhatCell_subset
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    graphFixedBruhatCell t K σ w ⊆ (twistedFixedGroup t K σ : Set (ModGL t.tag K)) := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedBruhatCell.1 hx
  exact mul_mem (mul_mem (graphFixedBorel_le t K σ hb)
    (canonicalRep_mem_twistedFixedGroup t K σ hw)) (graphFixedBorel_le t K σ hb')

theorem graphFixedBruhatCell_subset_bruhatCell
    (w : WeylGroup t.tag) :
    graphFixedBruhatCell t K σ w ⊆ bruhatCell t.tag K w := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedBruhatCell.1 hx
  exact mem_bruhatCell.2 ⟨b, (Subgroup.mem_inf.1 hb).1, b', (Subgroup.mem_inf.1 hb').1, rfl⟩

include hσ

theorem graphFixedBruhatCell_eq_inter
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    graphFixedBruhatCell t K σ w =
      (twistedFixedGroup t K σ : Set (ModGL t.tag K)) ∩ bruhatCell t.tag K w := by
  refine Set.Subset.antisymm (fun x hx => ⟨graphFixedBruhatCell_subset hw hx,
    graphFixedBruhatCell_subset_bruhatCell w hx⟩) fun x ⟨hxΓ, hxw⟩ => ?_
  obtain ⟨-, b, hb, u, hu, rfl⟩ := exists_fixed_bruhat_factor hσ hxΓ hxw
  exact mem_graphFixedBruhatCell.2 ⟨b, hb, u, graphFixedPosUnipotent_le_graphFixedBorel
    (graphFixedInversionUnipotent_le_graphFixedPosUnipotent w hu), rfl⟩

theorem bijOn_graphFixedBruhatCell
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    Set.BijOn (fun p : ModGL t.tag K × ModGL t.tag K =>
        p.1 * canonicalRep (coxeterSystem t.tag) K w * p.2)
      ((graphFixedBorel t K σ : Set (ModGL t.tag K)) ×ˢ
        (graphFixedInversionUnipotent t K σ w : Set (ModGL t.tag K)))
      (graphFixedBruhatCell t K σ w) := by
  refine ⟨fun p hp => mem_graphFixedBruhatCell.2 ⟨p.1, hp.1, p.2,
      graphFixedPosUnipotent_le_graphFixedBorel
        (graphFixedInversionUnipotent_le_graphFixedPosUnipotent w hp.2), rfl⟩,
    fun p hp q hq h => (bijOn_bruhatCell (K := K) w).2.1
      (Set.mem_prod.2 ⟨(Subgroup.mem_inf.1 hp.1).1, (Subgroup.mem_inf.1 hp.2).1⟩)
      (Set.mem_prod.2 ⟨(Subgroup.mem_inf.1 hq.1).1, (Subgroup.mem_inf.1 hq.2).1⟩) h,
    fun x hx => ?_⟩
  rw [graphFixedBruhatCell_eq_inter hσ hw] at hx
  obtain ⟨-, b, hb, u, hu, rfl⟩ := exists_fixed_bruhat_factor hσ hx.1 hx.2
  exact ⟨(b, u), ⟨hb, hu⟩, rfl⟩

theorem twistedFixedGroup_eq_iUnion_graphFixedBruhatCell :
    (twistedFixedGroup t K σ : Set (ModGL t.tag K)) =
      ⋃ w : relWeylTwist t, graphFixedBruhatCell t K σ w := by
  refine Set.Subset.antisymm (fun g hg => ?_)
    (Set.iUnion_subset fun w => graphFixedBruhatCell_subset w.2)
  have hgC : g ∈ (adjointGroup t.tag K : Set (ModGL t.tag K)) :=
    ((mem_twistedFixedGroup_iff_twistHom t K σ).1 hg).1
  rw [adjointGroup_eq_iUnion_bruhatCell] at hgC
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hgC
  obtain ⟨hδ, b, hb, u, hu, rfl⟩ := exists_fixed_bruhat_factor hσ hg hw
  exact Set.mem_iUnion.2 ⟨⟨w, hδ⟩, mem_graphFixedBruhatCell.2 ⟨b, hb, u,
    graphFixedPosUnipotent_le_graphFixedBorel
      (graphFixedInversionUnipotent_le_graphFixedPosUnipotent w hu), rfl⟩⟩

omit hσ

theorem disjoint_graphFixedBruhatCell
    {w w' : WeylGroup t.tag} (h : w ≠ w') :
    Disjoint (graphFixedBruhatCell t K σ w) (graphFixedBruhatCell t K σ w') :=
  (disjoint_bruhatCell h).mono (graphFixedBruhatCell_subset_bruhatCell w)
    (graphFixedBruhatCell_subset_bruhatCell w')

include hσ

theorem twistedFixedGroup_eq_sup_graphFixedMonomial :
    twistedFixedGroup t K σ = graphFixedBorel t K σ ⊔ graphFixedMonomial t K σ := by
  refine le_antisymm (fun g hg => ?_)
    (sup_le (graphFixedBorel_le t K σ) (graphFixedMonomial_le t K σ))
  have hg' : g ∈ (twistedFixedGroup t K σ : Set (ModGL t.tag K)) := hg
  rw [twistedFixedGroup_eq_iUnion_graphFixedBruhatCell hσ] at hg'
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedBruhatCell.1 hw
  exact mul_mem (mul_mem (Subgroup.mem_sup_left hb)
    (Subgroup.mem_sup_right (canonicalRep_mem_graphFixedMonomial t K σ w.2)))
    (Subgroup.mem_sup_left hb')

theorem twistedFixedGroup_eq_sup_closure :
    twistedFixedGroup t K σ = graphFixedBorel t K σ ⊔ Subgroup.closure
      (Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) := by
  rw [twistedFixedGroup_eq_sup_graphFixedMonomial hσ, graphFixedMonomial_eq_sup, ← sup_assoc,
    sup_eq_left.2 (graphFixedTorus_le_graphFixedBorel)]

theorem card_twistedFixedGroup
    [Finite K] :
    Nat.card (twistedFixedGroup t K σ) = Nat.card (graphFixedBorel t K σ) *
      ∑ᶠ w : relWeylTwist t, Nat.card (graphFixedInversionUnipotent t K σ w) := by
  classical
  have : Fintype (relWeylTwist t) := Fintype.ofFinite _
  have : Finite (Module.End K (RootModule t.tag K)) := Module.finite_of_finite K
  have e : (twistedFixedGroup t K σ : Set (ModGL t.tag K)) ≃
      Σ w : relWeylTwist t, graphFixedBruhatCell t K σ w := by
    rw [twistedFixedGroup_eq_iUnion_graphFixedBruhatCell hσ]
    exact Set.unionEqSigmaOfDisjoint fun w w' h =>
      disjoint_graphFixedBruhatCell fun h' => h (Subtype.ext h')
  have hcell : ∀ w : relWeylTwist t, Nat.card (graphFixedBruhatCell t K σ w) =
      Nat.card (graphFixedBorel t K σ) * Nat.card (graphFixedInversionUnipotent t K σ w) := by
    intro w
    rw [← Nat.card_congr (bijOn_graphFixedBruhatCell hσ w.2).equiv,
      Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
    rfl
  calc Nat.card (twistedFixedGroup t K σ) =
        Nat.card (Σ w : relWeylTwist t, graphFixedBruhatCell t K σ w) := Nat.card_congr e
    _ = ∑ w : relWeylTwist t, Nat.card (graphFixedBruhatCell t K σ w) := Nat.card_sigma
    _ = _ := by
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => hcell w

omit hσ

theorem graphFixed_mul_unique
    {h₁ h₂ u₁ u₂ : ModGL t.tag K} (hh₁ : h₁ ∈ graphFixedTorus t K σ)
    (hh₂ : h₂ ∈ graphFixedTorus t K σ) (hu₁ : u₁ ∈ graphFixedPosUnipotent t K σ)
    (hu₂ : u₂ ∈ graphFixedPosUnipotent t K σ) (h : h₁ * u₁ = h₂ * u₂) : h₁ = h₂ ∧ u₁ = u₂ :=
  (triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.1 h₁ (Subgroup.mem_inf.1 hh₁).1 h₂
    (Subgroup.mem_inf.1 hh₂).1 u₁ (Subgroup.mem_inf.1 hu₁).1 u₂ (Subgroup.mem_inf.1 hu₂).1 h

theorem graphFixed_mul_unique'
    {h₁ h₂ u₁ u₂ : ModGL t.tag K} (hh₁ : h₁ ∈ graphFixedTorus t K σ)
    (hh₂ : h₂ ∈ graphFixedTorus t K σ) (hu₁ : u₁ ∈ graphFixedPosUnipotent t K σ)
    (hu₂ : u₂ ∈ graphFixedPosUnipotent t K σ) (h : u₁ * h₁ = u₂ * h₂) : u₁ = u₂ ∧ h₁ = h₂ :=
  (triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.2.1 h₁ (Subgroup.mem_inf.1 hh₁).1 h₂
    (Subgroup.mem_inf.1 hh₂).1 u₁ (Subgroup.mem_inf.1 hu₁).1 u₂ (Subgroup.mem_inf.1 hu₂).1 h

theorem graphFixedPosUnipotent_subgroupOf_normal :
    ((graphFixedPosUnipotent t K σ).subgroupOf (graphFixedBorel t K σ)).Normal := by
  have hN := (triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.2.2.1
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnU, hnΓ⟩ := Subgroup.mem_inf.1 hn
  have hg := Subgroup.mem_inf.1 g.2
  have hn' := Subgroup.mem_inf.1 n.2
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h := hN.conj_mem ⟨n, hn'.1⟩ (Subgroup.mem_subgroupOf.2 hnU) ⟨g, hg.1⟩
    exact Subgroup.mem_subgroupOf.1 h
  · exact mul_mem (mul_mem hg.2 hnΓ) (inv_mem hg.2)

theorem isNilpotent_graphFixedPosUnipotent :
    Group.IsNilpotent (graphFixedPosUnipotent t K σ) := by
  have := (positive_root_height_series t.tag K).2.2.2.2.1
  have := Subgroup.isNilpotent
    ((graphFixedPosUnipotent t K σ).subgroupOf (posUnipotent t.tag K))
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_left)

theorem graphFixedTorus_mul_comm
    {g g' : ModGL t.tag K} (hg : g ∈ graphFixedTorus t K σ)
    (hg' : g' ∈ graphFixedTorus t K σ) : g * g' = g' * g :=
  (triangular_borel_structure.{0, 0} t.tag K).1 g (Subgroup.mem_inf.1 hg).1 g'
    (Subgroup.mem_inf.1 hg').1

theorem graph_field_fixed_Bruhat_decomposition
    (t : TwistTag) (K : Type) [Field K]
    (σ : K ≃+* K) :
    ((graphFixedBorel t K σ.toRingHom : Set (ModGL t.tag K)) =
      (graphFixedTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
        (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K))) ∧
    ((graphFixedBorel t K σ.toRingHom : Set (ModGL t.tag K)) =
      (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) *
        (graphFixedTorus t K σ.toRingHom : Set (ModGL t.tag K))) ∧
    (∀ h₁ ∈ graphFixedTorus t K σ.toRingHom, ∀ h₂ ∈ graphFixedTorus t K σ.toRingHom,
      ∀ u₁ ∈ graphFixedPosUnipotent t K σ.toRingHom,
      ∀ u₂ ∈ graphFixedPosUnipotent t K σ.toRingHom,
        h₁ * u₁ = h₂ * u₂ → h₁ = h₂ ∧ u₁ = u₂) ∧
    (∀ h₁ ∈ graphFixedTorus t K σ.toRingHom, ∀ h₂ ∈ graphFixedTorus t K σ.toRingHom,
      ∀ u₁ ∈ graphFixedPosUnipotent t K σ.toRingHom,
      ∀ u₂ ∈ graphFixedPosUnipotent t K σ.toRingHom,
        u₁ * h₁ = u₂ * h₂ → u₁ = u₂ ∧ h₁ = h₂) ∧
    ((graphFixedPosUnipotent t K σ.toRingHom).subgroupOf
      (graphFixedBorel t K σ.toRingHom)).Normal ∧
    Group.IsNilpotent (graphFixedPosUnipotent t K σ.toRingHom) ∧
    (∀ g ∈ graphFixedTorus t K σ.toRingHom, ∀ g' ∈ graphFixedTorus t K σ.toRingHom,
      g * g' = g' * g) ∧
    (twistedFixedGroup t K σ.toRingHom : Set (ModGL t.tag K)) =
      ⋃ w : relWeylTwist t, graphFixedBruhatCell t K σ.toRingHom w ∧
    (∀ w w' : WeylGroup t.tag, w ≠ w' →
      Disjoint (graphFixedBruhatCell t K σ.toRingHom w)
        (graphFixedBruhatCell t K σ.toRingHom w')) ∧
    (∀ w ∈ relWeylTwist t,
      Set.BijOn (fun p : ModGL t.tag K × ModGL t.tag K =>
          p.1 * canonicalRep (coxeterSystem t.tag) K w * p.2)
        ((graphFixedBorel t K σ.toRingHom : Set (ModGL t.tag K)) ×ˢ
          (graphFixedInversionUnipotent t K σ.toRingHom w : Set (ModGL t.tag K)))
        (graphFixedBruhatCell t K σ.toRingHom w) ∧
      graphFixedBruhatCell t K σ.toRingHom w =
        (twistedFixedGroup t K σ.toRingHom : Set (ModGL t.tag K)) ∩ bruhatCell t.tag K w) ∧
    twistedFixedGroup t K σ.toRingHom =
      graphFixedBorel t K σ.toRingHom ⊔ graphFixedMonomial t K σ.toRingHom ∧
    twistedFixedGroup t K σ.toRingHom = graphFixedBorel t K σ.toRingHom ⊔ Subgroup.closure
      (Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) ∧
    ∀ [Finite K], Nat.card (twistedFixedGroup t K σ.toRingHom) =
      Nat.card (graphFixedBorel t K σ.toRingHom) *
        ∑ᶠ w : relWeylTwist t, Nat.card (graphFixedInversionUnipotent t K σ.toRingHom w) :=
  ⟨graphFixedBorel_eq_mul σ.surjective, graphFixedBorel_eq_mul' σ.surjective,
    fun _ hh₁ _ hh₂ _ hu₁ _ hu₂ h => graphFixed_mul_unique hh₁ hh₂ hu₁ hu₂ h,
    fun _ hh₁ _ hh₂ _ hu₁ _ hu₂ h => graphFixed_mul_unique' hh₁ hh₂ hu₁ hu₂ h,
    graphFixedPosUnipotent_subgroupOf_normal, isNilpotent_graphFixedPosUnipotent,
    fun _ hg _ hg' => graphFixedTorus_mul_comm hg hg',
    twistedFixedGroup_eq_iUnion_graphFixedBruhatCell σ.surjective,
    fun _ _ h => disjoint_graphFixedBruhatCell h,
    fun _ hw => ⟨bijOn_graphFixedBruhatCell σ.surjective hw,
      graphFixedBruhatCell_eq_inter σ.surjective hw⟩,
    twistedFixedGroup_eq_sup_graphFixedMonomial σ.surjective,
    twistedFixedGroup_eq_sup_closure σ.surjective,
    card_twistedFixedGroup σ.surjective⟩

end CFSG.LieType.Chevalley
