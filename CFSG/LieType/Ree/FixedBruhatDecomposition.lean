module

public import CFSG.LieType.Ree.FixedMonomialQuotient
public import CFSG.LieType.Chevalley.HeightSeries

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

namespace ReeTag

variable (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

@[expose] def reeFixedBruhatCell
    (w : WeylGroup t.tag) : Set (ModGL t.tag K) :=
  (t.reeFixedBorel K a : Set (ModGL t.tag K)) * {canonicalRep (coxeterSystem t.tag) K w} *
    (t.reeFixedBorel K a : Set (ModGL t.tag K))

variable {t K a}

theorem mem_reeFixedBruhatCell
    {w : WeylGroup t.tag} {x : ModGL t.tag K} :
    x ∈ t.reeFixedBruhatCell K a w ↔ ∃ b ∈ t.reeFixedBorel K a,
      ∃ b' ∈ t.reeFixedBorel K a, b * canonicalRep (coxeterSystem t.tag) K w * b' = x := by
  simp only [reeFixedBruhatCell, Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩
    exact ⟨b, hb, b', hb', rfl⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩

theorem finiteReeAut_mem_of_map_le
    {S : Subgroup (ModGL t.tag K)}
    (hS : (S.subgroupOf (adjointGroup t.tag K)).map (t.finiteReeAut K a).toMonoidHom ≤
      S.subgroupOf (adjointGroup t.tag K))
    {g : ModGL t.tag K} (hg : g ∈ S) (hga : g ∈ adjointGroup t.tag K) :
    ((t.finiteReeAut K a ⟨g, hga⟩ : adjointGroup t.tag K) : ModGL t.tag K) ∈ S :=
  Subgroup.mem_subgroupOf.1 (hS ⟨⟨g, hga⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩)

theorem finiteReeAut_mem_borelGroup
    {g : ModGL t.tag K} (hg : g ∈ borelGroup t.tag K)
    (hga : g ∈ adjointGroup t.tag K) :
    ((t.finiteReeAut K a ⟨g, hga⟩ : adjointGroup t.tag K) : ModGL t.tag K) ∈
      borelGroup t.tag K :=
  finiteReeAut_mem_of_map_le (ree_root_Bruhat_equivariance t a K).2.2.2.2.2.1.le hg hga

theorem finiteReeAut_mem_posUnipotent
    {g : ModGL t.tag K} (hg : g ∈ posUnipotent t.tag K)
    (hga : g ∈ adjointGroup t.tag K) :
    ((t.finiteReeAut K a ⟨g, hga⟩ : adjointGroup t.tag K) : ModGL t.tag K) ∈
      posUnipotent t.tag K :=
  finiteReeAut_mem_of_map_le (ree_root_Bruhat_equivariance t a K).2.2.2.1.le hg hga

theorem dualRoot_mem_inversionSet
    {w : WeylGroup t.tag} (hw : t.weylPerm w = w)
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ inversionSet w) : t.dualRoot α ∈ inversionSet w := by
  obtain ⟨hr, hpos, hwr, hneg⟩ := hα
  have h := dualRoot_smul w hr
  rw [hw] at h
  refine ⟨isRoot_dualRoot hr, (height_dualRoot_pos_iff hr).2 hpos,
    IsRoot.smul (isRoot_dualRoot hr) w, ?_⟩
  rw [← h]
  exact (height_dualRoot_neg_iff hwr).2 hneg

theorem finiteReeAut_mem_rootSpan_inversionSet
    {w : WeylGroup t.tag} (hw : t.weylPerm w = w)
    {g : ModGL t.tag K} (hg : g ∈ rootSpan t.tag K (inversionSet w))
    (hga : g ∈ adjointGroup t.tag K) :
    ((t.finiteReeAut K a ⟨g, hga⟩ : adjointGroup t.tag K) : ModGL t.tag K) ∈
      rootSpan t.tag K (inversionSet w) :=
  finiteReeAut_mem_of_map_le
    (map_finiteReeAut_rootSpan_le fun _ hα => ⟨hα.1, dualRoot_mem_inversionSet hw hα⟩) hg hga

omit [Finite K] [CharP K t.prime] in
theorem canonicalRep_mem_adjointGroup'
    (w : WeylGroup t.tag) :
    canonicalRep (coxeterSystem t.tag) K w ∈ adjointGroup t.tag K :=
  canonicalRep_mem_adjointGroup _ K w

theorem finiteReeAut_canonicalRep
    (w : WeylGroup t.tag) :
    ((t.finiteReeAut K a ⟨canonicalRep (coxeterSystem t.tag) K w,
        canonicalRep_mem_adjointGroup' w⟩ : adjointGroup t.tag K) : ModGL t.tag K) =
      canonicalRep (coxeterSystem t.tag) K (t.weylPerm w) := by
  have h := (ree_root_Bruhat_equivariance t a K).2.2.2.2.2.2.1 w
  exact congrArg (fun x : adjointGroup t.tag K => (x : ModGL t.tag K)) h

theorem finiteReeAut_mul_canonicalRep_mul
    {b b' : ModGL t.tag K}
    (hb : b ∈ adjointGroup t.tag K) (hb' : b' ∈ adjointGroup t.tag K) (w : WeylGroup t.tag)
    (h : b * canonicalRep (coxeterSystem t.tag) K w * b' ∈ adjointGroup t.tag K) :
    ((t.finiteReeAut K a ⟨_, h⟩ : adjointGroup t.tag K) : ModGL t.tag K) =
      ((t.finiteReeAut K a ⟨b, hb⟩ : adjointGroup t.tag K) : ModGL t.tag K) *
        canonicalRep (coxeterSystem t.tag) K (t.weylPerm w) *
        ((t.finiteReeAut K a ⟨b', hb'⟩ : adjointGroup t.tag K) : ModGL t.tag K) := by
  have e : (⟨_, h⟩ : adjointGroup t.tag K) =
      ⟨b, hb⟩ * ⟨_, canonicalRep_mem_adjointGroup' w⟩ * ⟨b', hb'⟩ := rfl
  rw [e, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, finiteReeAut_canonicalRep]

omit [Finite K] [CharP K t.prime] in
theorem borelGroup_le_adjointGroup'
    : borelGroup t.tag K ≤ adjointGroup t.tag K :=
  ((triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.2.2.2.2.2 K).1

theorem mem_reeGamma_of_fixed
    {g : ModGL t.tag K} (hga : g ∈ adjointGroup t.tag K)
    (hF : ((t.finiteReeAut K a ⟨g, hga⟩ : adjointGroup t.tag K) : ModGL t.tag K) = g) :
    g ∈ t.reeGamma K a :=
  mem_reeGamma.2 ⟨hga, Subtype.ext hF⟩

theorem finiteReeAut_eq_of_mem_reeGamma
    {g : ModGL t.tag K} (hg : g ∈ t.reeGamma K a)
    (hga : g ∈ adjointGroup t.tag K) :
    ((t.finiteReeAut K a ⟨g, hga⟩ : adjointGroup t.tag K) : ModGL t.tag K) = g := by
  obtain ⟨hga', h⟩ := mem_reeGamma.1 hg
  exact congrArg Subtype.val h

theorem reeFixedTorus_le_reeFixedBorel
    : t.reeFixedTorus K a ≤ t.reeFixedBorel K a :=
  inf_le_inf_right _ torusGroup_le_borelGroup

theorem reeFixedPosUnipotent_le_reeFixedBorel :
    t.reeFixedPosUnipotent K a ≤ t.reeFixedBorel K a :=
  inf_le_inf_right _ le_sup_right

theorem reeFixedCellUnipotent_le_reeFixedPosUnipotent
    (w : WeylGroup t.tag) :
    t.reeFixedCellUnipotent K a w ≤ t.reeFixedPosUnipotent K a :=
  inf_le_inf_right _ (rootSpan_le_posUnipotent fun _ h => inversionSet_pos (w := w) h)

theorem reeFixedBorel_le_reeGamma :
    t.reeFixedBorel K a ≤ t.reeGamma K a :=
  inf_le_right

theorem reeFixedBorel_eq_mul :
    (t.reeFixedBorel K a : Set (ModGL t.tag K)) =
      (t.reeFixedTorus K a : Set (ModGL t.tag K)) *
        (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K)) := by
  obtain ⟨-, -, -, -, hHU, -, huniq, -⟩ := triangular_borel_structure.{0, 0} t.tag K
  refine Set.Subset.antisymm (fun b hb => ?_) ?_
  · obtain ⟨hbB, hbΓ⟩ := Subgroup.mem_inf.1 hb
    have hb' : b ∈ (torusGroup t.tag K : Set (ModGL t.tag K)) *
        (posUnipotent t.tag K : Set (ModGL t.tag K)) := by
      rw [← hHU]
      exact hbB
    obtain ⟨h, hh, u, hu, rfl⟩ := hb'
    have hha : h ∈ adjointGroup t.tag K := borelGroup_le_adjointGroup' (torusGroup_le_borelGroup hh)
    have hua : u ∈ adjointGroup t.tag K :=
      borelGroup_le_adjointGroup' (Subgroup.mem_sup_right hu)
    have hF := finiteReeAut_eq_of_mem_reeGamma hbΓ (mul_mem hha hua)
    have e : (⟨h * u, mul_mem hha hua⟩ : adjointGroup t.tag K) = ⟨h, hha⟩ * ⟨u, hua⟩ := rfl
    rw [e, map_mul, Subgroup.coe_mul] at hF
    obtain ⟨h1, h2⟩ := huniq _ (finiteReeAut_mem_torusGroup hh hha) _ hh _
      (finiteReeAut_mem_posUnipotent hu hua) _ hu hF
    exact ⟨h, Subgroup.mem_inf.2 ⟨hh, mem_reeGamma_of_fixed hha h1⟩, u,
      Subgroup.mem_inf.2 ⟨hu, mem_reeGamma_of_fixed hua h2⟩, rfl⟩
  · rintro _ ⟨h, hh, u, hu, rfl⟩
    exact mul_mem (reeFixedTorus_le_reeFixedBorel hh) (reeFixedPosUnipotent_le_reeFixedBorel hu)

theorem reeFixedBorel_eq_mul' :
    (t.reeFixedBorel K a : Set (ModGL t.tag K)) =
      (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K)) *
        (t.reeFixedTorus K a : Set (ModGL t.tag K)) := by
  refine Set.Subset.antisymm (fun b hb => ?_) ?_
  · have hb' : b⁻¹ ∈ (t.reeFixedBorel K a : Set (ModGL t.tag K)) := inv_mem hb
    rw [reeFixedBorel_eq_mul] at hb'
    obtain ⟨h, hh, u, hu, hhu⟩ := hb'
    refine ⟨u⁻¹, inv_mem hu, h⁻¹, inv_mem hh, ?_⟩
    simp only at hhu ⊢
    rw [← mul_inv_rev, hhu, inv_inv]
  · rintro _ ⟨u, hu, h, hh, rfl⟩
    exact mul_mem (reeFixedPosUnipotent_le_reeFixedBorel hu) (reeFixedTorus_le_reeFixedBorel hh)

theorem exists_reeFixed_bruhat_factor
    {w : WeylGroup t.tag} {g : ModGL t.tag K}
    (hg : g ∈ t.reeGamma K a) (hgw : g ∈ bruhatCell t.tag K w) :
    t.weylPerm w = w ∧ ∃ b ∈ t.reeFixedBorel K a, ∃ u ∈ t.reeFixedCellUnipotent K a w,
      b * canonicalRep (coxeterSystem t.tag) K w * u = g := by
  have hIB : rootSpan t.tag K (inversionSet w) ≤ borelGroup t.tag K :=
    (rootSpan_le_posUnipotent fun _ h => inversionSet_pos (w := w) h).trans le_sup_right
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, rfl⟩ := (bijOn_bruhatCell (K := K) w).2.2 hgw
  simp only at hb hu hg ⊢
  have hba := borelGroup_le_adjointGroup' hb
  have hua := borelGroup_le_adjointGroup' (hIB hu)
  have hga : b * canonicalRep (coxeterSystem t.tag) K w * u ∈ adjointGroup t.tag K :=
    mul_mem (mul_mem hba (canonicalRep_mem_adjointGroup' w)) hua
  have hF := finiteReeAut_eq_of_mem_reeGamma hg hga
  rw [finiteReeAut_mul_canonicalRep_mul hba hua w hga] at hF
  have hδ : t.weylPerm w = w := by
    have hmem : b * canonicalRep (coxeterSystem t.tag) K w * u ∈
        bruhatCell t.tag K (t.weylPerm w) := by
      rw [← hF]
      exact mem_bruhatCell.2 ⟨_, finiteReeAut_mem_borelGroup hb hba, _,
        finiteReeAut_mem_borelGroup (hIB hu) hua, rfl⟩
    exact bruhatCell_injective (bruhatCell_eq_of_mem hmem
      (mem_bruhatCell.2 ⟨b, hb, u, hIB hu, rfl⟩))
  refine ⟨hδ, ?_⟩
  rw [hδ] at hF
  have h := (bijOn_bruhatCell (K := K) w).2.1
    (Set.mk_mem_prod (finiteReeAut_mem_borelGroup hb hba)
      (finiteReeAut_mem_rootSpan_inversionSet hδ hu hua)) (Set.mk_mem_prod hb hu) hF
  simp only [Prod.mk.injEq] at h
  exact ⟨b, Subgroup.mem_inf.2 ⟨hb, mem_reeGamma_of_fixed hba h.1⟩, u,
    Subgroup.mem_inf.2 ⟨hu, mem_reeGamma_of_fixed hua h.2⟩, rfl⟩

theorem reeFixedBruhatCell_subset
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) :
    t.reeFixedBruhatCell K a w ⊆ (t.reeGamma K a : Set (ModGL t.tag K)) := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hx
  exact mul_mem (mul_mem (reeFixedBorel_le_reeGamma hb)
    (canonicalRep_mem_reeFixedMonomial t K a hw).2) (reeFixedBorel_le_reeGamma hb')

theorem reeFixedBruhatCell_subset_bruhatCell
    (w : WeylGroup t.tag) :
    t.reeFixedBruhatCell K a w ⊆ bruhatCell t.tag K w := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hx
  exact mem_bruhatCell.2 ⟨b, (Subgroup.mem_inf.1 hb).1, b', (Subgroup.mem_inf.1 hb').1, rfl⟩

theorem reeFixedBruhatCell_eq_inter
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) :
    t.reeFixedBruhatCell K a w =
      (t.reeGamma K a : Set (ModGL t.tag K)) ∩ bruhatCell t.tag K w := by
  refine Set.Subset.antisymm (fun x hx => ⟨reeFixedBruhatCell_subset hw hx,
    reeFixedBruhatCell_subset_bruhatCell w hx⟩) fun x ⟨hxΓ, hxw⟩ => ?_
  obtain ⟨-, b, hb, u, hu, rfl⟩ := exists_reeFixed_bruhat_factor hxΓ hxw
  exact mem_reeFixedBruhatCell.2 ⟨b, hb, u, reeFixedPosUnipotent_le_reeFixedBorel
    (reeFixedCellUnipotent_le_reeFixedPosUnipotent w hu), rfl⟩

theorem bijOn_reeFixedBruhatCell
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) :
    Set.BijOn (fun p : ModGL t.tag K × ModGL t.tag K =>
        p.1 * canonicalRep (coxeterSystem t.tag) K w * p.2)
      ((t.reeFixedBorel K a : Set (ModGL t.tag K)) ×ˢ
        (t.reeFixedCellUnipotent K a w : Set (ModGL t.tag K)))
      (t.reeFixedBruhatCell K a w) := by
  refine ⟨fun p hp => mem_reeFixedBruhatCell.2 ⟨p.1, hp.1, p.2,
      reeFixedPosUnipotent_le_reeFixedBorel
        (reeFixedCellUnipotent_le_reeFixedPosUnipotent w hp.2), rfl⟩,
    fun p hp q hq h => (bijOn_bruhatCell (K := K) w).2.1
      (Set.mem_prod.2 ⟨(Subgroup.mem_inf.1 hp.1).1, (Subgroup.mem_inf.1 hp.2).1⟩)
      (Set.mem_prod.2 ⟨(Subgroup.mem_inf.1 hq.1).1, (Subgroup.mem_inf.1 hq.2).1⟩) h,
    fun x hx => ?_⟩
  rw [reeFixedBruhatCell_eq_inter hw] at hx
  obtain ⟨-, b, hb, u, hu, rfl⟩ := exists_reeFixed_bruhat_factor hx.1 hx.2
  exact ⟨(b, u), ⟨hb, hu⟩, rfl⟩

theorem reeGamma_eq_iUnion_reeFixedBruhatCell :
    (t.reeGamma K a : Set (ModGL t.tag K)) = ⋃ w : t.relWeylRee, t.reeFixedBruhatCell K a w := by
  refine Set.Subset.antisymm (fun g hg => ?_)
    (Set.iUnion_subset fun w => reeFixedBruhatCell_subset w.2)
  have hgC : g ∈ (adjointGroup t.tag K : Set (ModGL t.tag K)) := (mem_reeGamma.1 hg).1
  rw [adjointGroup_eq_iUnion_bruhatCell] at hgC
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hgC
  obtain ⟨hδ, b, hb, u, hu, rfl⟩ := exists_reeFixed_bruhat_factor hg hw
  exact Set.mem_iUnion.2 ⟨⟨w, hδ⟩, mem_reeFixedBruhatCell.2 ⟨b, hb, u,
    reeFixedPosUnipotent_le_reeFixedBorel
      (reeFixedCellUnipotent_le_reeFixedPosUnipotent w hu), rfl⟩⟩

theorem disjoint_reeFixedBruhatCell
    {w w' : WeylGroup t.tag} (h : w ≠ w') :
    Disjoint (t.reeFixedBruhatCell K a w) (t.reeFixedBruhatCell K a w') :=
  (disjoint_bruhatCell h).mono (reeFixedBruhatCell_subset_bruhatCell w)
    (reeFixedBruhatCell_subset_bruhatCell w')

theorem reeGamma_eq_sup_reeFixedMonomial :
    t.reeGamma K a = t.reeFixedBorel K a ⊔ t.reeFixedMonomial K a := by
  refine le_antisymm (fun g hg => ?_) (sup_le reeFixedBorel_le_reeGamma inf_le_right)
  have hg' : g ∈ (t.reeGamma K a : Set (ModGL t.tag K)) := hg
  rw [reeGamma_eq_iUnion_reeFixedBruhatCell] at hg'
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hw
  exact mul_mem (mul_mem (Subgroup.mem_sup_left hb)
    (Subgroup.mem_sup_right (canonicalRep_mem_reeFixedMonomial t K a w.2)))
    (Subgroup.mem_sup_left hb')

theorem reeGamma_eq_sup_closure :
    t.reeGamma K a = t.reeFixedBorel K a ⊔ Subgroup.closure
      (Set.range fun j => canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j)) := by
  rw [reeGamma_eq_sup_reeFixedMonomial, reeFixedMonomial_eq_sup, ← sup_assoc,
    sup_eq_left.2 reeFixedTorus_le_reeFixedBorel]

theorem reeFixed_mul_unique
    {h₁ h₂ u₁ u₂ : ModGL t.tag K} (hh₁ : h₁ ∈ t.reeFixedTorus K a)
    (hh₂ : h₂ ∈ t.reeFixedTorus K a) (hu₁ : u₁ ∈ t.reeFixedPosUnipotent K a)
    (hu₂ : u₂ ∈ t.reeFixedPosUnipotent K a) (h : h₁ * u₁ = h₂ * u₂) : h₁ = h₂ ∧ u₁ = u₂ :=
  (triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.1 h₁ (Subgroup.mem_inf.1 hh₁).1 h₂
    (Subgroup.mem_inf.1 hh₂).1 u₁ (Subgroup.mem_inf.1 hu₁).1 u₂ (Subgroup.mem_inf.1 hu₂).1 h

theorem reeFixed_mul_unique'
    {h₁ h₂ u₁ u₂ : ModGL t.tag K} (hh₁ : h₁ ∈ t.reeFixedTorus K a)
    (hh₂ : h₂ ∈ t.reeFixedTorus K a) (hu₁ : u₁ ∈ t.reeFixedPosUnipotent K a)
    (hu₂ : u₂ ∈ t.reeFixedPosUnipotent K a) (h : u₁ * h₁ = u₂ * h₂) : u₁ = u₂ ∧ h₁ = h₂ :=
  (triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.2.1 h₁ (Subgroup.mem_inf.1 hh₁).1 h₂
    (Subgroup.mem_inf.1 hh₂).1 u₁ (Subgroup.mem_inf.1 hu₁).1 u₂ (Subgroup.mem_inf.1 hu₂).1 h

theorem reeFixedPosUnipotent_subgroupOf_normal :
    ((t.reeFixedPosUnipotent K a).subgroupOf (t.reeFixedBorel K a)).Normal := by
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

theorem isNilpotent_reeFixedPosUnipotent
    : Group.IsNilpotent (t.reeFixedPosUnipotent K a) := by
  have := (positive_root_height_series t.tag K).2.2.2.2.1
  have := Subgroup.isNilpotent
    ((t.reeFixedPosUnipotent K a).subgroupOf (posUnipotent t.tag K))
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_left)

theorem reeFixedTorus_mul_comm
    {g g' : ModGL t.tag K} (hg : g ∈ t.reeFixedTorus K a)
    (hg' : g' ∈ t.reeFixedTorus K a) : g * g' = g' * g :=
  (triangular_borel_structure.{0, 0} t.tag K).1 g (Subgroup.mem_inf.1 hg).1 g'
    (Subgroup.mem_inf.1 hg').1

theorem isSolvable_reeFixedBorel
    : Group.IsSolvable (t.reeFixedBorel K a) := by
  set U : Subgroup (t.reeFixedBorel K a) :=
    (t.reeFixedPosUnipotent K a).subgroupOf (t.reeFixedBorel K a) with hUdef
  have : U.Normal := reeFixedPosUnipotent_subgroupOf_normal
  have := isNilpotent_reeFixedPosUnipotent (t := t) (K := K) (a := a)
  have : Group.IsSolvable U := Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe reeFixedPosUnipotent_le_reeFixedBorel).toMonoidHom)
    (MulEquiv.injective _)
  have key : ∀ x : t.reeFixedBorel K a, ∃ h ∈ t.reeFixedTorus K a,
      ∃ hB : h ∈ t.reeFixedBorel K a,
        (QuotientGroup.mk x : t.reeFixedBorel K a ⧸ U) = QuotientGroup.mk ⟨h, hB⟩ := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ (t.reeFixedBorel K a : Set (ModGL t.tag K)) := hx
    rw [reeFixedBorel_eq_mul] at hx'
    obtain ⟨h, hh, u, hu, rfl⟩ := hx'
    refine ⟨h, hh, reeFixedTorus_le_reeFixedBorel hh, ?_⟩
    rw [QuotientGroup.eq, hUdef, Subgroup.mem_subgroupOf]
    change (h * u)⁻¹ * h ∈ t.reeFixedPosUnipotent K a
    rw [show (h * u)⁻¹ * h = u⁻¹ by group]
    exact inv_mem hu
  have : Group.IsSolvable (t.reeFixedBorel K a ⧸ U) := Group.isSolvable_of_comm fun x y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨h, hh, hB, hxh⟩ := key x
    obtain ⟨h', hh', hB', hyh⟩ := key y
    rw [hxh, hyh, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext (reeFixedTorus_mul_comm hh hh'))
  exact Group.isSolvable_of_subgroup_quotient U

theorem ree_fixed_Bruhat_decomposition
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] :
    ((t.reeFixedBorel K a : Set (ModGL t.tag K)) =
      (t.reeFixedTorus K a : Set (ModGL t.tag K)) *
        (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K))) ∧
    ((t.reeFixedBorel K a : Set (ModGL t.tag K)) =
      (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K)) *
        (t.reeFixedTorus K a : Set (ModGL t.tag K))) ∧
    (∀ h₁ ∈ t.reeFixedTorus K a, ∀ h₂ ∈ t.reeFixedTorus K a,
      ∀ u₁ ∈ t.reeFixedPosUnipotent K a, ∀ u₂ ∈ t.reeFixedPosUnipotent K a,
        h₁ * u₁ = h₂ * u₂ → h₁ = h₂ ∧ u₁ = u₂) ∧
    (∀ h₁ ∈ t.reeFixedTorus K a, ∀ h₂ ∈ t.reeFixedTorus K a,
      ∀ u₁ ∈ t.reeFixedPosUnipotent K a, ∀ u₂ ∈ t.reeFixedPosUnipotent K a,
        u₁ * h₁ = u₂ * h₂ → u₁ = u₂ ∧ h₁ = h₂) ∧
    ((t.reeFixedPosUnipotent K a).subgroupOf (t.reeFixedBorel K a)).Normal ∧
    Group.IsNilpotent (t.reeFixedPosUnipotent K a) ∧
    (∀ g ∈ t.reeFixedTorus K a, ∀ g' ∈ t.reeFixedTorus K a, g * g' = g' * g) ∧
    Group.IsSolvable (t.reeFixedBorel K a) ∧
    (t.reeGamma K a : Set (ModGL t.tag K)) = ⋃ w : t.relWeylRee, t.reeFixedBruhatCell K a w ∧
    (∀ w w' : WeylGroup t.tag, w ≠ w' →
      Disjoint (t.reeFixedBruhatCell K a w) (t.reeFixedBruhatCell K a w')) ∧
    (∀ w ∈ t.relWeylRee,
      Set.BijOn (fun p : ModGL t.tag K × ModGL t.tag K =>
          p.1 * canonicalRep (coxeterSystem t.tag) K w * p.2)
        ((t.reeFixedBorel K a : Set (ModGL t.tag K)) ×ˢ
          (t.reeFixedCellUnipotent K a w : Set (ModGL t.tag K)))
        (t.reeFixedBruhatCell K a w) ∧
      t.reeFixedBruhatCell K a w =
        (t.reeGamma K a : Set (ModGL t.tag K)) ∩ bruhatCell t.tag K w) ∧
    t.reeGamma K a = t.reeFixedBorel K a ⊔ t.reeFixedMonomial K a ∧
    t.reeGamma K a = t.reeFixedBorel K a ⊔ Subgroup.closure
      (Set.range fun j => canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j)) :=
  ⟨reeFixedBorel_eq_mul, reeFixedBorel_eq_mul',
    fun _ hh₁ _ hh₂ _ hu₁ _ hu₂ h => reeFixed_mul_unique hh₁ hh₂ hu₁ hu₂ h,
    fun _ hh₁ _ hh₂ _ hu₁ _ hu₂ h => reeFixed_mul_unique' hh₁ hh₂ hu₁ hu₂ h,
    reeFixedPosUnipotent_subgroupOf_normal, isNilpotent_reeFixedPosUnipotent,
    fun _ hg _ hg' => reeFixedTorus_mul_comm hg hg', isSolvable_reeFixedBorel,
    reeGamma_eq_iUnion_reeFixedBruhatCell, fun _ _ h => disjoint_reeFixedBruhatCell h,
    fun _ hw => ⟨bijOn_reeFixedBruhatCell hw, reeFixedBruhatCell_eq_inter hw⟩,
    reeGamma_eq_sup_reeFixedMonomial, reeGamma_eq_sup_closure⟩

end ReeTag

end CFSG.LieType.Ree
