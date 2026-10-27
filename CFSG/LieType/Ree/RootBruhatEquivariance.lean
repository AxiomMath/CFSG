module

public import CFSG.LieType.Ree.FixedSubgroupData
public import CFSG.LieType.Chevalley.ChevalleySplitBN

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Generic

variable {G : Type*} [Group G] {C : Subgroup G}

theorem subgroupOf_closure_image (S : Set C) :
    (Subgroup.closure (C.subtype '' S)).subgroupOf C = Subgroup.closure S := by
  rw [← MonoidHom.map_closure]
  exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _

theorem subgroupOf_sup_of_le {A B : Subgroup G} (hA : A ≤ C) (hB : B ≤ C) :
    (A ⊔ B).subgroupOf C = A.subgroupOf C ⊔ B.subgroupOf C := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (sup_le hA hB), inf_eq_left.2 hA,
    inf_eq_left.2 hB]

theorem subgroupOf_biSup_of_le {ι : Type*} {s : Set ι} {X : ι → Subgroup G}
    (h : ∀ i ∈ s, X i ≤ C) : (⨆ i ∈ s, X i).subgroupOf C = ⨆ i ∈ s, (X i).subgroupOf C := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (iSup₂_le h)]
  simp only [Subgroup.map_iSup, Subgroup.subgroupOf_map_subtype]
  exact iSup_congr fun i => iSup_congr fun hi => (inf_eq_left.2 (h i hi)).symm

theorem map_eq_of_map_le [Finite G] (F : MulAut G) {X : Subgroup G}
    (h : X.map F.toMonoidHom ≤ X) : X.map F.toMonoidHom = X :=
  Subgroup.eq_of_le_of_card_ge h (by rw [Subgroup.card_map_of_injective F.injective])

end Generic

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K]

theorem torusSub_eq_closure :
    (torusGroup t.tag K).subgroupOf (adjointGroup t.tag K) =
      Subgroup.closure (Set.range fun x : Fin t.tag.rank × Kˣ =>
        torusElement t.tag K x.1 x.2) := by
  rw [← subgroupOf_closure_image, ← Set.range_comp]
  rfl

theorem monomialSub_eq_monomialGroup :
    (monomialSubgroup t.tag K).subgroupOf (adjointGroup t.tag K) = monomialGroup t.tag K := by
  rw [monomialGroup, ← subgroupOf_closure_image, Set.image_union, ← Set.range_comp,
    ← Set.range_comp, Subgroup.closure_union, sup_comm, monomialSubgroup]
  rfl

theorem rootSpan_le_adjointGroup
    (S : Set (Fin t.tag.rank → ℤ)) :
    rootSpan t.tag K S ≤ adjointGroup t.tag K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem subgroupOf_rootSpan
    (S : Set (Fin t.tag.rank → ℤ)) :
    (rootSpan t.tag K S).subgroupOf (adjointGroup t.tag K) =
      ⨆ α ∈ S, (rootSubgroup t.tag K α).subgroupOf (adjointGroup t.tag K) :=
  subgroupOf_biSup_of_le fun α _ => rootSubgroup_le_adjointGroup α

variable [Finite K] [CharP K t.prime] {a : ℕ}

theorem finiteReeAut_eq_reeAut :
    t.finiteReeAut K a = t.reeAut K a :=
  MulEquiv.ext fun g => DFunLike.congr_fun (finiteReeAut_toMonoidHom a) g

theorem map_finiteReeAut_rootSubgroup
    {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) :
    ((rootSubgroup t.tag K α).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom =
      (rootSubgroup t.tag K (t.dualRoot α)).subgroupOf (adjointGroup t.tag K) := by
  have h := map_reeAut_X (K := K) a ⟨α, hα⟩
  rw [nativeRootSubgroups_X, ← (rootOperatorFamily t.tag).subgroupOf_rootSubgroup_eq K,
    ← (rootOperatorFamily t.tag).subgroupOf_rootSubgroup_eq K] at h
  rw [finiteReeAut_eq_reeAut]
  exact h

theorem map_finiteReeAut_rootSpan_le
    {S : Set (Fin t.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot t.tag α ∧ t.dualRoot α ∈ S) :
    ((rootSpan t.tag K S).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom ≤
      (rootSpan t.tag K S).subgroupOf (adjointGroup t.tag K) := by
  rw [subgroupOf_rootSpan, Subgroup.map_iSup]
  refine iSup_le fun α => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hα => ?_
  rw [map_finiteReeAut_rootSubgroup (hS α hα).1]
  exact le_iSup₂_of_le (f := fun β (_ : β ∈ S) =>
    (rootSubgroup t.tag K β).subgroupOf (adjointGroup t.tag K)) _ (hS α hα).2 le_rfl

theorem dualRoot_mem_posRoots
    {α : Fin t.tag.rank → ℤ}
    (hα : α ∈ {β : Fin t.tag.rank → ℤ | IsRoot t.tag β ∧ 0 < height β}) :
    IsRoot t.tag α ∧ t.dualRoot α ∈ {β : Fin t.tag.rank → ℤ | IsRoot t.tag β ∧ 0 < height β} :=
  ⟨hα.1, isRoot_dualRoot hα.1, (height_dualRoot_pos_iff hα.1).2 hα.2⟩

theorem dualRoot_mem_negRoots
    {α : Fin t.tag.rank → ℤ}
    (hα : α ∈ {β : Fin t.tag.rank → ℤ | IsRoot t.tag β ∧ height β < 0}) :
    IsRoot t.tag α ∧ t.dualRoot α ∈ {β : Fin t.tag.rank → ℤ | IsRoot t.tag β ∧ height β < 0} :=
  ⟨hα.1, isRoot_dualRoot hα.1, (height_dualRoot_neg_iff hα.1).2 hα.2⟩

theorem map_finiteReeAut_torusSub :
    ((torusGroup t.tag K).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom =
      (torusGroup t.tag K).subgroupOf (adjointGroup t.tag K) := by
  refine map_eq_of_map_le _ ?_
  rw [torusSub_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨⟨i, u⟩, rfl⟩, rfl⟩
  change t.finiteReeAut K a (torusElement t.tag K i u) ∈ _
  rw [finiteReeAut_eq_reeAut, reeAut_torusElement]
  exact Subgroup.subset_closure ⟨(t.perm i, u ^ t.relationExponent a i), rfl⟩

theorem map_finiteReeAut_monomialSub :
    ((monomialSubgroup t.tag K).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom =
      (monomialSubgroup t.tag K).subgroupOf (adjointGroup t.tag K) := by
  refine map_eq_of_map_le _ ?_
  rw [monomialSub_eq_monomialGroup]
  rintro _ ⟨m, hm, rfl⟩
  change t.finiteReeAut K a m ∈ _
  rw [finiteReeAut_eq_reeAut]
  exact reeAut_mem_monomialGroup a hm

theorem map_finiteReeAut_posUnipotentSub :
    ((posUnipotent t.tag K).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom =
      (posUnipotent t.tag K).subgroupOf (adjointGroup t.tag K) :=
  map_eq_of_map_le _ (map_finiteReeAut_rootSpan_le fun _ hα => dualRoot_mem_posRoots hα)

theorem map_finiteReeAut_negUnipotentSub :
    ((negUnipotent t.tag K).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom =
      (negUnipotent t.tag K).subgroupOf (adjointGroup t.tag K) :=
  map_eq_of_map_le _ (map_finiteReeAut_rootSpan_le fun _ hα => dualRoot_mem_negRoots hα)

theorem map_finiteReeAut_borelSub :
    ((borelGroup t.tag K).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom =
      (borelGroup t.tag K).subgroupOf (adjointGroup t.tag K) := by
  have hT : torusGroup t.tag K ≤ adjointGroup t.tag K :=
    le_sup_left.trans borelGroup_le_adjointGroup'
  rw [borelGroup, subgroupOf_sup_of_le hT posUnipotent_le_adjointGroup, Subgroup.map_sup,
    map_finiteReeAut_torusSub, map_finiteReeAut_posUnipotentSub]

end ReeTag

open ReeTag

theorem ree_root_Bruhat_equivariance
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] :
    (∀ α : Fin t.tag.rank → ℤ, IsRoot t.tag α →
      ((rootSubgroup t.tag K α).subgroupOf (adjointGroup t.tag K)).map
          (t.finiteReeAut K a).toMonoidHom =
        (rootSubgroup t.tag K (t.dualRoot α)).subgroupOf (adjointGroup t.tag K)) ∧
    ((torusGroup t.tag K).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom =
      (torusGroup t.tag K).subgroupOf (adjointGroup t.tag K) ∧
    ((monomialSubgroup t.tag K).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom =
      (monomialSubgroup t.tag K).subgroupOf (adjointGroup t.tag K) ∧
    ((posUnipotent t.tag K).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom =
      (posUnipotent t.tag K).subgroupOf (adjointGroup t.tag K) ∧
    ((negUnipotent t.tag K).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom =
      (negUnipotent t.tag K).subgroupOf (adjointGroup t.tag K) ∧
    ((borelGroup t.tag K).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom =
      (borelGroup t.tag K).subgroupOf (adjointGroup t.tag K) ∧
    (∀ w : WeylGroup t.tag, t.finiteReeAut K a (nrep t.tag K w) = nrep t.tag K (t.weylPerm w)) ∧
    ∀ w ∈ t.relWeylRee, canonicalRep (coxeterSystem t.tag) K w ∈ t.reeFixedMonomial K a := by
  have hnrep : ∀ w : WeylGroup t.tag,
      t.finiteReeAut K a (nrep t.tag K w) = nrep t.tag K (t.weylPerm w) := fun w => by
    rw [finiteReeAut_eq_reeAut]
    exact reeAut_nrep a w
  refine ⟨fun α hα => map_finiteReeAut_rootSubgroup hα, map_finiteReeAut_torusSub,
    map_finiteReeAut_monomialSub, map_finiteReeAut_posUnipotentSub,
    map_finiteReeAut_negUnipotentSub, map_finiteReeAut_borelSub, hnrep, fun w hw => ?_⟩
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_right (canonicalRep_mem_closure _ K w), ?_⟩
  refine mem_reeGamma.2 ⟨canonicalRep_mem_adjointGroup _ K w, ?_⟩
  have h := hnrep w
  rw [(mem_relWeylRee t).1 hw] at h
  exact h

end CFSG.LieType.Ree
