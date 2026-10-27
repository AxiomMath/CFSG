module

public import CFSG.LieType.Ree.LargeReeA1Pair
public import CFSG.LieType.Ree.LargeReeTorusRootForms
public import CFSG.LieType.Ree.LocalBlockSylowAction
public import CFSG.LocalAnalysis.SectionRank.LargeRee.Suzuki
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Walter.PSL2Facts.Even

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom pairedTorusHom_apply f4i)

variable (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)

@[expose] def rankOneTorusOne
    : Subgroup (ModGL F4.tag K) :=
  (pairedTorusHom a (f4i 0) (f4i 3)).range

@[expose] def rankOneTorusTwo
    : Subgroup (ModGL F4.tag K) :=
  (pairedTorusHom a (f4i 1) (f4i 2)).range

@[expose] def rankOneGroupOne
    : Subgroup (ModGL F4.tag K) :=
  Subgroup.closure ((F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K)) ∪
    (rankOneTorusOne K a : Set (ModGL F4.tag K)) ∪
      {canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩)})

@[expose] def rankOneGroupTwo
    : Subgroup (ModGL F4.tag K) :=
  Subgroup.closure ((F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K)) ∪
    (rankOneTorusTwo K a : Set (ModGL F4.tag K)) ∪
      {canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩)})

variable {K a}

omit [Finite K] in
theorem pairedTorusHom_eq_largeReeA1Hom
    (u : Kˣ) :
    pairedTorusHom a (f4i 0) (f4i 3) u = largeReeA1Hom K a (HSL u) := by
  rw [pairedTorusHom_apply, largeReeA1Hom_HSL]
  congr 2

theorem rankOneGroupOne_eq_range
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupOne K a = (largeReeA1Hom K a).range := by
  have hrange := largeReeA1Hom_range (K := K) (a := a) hK
  have hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) ∈
      rankOneGroupOne K a := Subgroup.subset_closure (.inr rfl)
  apply le_antisymm
  · rw [rankOneGroupOne, Subgroup.closure_le]
    rintro g ((hg | ⟨u, rfl⟩) | rfl)
    · rw [SetLike.mem_coe, hrange]
      exact Subgroup.mem_sup_left hg
    · exact ⟨HSL u, (pairedTorusHom_eq_largeReeA1Hom u).symm⟩
    · exact ⟨WSL, by rw [largeReeA1Hom_WSL, canonicalRep_F4_fixedOrbitElement_zero]⟩
  · rw [hrange, largeReeA1M]
    refine sup_le (fun g hg => Subgroup.subset_closure (.inl (.inl hg))) ?_
    have hY : largeReeA1Y K a = (F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K
          (F4.fixedOrbitElement ⟨0, by decide⟩))).toMonoidHom :=
      (map_conj_reeFixedOrbitUnipotent _).symm
    rw [hY]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ rankOneGroupOne K a := Subgroup.subset_closure (.inl (.inl hx))
    exact mul_mem (mul_mem hn hx') (inv_mem hn)

omit [Finite K] in
theorem largeReeA1Hom_injective
    : Function.Injective (largeReeA1Hom K a) :=
  (injective_iff_map_eq_one _).2 fun _ hg => eq_one_of_largeReeA1Hom_eq_one a hg

variable (K a) in
@[expose] def rankOneEquivSL
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    SL2 K ≃* rankOneGroupOne K a :=
  (MonoidHom.ofInjective largeReeA1Hom_injective).trans
    (MulEquiv.subgroupCongr (rankOneGroupOne_eq_range hK).symm)

theorem coe_rankOneEquivSL
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : SL2 K) :
    (rankOneEquivSL K a hK g : ModGL F4.tag K) = largeReeA1Hom K a g :=
  rfl

theorem card_rankOneGroupOne
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (rankOneGroupOne K a) = 2 ^ (2 * a + 1) * ((2 ^ (2 * a + 1)) ^ 2 - 1) := by
  rw [← Nat.card_congr (rankOneEquivSL K a hK).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]

omit [Finite K] in
theorem exists_SL2_mul_ne_mul : ∃ x y : SL2 K, x * y ≠ y * x := by
  have : CharP K 2 := ‹CharP K F4.prime›
  refine ⟨uSL 1, vSL 1, fun h => ?_⟩
  have h00 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  change ((uSL 1 : SL2 K) * (vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
    ((vSL 1 : SL2 K) * (uSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 at h00
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem isSimpleGroup_SL2 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSimpleGroup (SL2 K) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have := Fintype.ofFinite K
  have h4 : ∃ s : Finset K, s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl (Or.inr h4)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm.isSimpleGroup

theorem isSimpleGroup_rankOneGroupOne
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSimpleGroup (rankOneGroupOne K a) ∧ ∃ x y : rankOneGroupOne K a, x * y ≠ y * x := by
  have := isSimpleGroup_SL2 ha hK
  refine ⟨(rankOneEquivSL K a hK).symm.isSimpleGroup, ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_SL2_mul_ne_mul (K := K)
  refine ⟨rankOneEquivSL K a hK x, rankOneEquivSL K a hK y, fun h => hxy ?_⟩
  rw [← map_mul, ← map_mul] at h
  exact (rankOneEquivSL K a hK).injective h

variable (K a) in
abbrev reeFixedEmb :
    reeFixed F4 K a →* ModGL F4.tag K :=
  (adjointGroup F4.tag K).subtype.comp (reeFixed F4 K a).subtype

theorem reeFixedEmb_injective :
    Function.Injective (reeFixedEmb K a) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem map_reeFixed_eq_reeGamma :
    (reeFixed F4 K a).map (adjointGroup F4.tag K).subtype = F4.reeGamma K a := by
  rw [reeGamma_eq_reeFixedGroup, reeFixedGroup_eq_map_reeFixed]

omit [Finite K] [CharP K F4.prime] in
theorem map_Uminus_eq_rootSpan
    (w : WeylGroup F4.tag) :
    (Uminus F4.tag K w).map (adjointGroup F4.tag K).subtype =
      rootSpan F4.tag K (inversionSet w) := by
  apply le_antisymm
  · rw [Uminus, Subgroup.map_iSup]
    refine iSup_le fun α => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hα => ?_
    rw [nativeRootSubgroups_X, ← (rootOperatorFamily F4.tag).subgroupOf_rootSubgroup_eq K α,
      Subgroup.subgroupOf_map_subtype]
    refine inf_le_left.trans ?_
    exact le_iSup₂ (f := fun β (_ : β ∈ inversionSet w) => rootSubgroup F4.tag K β) α.1
      ⟨α.2, hα.1, (w • α).2, by rw [← coe_smul_root]; exact hα.2⟩
  · refine iSup₂_le fun β hβ => ?_
    have hle : rootSubgroup F4.tag K β ≤ adjointGroup F4.tag K := rootSubgroup_le_adjointGroup β
    have e : rootSubgroup F4.tag K β =
        ((rootOperatorFamily F4.tag).rootSubgroup K ⟨β, hβ.1⟩).map
          (adjointGroup F4.tag K).subtype := by
      rw [← (rootOperatorFamily F4.tag).subgroupOf_rootSubgroup_eq K ⟨β, hβ.1⟩,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hle]
    rw [e]
    refine Subgroup.map_mono ?_
    rw [Uminus, ← nativeRootSubgroups_X]
    exact le_iSup₂ (f := fun (α : Root F4.tag) (_ : 0 < height α.1 ∧ height (w • α).1 < 0) =>
      (nativeRootSubgroups F4.tag K).X α) ⟨β, hβ.1⟩
      ⟨hβ.2.1, by rw [coe_smul_root]; exact hβ.2.2.2⟩

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem inversionSet_fixedOrbitElement
    (j : Fin F4.fixedOrbitCount) :
    inversionSet (F4.fixedOrbitElement j) = F4.fixedOrbitRoots j := by
  refine Set.Subset.antisymm (inversionSet_fixedOrbitElement_subset j) fun α hα => ?_
  obtain ⟨hr, hp, -⟩ := mem_fixedOrbitRoots_iff.1 hα
  exact ⟨hr, hp, CFSG.LieType.Chevalley.IsRoot.smul hr _, height_fixedOrbitElement_smul_neg hα⟩

theorem map_blockX_one :
    (CFSG.SectionRank.LargeRee.blockX (K := K) a 1).map (reeFixedEmb K a) =
      F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ := by
  have hw : ((CFSG.SectionRank.LargeRee.blockGen 1 : F4.relWeylRee) : WeylGroup F4.tag) =
      F4.fixedOrbitElement ⟨1, by decide⟩ := by
    rw [CFSG.SectionRank.LargeRee.coe_blockGen_one, blockElt_eq]
    rfl
  rw [CFSG.SectionRank.LargeRee.blockX, CFSG.SectionRank.LargeRee.UminusFixed, hw,
    reeFixedEmb, ← Subgroup.map_map, Subgroup.map_comap_eq, Subgroup.range_subtype,
    Subgroup.map_inf_eq _ _ _ Subtype.val_injective, map_Uminus_eq_rootSpan,
    map_reeFixed_eq_reeGamma, inversionSet_fixedOrbitElement, reeFixedOrbitUnipotent]
  exact inf_comm _ _

theorem map_blockT_one
    (hK : Nat.card K = F4.prime ^ (2 * a + 1)) :
    (CFSG.SectionRank.LargeRee.blockT a hK 1).map (reeFixedEmb K a) = rankOneTorusTwo K a := by
  rw [CFSG.SectionRank.LargeRee.blockT_one, CFSG.SectionRank.LargeRee.reeTorusSub,
    MonoidHom.map_range, rankOneTorusTwo]
  congr 1

theorem reeFixedEmb_relNrepHom_one :
    reeFixedEmb K a (CFSG.SectionRank.LargeRee.relNrepHom K a
        (CFSG.SectionRank.LargeRee.blockGen 1)) =
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) := by
  change ((CFSG.SectionRank.LargeRee.relNrepHom K a (CFSG.SectionRank.LargeRee.blockGen 1) :
    adjointGroup F4.tag K) : ModGL F4.tag K) = _
  rw [CFSG.SectionRank.LargeRee.coe_relNrepHom_blockGen_one, blockElt_eq]
  rfl

theorem rankOneGroupTwo_eq_map
    (hK : Nat.card K = F4.prime ^ (2 * a + 1)) :
    rankOneGroupTwo K a = (CFSG.SectionRank.LargeRee.r2 K a hK).map (reeFixedEmb K a) := by
  rw [CFSG.SectionRank.LargeRee.r2, MonoidHom.map_closure, Set.image_union, Set.image_union,
    Set.image_singleton, ← Subgroup.coe_map, ← Subgroup.coe_map, map_blockX_one,
    map_blockT_one hK, reeFixedEmb_relNrepHom_one, rankOneGroupTwo]

variable (K a) in
@[expose] def rankOneEquivSuzuki
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupTwo K a ≃* CFSG.Blueprint.suzukiGroup a K :=
  (MulEquiv.subgroupCongr (rankOneGroupTwo_eq_map hK)).trans
    ((Subgroup.equivMapOfInjective _ _ reeFixedEmb_injective).symm.trans
      (CFSG.SectionRank.LargeRee.r2EquivSuzuki K a hK ha))

theorem card_rankOneGroupTwo
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (rankOneGroupTwo K a) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  rw [Nat.card_congr (rankOneEquivSuzuki K a ha hK).toEquiv, suzuki_order hK]

theorem exists_mul_ne_mul_of_commutator_eq_top {G : Type*} [Group G] [Nontrivial G]
    (h : commutator G = ⊤) : ∃ x y : G, x * y ≠ y * x := by
  by_contra hcomm
  push Not at hcomm
  have hbot : commutator G = ⊥ := by
    rw [commutator, eq_bot_iff, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm x y
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hg' : g ∈ commutator G := h ▸ Subgroup.mem_top g
  rw [hbot, Subgroup.mem_bot] at hg'
  exact hg hg'

theorem isSimpleGroup_rankOneGroupTwo
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSimpleGroup (rankOneGroupTwo K a) ∧ ∃ x y : rankOneGroupTwo K a, x * y ≠ y * x := by
  obtain ⟨-, hnt, hs⟩ := suzuki_simple ha hK
  refine ⟨(rankOneEquivSuzuki K a ha hK).isSimpleGroup, ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_mul_ne_mul_of_commutator_eq_top (suzuki_perfect ha hK).1
  set e := (rankOneEquivSuzuki K a ha hK).symm
  refine ⟨e x, e y, fun h => hxy ?_⟩
  rw [← map_mul, ← map_mul] at h
  exact e.injective h

end CFSG.LieType.Ree.LargeReeInvolution
