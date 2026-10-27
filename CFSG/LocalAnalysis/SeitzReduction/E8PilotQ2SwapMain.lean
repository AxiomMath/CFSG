module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapParam
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapTriangle
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapPair
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainRows
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapCT

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)
open E8Neighbour

local instance e8PilotQ2SwapMainNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

section Model

@[expose] def overlapRoots (N N' : E8Neighbour) : Set (Fin (Tag.rank .E8) → ℤ) :=
  orthRoots N.root ∩ orthRoots N'.root

variable (K : Type) [Field K]

@[expose] noncomputable def overlapSpan (N N' : E8Neighbour) : Subgroup (adjointGroup .E8 K) :=
  (rootSpan .E8 K (overlapRoots N N')).subgroupOf (adjointGroup .E8 K)

@[expose] def E8TwoOverlapInput : Prop :=
  ∀ A : Subgroup (adjointGroup .E8 K), A ≤ posJE8 K → IsCyclic A → Nat.card A = Nat.card K + 1 →
    ∀ N N' : E8Neighbour, N ≠ N' →
      perfectCore (N.levi K ⊓ centralizer
          ((A.map (MulAut.conj (N'.rep K)).toMonoidHom : Subgroup (adjointGroup .E8 K)) :
            Set (adjointGroup .E8 K))) = overlapSpan K N N' ∧
        IsSimpleGroup (overlapSpan K N N') ∧ center (overlapSpan K N N') = ⊥

variable {K}

theorem levi_le_overlapSpan {J : Finset (Fin (Tag.rank .E8))} {N N' : E8Neighbour}
    (h : J ⊆ N.nodes) (h' : J ⊆ N'.nodes) :
    CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J ≤ overlapSpan K N N' := by
  rw [levi_adjDatumE8_eq]
  exact Subgroup.subgroupOf_mono _ (rootSpan_mono_E8 (Set.subset_inter
    (amalgamRoots_subset_orthRoots_iff_subset_nodes.2 h)
    (amalgamRoots_subset_orthRoots_iff_subset_nodes.2 h')))

theorem overlapSpan_sup_eq_top :
    overlapSpan K .high .two ⊔ overlapSpan K .high .six ⊔ overlapSpan K .two .six = ⊤ := by
  have key : ∀ i : Fin (Tag.rank .E8),
      ({i} ⊆ high.nodes ∧ {i} ⊆ two.nodes) ∨ ({i} ⊆ high.nodes ∧ {i} ⊆ six.nodes) ∨
        ({i} ⊆ two.nodes ∧ {i} ⊆ six.nodes) := by
    decide +kernel
  refine top_unique (top_le_of_forall_levi_singleton_le_E8 fun i => ?_)
  rcases key i with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact le_sup_of_le_left (le_sup_of_le_left (levi_le_overlapSpan h1 h2))
  · exact le_sup_of_le_left (le_sup_of_le_right (levi_le_overlapSpan h1 h2))
  · exact le_sup_of_le_right (levi_le_overlapSpan h1 h2)

theorem pinnedX_mem_overlapSpan (N N' : E8Neighbour) :
    (⟨pinnedX .E8 K (Pi.single 0 1) 1, pinnedX_mem_adjointGroup _ 1⟩ : adjointGroup .E8 K) ∈
      overlapSpan K N N' := by
  rw [overlapSpan, mem_subgroupOf]
  have hα : (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) ∈ overlapRoots N N' := by
    refine ⟨⟨isRoot_single _ 0, (N.iform_root_single_eq_zero_iff 0).2 ?_⟩,
      ⟨isRoot_single _ 0, (N'.iform_root_single_eq_zero_iff 0).2 ?_⟩⟩ <;>
    cases N <;> cases N' <;> decide
  exact (le_iSup₂ (f := fun α (_ : α ∈ overlapRoots N N') => rootSubgroup .E8 K α) _ hα)
    (Subgroup.subset_closure ⟨1, rfl⟩)

theorem pinnedX_single_zero_ne_one [CharP K 2] :
    (⟨pinnedX .E8 K (Pi.single 0 1) 1, pinnedX_mem_adjointGroup _ 1⟩ : adjointGroup .E8 K) ≠ 1 :=
  fun h => by
    have h2 := E6Pilot.orderOf_pinnedX_one_adjointGroup (K := K) (τ := .E8)
      (Pi.single (0 : Fin (Tag.rank .E8)) 1)
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)

theorem rootPairSL2_le_levi {N N' : E8Neighbour} (h : N ≠ N') :
    (rootSubgroup .E8 K N'.root ⊔ rootSubgroup .E8 K (-N'.root)).subgroupOf
      (adjointGroup .E8 K) ≤ N.levi K := by
  refine Subgroup.subgroupOf_mono _ (sup_le ?_ ?_)
  · exact le_iSup₂ (f := fun α (_ : α ∈ orthRoots N.root) => rootSubgroup .E8 K α) N'.root
      ⟨N'.isRoot_root, iform_root_root_eq_zero h⟩
  · exact le_iSup₂ (f := fun α (_ : α ∈ orthRoots N.root) => rootSubgroup .E8 K α) (-N'.root)
      ⟨IsRoot.neg N'.isRoot_root, by rw [iform_neg_right_E8, iform_root_root_eq_zero h, neg_zero]⟩

theorem map_conj_rep_le_levi {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K)
    {N N' : E8Neighbour} (h : N ≠ N') :
    A.map (MulAut.conj (N'.rep K)).toMonoidHom ≤ N.levi K :=
  (Subgroup.map_mono hAJ).trans ((map_conj_rep_rootSL2 N').le.trans (rootPairSL2_le_levi h))

end Model

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {C : Type*} [Group C]

theorem map_map_symm_map_conj (e : L ≃* C) (H : Subgroup C) (n : C) :
    ((H.map (MulAut.conj n).toMonoidHom).map e.symm.toMonoidHom).map L.subtype =
      ((H.map e.symm.toMonoidHom).map L.subtype).map
        (MulAut.conj ((e.symm n : L) : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem map_map_symm_inf_centralizer (e : L ≃* C) (M Y : Subgroup C) :
    ((M ⊓ centralizer (Y : Set C)).map e.symm.toMonoidHom).map L.subtype =
      (M.map e.symm.toMonoidHom).map L.subtype ⊓
        centralizer (((Y.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) := by
  have hML : (M.map e.symm.toMonoidHom).map L.subtype ≤ L := map_subtype_le _
  calc ((M ⊓ centralizer (Y : Set C)).map e.symm.toMonoidHom).map L.subtype =
      (M.map e.symm.toMonoidHom).map L.subtype ⊓
        ((centralizer (Y : Set C)).map e.symm.toMonoidHom).map L.subtype := by
        rw [Subgroup.map_inf_eq _ _ _ e.symm.injective,
          Subgroup.map_inf_eq _ _ _ L.subtype_injective]
    _ = (M.map e.symm.toMonoidHom).map L.subtype ⊓ (L ⊓
        centralizer (((Y.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) := by
        rw [F4Pilot.inf_centralizer_map_symm]
    _ = _ := by rw [← inf_assoc, inf_eq_left.2 hML]

@[expose] noncomputable def mapMapSymmEquiv (e : L ≃* C) (H : Subgroup C) :
    H ≃* ((H.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :=
  (H.equivMapOfInjective _ e.symm.injective).trans
    ((H.map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)

end Transport

section Assembly

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] def HR8SwapE8Two (e : L ≃* adjointGroup .E8 K) (t : G) : Prop :=
  ∃ A : Subgroup (adjointGroup .E8 K), A ≤ posJE8 K ∧ Nat.card A = Nat.card K + 1 ∧
    ∃ htX : t ∈ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G),
      NeighbourOvergroupE7Swap
        (QuotientGroup.mk' (oddCore (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))) ⟨t, htX⟩)
        (((((e7Levi K).map e.symm.toMonoidHom).map L.subtype).subgroupOf (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)))))

@[expose] def HR8FieldE8Two (e : L ≃* adjointGroup .E8 K) (t : G) : Prop :=
  ∃ A : Subgroup (adjointGroup .E8 K), A ≤ posJE8 K ∧ Nat.card A = Nat.card K + 1 ∧
    ∃ htX : t ∈ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G),
      NeighbourOvergroupE7Field
        (QuotientGroup.mk' (oddCore (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))) ⟨t, htX⟩)
        (((((e7Levi K).map e.symm.toMonoidHom).map L.subtype).subgroupOf (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))))) 1

@[expose] noncomputable def nonsplitNeighbourG (e : L ≃* adjointGroup .E8 K)
    (A : Subgroup (adjointGroup .E8 K)) (N : E8Neighbour) : Subgroup G :=
  ((A.map (MulAut.conj (N.rep K)).toMonoidHom).map e.symm.toMonoidHom).map L.subtype

variable [Finite G]

theorem exists_swapFactors_E8_two (hO : E8TwoOverlapInput K) {t : G} (hw : E8Work L K t 1)
    (e : L ≃* adjointGroup .E8 K) {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K)
    (hA : Nat.card A = Nat.card K + 1)
    (htX : t ∈ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))
    (hSw : NeighbourOvergroupE7Swap
      (QuotientGroup.mk' (oddCore (centralizer
        (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))) ⟨t, htX⟩)
      (((((e7Levi K).map e.symm.toMonoidHom).map L.subtype).subgroupOf (centralizer
        (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)))))) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        centralizerPerfectCore (nonsplitNeighbourG e A .high ⊔ nonsplitNeighbourG e A .two) ⊔
          centralizerPerfectCore (nonsplitNeighbourG e A .high ⊔ nonsplitNeighbourG e A .six) ⊔
            centralizerPerfectCore (nonsplitNeighbourG e A .two ⊔ nonsplitNeighbourG e A .six) ∧
      ∀ g : G, g⁻¹ * t * g ∈
          normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
        g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have : Finite (adjointGroup .E8 K) := by
    have : Finite (ModGL Tag.E8 K) := finite_modGL
    infer_instance
  have hcycA : IsCyclic A := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card (show Nat.card A = 3 by rw [hA, hK2])
  obtain ⟨P, hinj, hrange⟩ := exists_swapParam_nonsplit_two hw e hAJ hA rfl htX rfl hSw
  clear hSw htX
  generalize hXdef : (A.map e.symm.toMonoidHom).map L.subtype = X at hrange
  generalize hDdef : ((e7Levi K).map e.symm.toMonoidHom).map L.subtype = D at P hinj hrange
  have hn : ∀ N : E8Neighbour,
      ((e.symm (N.rep K) : L) : G) * t = t * ((e.symm (N.rep K) : L) : G) :=
    fun N => mem_centralizer_iff.1 hw.mem_centralizer _ (e.symm (N.rep K)).2
  have hconj : ∀ N : E8Neighbour,
      ∃ P' : SwapParam t (D.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom),
        Function.Injective P'.Ψ ∧ P'.Ψ.range =
          centralizerPerfectCore (X.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom) :=
    fun N => by
      obtain ⟨P', h1, h2⟩ := exists_swapParam_conj P hinj _ (hn N)
      exact ⟨P', h1, by rw [h2, hrange, F4Pilot.map_centralizerPerfectCore]⟩
  obtain ⟨P₁, hinj₁, hrange₁⟩ := hconj .high
  obtain ⟨P₂, hinj₂, hrange₂⟩ := hconj .two
  obtain ⟨P₃, hinj₃, hrange₃⟩ := hconj .six
  have hXN : ∀ N : E8Neighbour, X.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom =
      ((A.map (MulAut.conj (N.rep K)).toMonoidHom).map e.symm.toMonoidHom).map L.subtype :=
    fun N => by
      rw [← hXdef]
      exact (map_map_symm_map_conj e A (N.rep K)).symm
  have hDN : ∀ N : E8Neighbour, D.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom =
      ((N.levi K).map e.symm.toMonoidHom).map L.subtype := fun N => by
    rw [← map_conj_rep_e7Levi N, ← hDdef]
    exact (map_map_symm_map_conj e (e7Levi K) (N.rep K)).symm
  have horth : ∀ N N' : E8Neighbour, N ≠ N' →
      X.map (MulAut.conj ((e.symm (N'.rep K) : L) : G)).toMonoidHom ≤
        D.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom := fun N N' h => by
    rw [hXN, hDN]
    exact Subgroup.map_mono (Subgroup.map_mono (map_conj_rep_le_levi hAJ h))
  have hXL : ∀ N : E8Neighbour,
      X.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom ≤ L := fun N => by
    rw [hXN]
    exact map_subtype_le _
  have hov : ∀ N N' : E8Neighbour, N ≠ N' →
      perfectCore (D.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom ⊓
          centralizer ((X.map (MulAut.conj ((e.symm (N'.rep K) : L) : G)).toMonoidHom :
            Subgroup G) : Set G)) =
        ((overlapSpan K N N').map e.symm.toMonoidHom).map L.subtype := fun N N' h => by
    rw [hDN, hXN, ← map_map_symm_inf_centralizer, ← CFSG.Quasithin.map_perfectCore,
      ← CFSG.Quasithin.map_perfectCore, (hO A hAJ hcycA hA N N' h).1]
  have hsimple : ∀ N N' : E8Neighbour, N ≠ N' →
      IsSimpleGroup (((overlapSpan K N N').map e.symm.toMonoidHom).map L.subtype : Subgroup G) :=
    fun N N' h => by
      have := (hO A hAJ hcycA hA N N' h).2.1
      exact (mapMapSymmEquiv e (overlapSpan K N N')).symm.isSimpleGroup
  have hcenter : ∀ N N' : E8Neighbour, N ≠ N' →
      center (((overlapSpan K N N').map e.symm.toMonoidHom).map L.subtype : Subgroup G) = ⊥ :=
    fun N N' h => F4Pilot.center_eq_bot_congr (mapMapSymmEquiv e (overlapSpan K N N'))
      (hO A hAJ hcycA hA N N' h).2.2
  set q : G := ((e.symm ⟨pinnedX .E8 K (Pi.single 0 1) 1, pinnedX_mem_adjointGroup _ 1⟩ : L) : G)
    with hqdef
  have hq : ∀ N N' : E8Neighbour,
      q ∈ ((overlapSpan K N N').map e.symm.toMonoidHom).map L.subtype := fun N N' =>
    ⟨_, ⟨_, pinnedX_mem_overlapSpan N N', rfl⟩, rfl⟩
  have hq1 : q ≠ 1 := fun h => pinnedX_single_zero_ne_one (K := K)
    (e.symm.injective (Subtype.ext (by rw [map_one]; exact h)))
  have hgen : ((overlapSpan K .high .two).map e.symm.toMonoidHom).map L.subtype ⊔
      ((overlapSpan K .high .six).map e.symm.toMonoidHom).map L.subtype ⊔
        ((overlapSpan K .two .six).map e.symm.toMonoidHom).map L.subtype = L := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_sup,
      overlapSpan_sup_eq_top, Subgroup.map_top_of_surjective _ e.symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hne₁₂ : (E8Neighbour.high : E8Neighbour) ≠ .two := by decide
  have hne₁₃ : (E8Neighbour.high : E8Neighbour) ≠ .six := by decide
  have hne₂₃ : (E8Neighbour.two : E8Neighbour) ≠ .six := by decide
  obtain ⟨G₁, hq', h₁₂', hδ, hsurj, hspan, huniq⟩ := exists_swapFactors_unique_of_swapParam_triangle
    hw.seitz (isSolvable_outer_of_mulEquiv_E8 e) e
    (swapPairExclusion_adjointGroup_E8_two hK2) hw.orderOf_eq (hw.inf_eq e) P₁ P₂ P₃ hinj₁ hinj₂
    hinj₃ hrange₁ hrange₂ hrange₃ (hXL _) (hXL _) (hXL _) (horth _ _ hne₁₂) (horth _ _ hne₁₃)
    (horth _ _ hne₁₂.symm) (horth _ _ hne₂₃) (horth _ _ hne₁₃.symm) (horth _ _ hne₂₃.symm)
    ((hov _ _ hne₁₂).symm ▸ hsimple _ _ hne₁₂) ((hov _ _ hne₁₃).symm ▸ hsimple _ _ hne₁₃)
    ((hov _ _ hne₂₃).symm ▸ hsimple _ _ hne₂₃) ((hov _ _ hne₁₂).symm ▸ hcenter _ _ hne₁₂)
    ((hov _ _ hne₁₃).symm ▸ hcenter _ _ hne₁₃) ((hov _ _ hne₂₃).symm ▸ hcenter _ _ hne₂₃)
    ((hov _ _ hne₁₂).symm ▸ hq _ _) ((hov _ _ hne₁₃).symm ▸ hq _ _) ((hov _ _ hne₂₃).symm ▸ hq _ _)
    hq1 (by rw [hov _ _ hne₁₂, hov _ _ hne₁₃, hov _ _ hne₂₃]; exact hgen)
  refine ⟨G₁, hq', h₁₂', hδ, hsurj, ?_, huniq⟩
  rw [hspan, hXN, hXN, hXN]
  rfl

theorem false_of_swapRow_E8_two (hO : E8TwoOverlapInput K) {t : G} (hw : E8Work L K t 1)
    (e : L ≃* adjointGroup .E8 K) (hS : HR8SwapE8Two e t) : False := by
  obtain ⟨A, hAJ, hA, htX, hSw⟩ := hS
  obtain ⟨G₁, hq, h₁₂, -, -, -, huniq⟩ := exists_swapFactors_E8_two hO hw e hAJ hA htX hSw
  have : IsSimpleGroup G := hw.seitz.1
  exact F4Pilot.false_of_simple_of_swap_of_isQuasisimple hw.orderOf_eq hq h₁₂ rfl huniq

end Assembly

section Remains

@[expose] def E8TwoFieldRowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K]
    (e : L ≃* adjointGroup .E8 K) (t : G), E8Work L K t 1 → HR8FieldE8Two e t → False

theorem e8TwoInput_of_fieldRow (hcat : E7CatalogueClauses)
    (hO : ∀ (K : Type) [Field K], Nat.card K = 2 → E8TwoOverlapInput K)
    (hF : E8TwoFieldRowInput) : E8TwoInput := by
  intro G _ _ L K _ e t hw
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  obtain ⟨A, hAJ, -, hA, htX, -⟩ := hw.exists_not_normal_neighbour_nonsplit_two e
  rcases (hw.neighbour_overgroup_nonsplit_two hcat e hAJ hA rfl htX rfl).field_or_swap with h | h
  · exact hF G L K e t hw ⟨A, hAJ, hA, htX, h⟩
  · exact false_of_swapRow_E8_two (hO K hK2) hw e ⟨A, hAJ, hA, htX, h⟩

end Remains

end CFSG.SeitzReduction.E8Pilot
