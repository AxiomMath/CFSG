module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowParam
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowPair
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverDiag
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapMain
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowSetting

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore F4Work)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)
open E6Neighbour

local instance e6PilotQ2RowSwapNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def overlapRoots (N N' : E6Neighbour) : Set (Fin (Tag.rank .E6) → ℤ) :=
  orthRoots N.root ∩ orthRoots N'.root

@[expose] def overlapCommonRoot : Fin (Tag.rank .E6) → ℤ := ![1, 0, 1, 1, 0, 0]

theorem isRoot_overlapCommonRoot : IsRoot .E6 overlapCommonRoot := by
  have h := IsRoot.reflect 3 (IsRoot.reflect 2 (isRoot_single .E6 0))
  convert h using 1
  decide +kernel

theorem overlapCommonRoot_mem_overlapRoots (N N' : E6Neighbour) :
    overlapCommonRoot ∈ overlapRoots N N' := by
  refine ⟨⟨isRoot_overlapCommonRoot, ?_⟩, ⟨isRoot_overlapCommonRoot, ?_⟩⟩ <;> cases N <;>
    cases N' <;> decide +kernel

theorem single_mem_overlapRoots (j : Fin (Tag.rank .E6)) :
    Pi.single j 1 ∈ overlapRoots .high .six ∨ Pi.single j 1 ∈ overlapRoots .high .three ∨
      Pi.single j 1 ∈ overlapRoots .six .three := by
  have key : ∀ j : Fin (Tag.rank .E6),
      (iform high.root (Pi.single j 1) = 0 ∧ iform six.root (Pi.single j 1) = 0) ∨
        (iform high.root (Pi.single j 1) = 0 ∧ iform three.root (Pi.single j 1) = 0) ∨
        (iform six.root (Pi.single j 1) = 0 ∧ iform three.root (Pi.single j 1) = 0) := by
    decide +kernel
  rcases key j with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨⟨isRoot_single _ j, h1⟩, ⟨isRoot_single _ j, h2⟩⟩
  · exact .inr (.inl ⟨⟨isRoot_single _ j, h1⟩, ⟨isRoot_single _ j, h2⟩⟩)
  · exact .inr (.inr ⟨⟨isRoot_single _ j, h1⟩, ⟨isRoot_single _ j, h2⟩⟩)

theorem amalgamRoots_singleton_subset_overlapRoots {N N' : E6Neighbour} {j : Fin (Tag.rank .E6)}
    (h : Pi.single j 1 ∈ overlapRoots N N') : amalgamRoots {j} ⊆ overlapRoots N N' := by
  have h1 : amalgamRoots {j} ⊆ orthRoots N.root :=
    amalgamRoots_subset_orthRoots_iff.2 fun i hi => by
      rw [Finset.mem_singleton] at hi
      subst hi
      exact h.1.2
  have h2 : amalgamRoots {j} ⊆ orthRoots N'.root :=
    amalgamRoots_subset_orthRoots_iff.2 fun i hi => by
      rw [Finset.mem_singleton] at hi
      subst hi
      exact h.2.2
  exact fun γ hγ => ⟨h1 hγ, h2 hγ⟩

section Model


variable (K : Type) [Field K]

@[expose] noncomputable def overlapSpan (N N' : E6Neighbour) : Subgroup (adjointGroup .E6 K) :=
  (rootSpan .E6 K (overlapRoots N N')).subgroupOf (adjointGroup .E6 K)

@[expose] def E6TwoOverlapInput : Prop :=
  Nat.card K = 2 →
  ∀ A : Subgroup (adjointGroup .E6 K), A ≤ posJ K → Nat.card A = Nat.card K + 1 →
    ∀ N N' : E6Neighbour, N ≠ N' →
      perfectCore (N.levi K ⊓ centralizer
          ((A.map (MulAut.conj (N'.rep K)).toMonoidHom : Subgroup (adjointGroup .E6 K)) :
            Set (adjointGroup .E6 K))) = overlapSpan K N N' ∧
        IsSimpleGroup (overlapSpan K N N') ∧ center (overlapSpan K N N') = ⊥

variable {K}

theorem overlapSpan_le_levi (N N' : E6Neighbour) : overlapSpan K N N' ≤ N.levi K :=
  Subgroup.subgroupOf_mono _ (rootSpan_mono_E6 Set.inter_subset_left)

theorem levi_singleton_le_overlapSpan {N N' : E6Neighbour} {j : Fin (Tag.rank .E6)}
    (h : Pi.single j 1 ∈ overlapRoots N N') :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j} ≤ overlapSpan K N N' := by
  rw [levi_adjDatumE6_eq]
  exact Subgroup.subgroupOf_mono _
    (rootSpan_mono_E6 (amalgamRoots_singleton_subset_overlapRoots h))

theorem overlapSpan_sup_eq_top :
    overlapSpan K .high .six ⊔ overlapSpan K .high .three ⊔ overlapSpan K .six .three = ⊤ := by
  refine top_unique (top_le_of_forall_levi_singleton_le_E6 fun j => ?_)
  rcases single_mem_overlapRoots j with h | h | h
  · exact le_sup_of_le_left (le_sup_of_le_left (levi_singleton_le_overlapSpan h))
  · exact le_sup_of_le_left (le_sup_of_le_right (levi_singleton_le_overlapSpan h))
  · exact le_sup_of_le_right (levi_singleton_le_overlapSpan h)

theorem pinnedX_overlapCommonRoot_mem_overlapSpan (N N' : E6Neighbour) :
    (⟨pinnedX .E6 K overlapCommonRoot 1, pinnedX_mem_adjointGroup _ 1⟩ : adjointGroup .E6 K) ∈
      overlapSpan K N N' := by
  rw [overlapSpan, mem_subgroupOf]
  exact (le_iSup₂ (f := fun α (_ : α ∈ overlapRoots N N') => rootSubgroup .E6 K α) _
    (overlapCommonRoot_mem_overlapRoots N N')) (Subgroup.subset_closure ⟨1, rfl⟩)

theorem pinnedX_overlapCommonRoot_ne_one [CharP K 2] :
    (⟨pinnedX .E6 K overlapCommonRoot 1, pinnedX_mem_adjointGroup _ 1⟩ : adjointGroup .E6 K) ≠ 1 :=
  fun h => by
    have h2 := orderOf_pinnedX_one_adjointGroup (K := K) (τ := .E6) overlapCommonRoot
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)

theorem rootPairSL2_le_levi_E6 {N N' : E6Neighbour} (h : N ≠ N') :
    (rootSubgroup .E6 K N'.root ⊔ rootSubgroup .E6 K (-N'.root)).subgroupOf
      (adjointGroup .E6 K) ≤ N.levi K := by
  refine Subgroup.subgroupOf_mono _ (sup_le ?_ ?_)
  · exact le_iSup₂ (f := fun α (_ : α ∈ orthRoots N.root) => rootSubgroup .E6 K α) N'.root
      ⟨N'.isRoot_root, iform_root_root_eq_zero h⟩
  · exact le_iSup₂ (f := fun α (_ : α ∈ orthRoots N.root) => rootSubgroup .E6 K α) (-N'.root)
      ⟨IsRoot.neg N'.isRoot_root, by rw [iform_neg_right_E6, iform_root_root_eq_zero h, neg_zero]⟩

theorem map_conj_rep_le_levi_E6 {A : Subgroup (adjointGroup .E6 K)} (hAJ : A ≤ posJ K)
    {N N' : E6Neighbour} (h : N ≠ N') :
    A.map (MulAut.conj (N'.rep K)).toMonoidHom ≤ N.levi K :=
  (Subgroup.map_mono hAJ).trans ((map_conj_rep_rootSL2 N').le.trans (rootPairSL2_le_levi_E6 h))

end Model

section Assembly


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def nonsplitNeighbourG (e : L ≃* adjointGroup .E6 K)
    (A : Subgroup (adjointGroup .E6 K)) (N : E6Neighbour) : Subgroup G :=
  ((A.map (MulAut.conj (N.rep K)).toMonoidHom).map e.symm.toMonoidHom).map L.subtype

variable [Finite G]

theorem exists_swapFactors_E6_two (hO : E6TwoOverlapInput K) {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .E6 K) {A : Subgroup (adjointGroup .E6 K)} (hAJ : A ≤ posJ K)
    (hA : Nat.card A = 3)
    (htX : t ∈ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))
    (hSw : NeighbourOvergroupSLSwapKind
      (QuotientGroup.mk' (oddCore (centralizer
        (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))) ⟨t, htX⟩)
      (((rootLeviG e).subgroupOf
        (centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)))))) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        centralizerPerfectCore (nonsplitNeighbourG e A .high ⊔ nonsplitNeighbourG e A .six) ⊔
          centralizerPerfectCore
            (nonsplitNeighbourG e A .high ⊔ nonsplitNeighbourG e A .three) ⊔
            centralizerPerfectCore
              (nonsplitNeighbourG e A .six ⊔ nonsplitNeighbourG e A .three) ∧
      ∀ g : G, g⁻¹ * t * g ∈
          normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
        g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have : Finite (adjointGroup .E6 K) := by
    have : Finite (ModGL Tag.E6 K) := finite_modGL
    infer_instance
  have hA' : Nat.card A = Nat.card K + 1 := by rw [hA, hK2]
  obtain ⟨P, hinj, hrange⟩ := exists_swapParam_nonsplit_E6_two hw e hAJ hA rfl htX rfl hSw
  clear hSw htX
  generalize hXdef : (A.map e.symm.toMonoidHom).map L.subtype = X at hrange
  generalize hDdef : ((a5Levi K).map e.symm.toMonoidHom).map L.subtype = D at P hinj hrange
  have hn : ∀ N : E6Neighbour,
      ((e.symm (N.rep K) : L) : G) * t = t * ((e.symm (N.rep K) : L) : G) :=
    fun N => mem_centralizer_iff.1 hw.mem_centralizer _ (e.symm (N.rep K)).2
  have hconj : ∀ N : E6Neighbour,
      ∃ P' : SwapParam t (D.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom),
        Function.Injective P'.Ψ ∧ P'.Ψ.range =
          centralizerPerfectCore (X.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom) :=
    fun N => by
      obtain ⟨P', h1, h2⟩ := E8Pilot.exists_swapParam_conj P hinj _ (hn N)
      exact ⟨P', h1, by rw [h2, hrange, F4Pilot.map_centralizerPerfectCore]⟩
  obtain ⟨P₁, hinj₁, hrange₁⟩ := hconj .high
  obtain ⟨P₂, hinj₂, hrange₂⟩ := hconj .six
  obtain ⟨P₃, hinj₃, hrange₃⟩ := hconj .three
  have hXN : ∀ N : E6Neighbour, X.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom =
      ((A.map (MulAut.conj (N.rep K)).toMonoidHom).map e.symm.toMonoidHom).map L.subtype :=
    fun N => by
      rw [← hXdef]
      exact (E8Pilot.map_map_symm_map_conj e A (N.rep K)).symm
  have hDN : ∀ N : E6Neighbour, D.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom =
      ((N.levi K).map e.symm.toMonoidHom).map L.subtype := fun N => by
    rw [← map_conj_rep_a5Levi N, ← hDdef]
    exact (E8Pilot.map_map_symm_map_conj e (a5Levi K) (N.rep K)).symm
  have horth : ∀ N N' : E6Neighbour, N ≠ N' →
      X.map (MulAut.conj ((e.symm (N'.rep K) : L) : G)).toMonoidHom ≤
        D.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom := fun N N' h => by
    rw [hXN, hDN]
    exact Subgroup.map_mono (Subgroup.map_mono (map_conj_rep_le_levi_E6 hAJ h))
  have hXL : ∀ N : E6Neighbour,
      X.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom ≤ L := fun N => by
    rw [hXN]
    exact map_subtype_le _
  have hov : ∀ N N' : E6Neighbour, N ≠ N' →
      perfectCore (D.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom ⊓
          centralizer ((X.map (MulAut.conj ((e.symm (N'.rep K) : L) : G)).toMonoidHom :
            Subgroup G) : Set G)) =
        ((overlapSpan K N N').map e.symm.toMonoidHom).map L.subtype := fun N N' h => by
    rw [hDN, hXN, ← E8Pilot.map_map_symm_inf_centralizer, ← CFSG.Quasithin.map_perfectCore,
      ← CFSG.Quasithin.map_perfectCore, (hO hK2 A hAJ hA' N N' h).1]
  have hsimple : ∀ N N' : E6Neighbour, N ≠ N' →
      IsSimpleGroup (((overlapSpan K N N').map e.symm.toMonoidHom).map L.subtype :
        Subgroup G) :=
    fun N N' h => by
      have := (hO hK2 A hAJ hA' N N' h).2.1
      exact (E8Pilot.mapMapSymmEquiv e (overlapSpan K N N')).symm.isSimpleGroup
  have hcenter : ∀ N N' : E6Neighbour, N ≠ N' →
      center (((overlapSpan K N N').map e.symm.toMonoidHom).map L.subtype : Subgroup G) = ⊥ :=
    fun N N' h => F4Pilot.center_eq_bot_congr (E8Pilot.mapMapSymmEquiv e (overlapSpan K N N'))
      (hO hK2 A hAJ hA' N N' h).2.2
  set q : G := ((e.symm ⟨pinnedX .E6 K overlapCommonRoot 1, pinnedX_mem_adjointGroup _ 1⟩ : L) : G)
    with hqdef
  have hq : ∀ N N' : E6Neighbour,
      q ∈ ((overlapSpan K N N').map e.symm.toMonoidHom).map L.subtype := fun N N' =>
    ⟨_, ⟨_, pinnedX_overlapCommonRoot_mem_overlapSpan N N', rfl⟩, rfl⟩
  have hq1 : q ≠ 1 := fun h => pinnedX_overlapCommonRoot_ne_one (K := K)
    (e.symm.injective (Subtype.ext (by rw [map_one]; exact h)))
  have hgen : ((overlapSpan K .high .six).map e.symm.toMonoidHom).map L.subtype ⊔
      ((overlapSpan K .high .three).map e.symm.toMonoidHom).map L.subtype ⊔
        ((overlapSpan K .six .three).map e.symm.toMonoidHom).map L.subtype = L := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_sup,
      overlapSpan_sup_eq_top, Subgroup.map_top_of_surjective _ e.symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hne₁₂ : (E6Neighbour.high : E6Neighbour) ≠ .six := by decide
  have hne₁₃ : (E6Neighbour.high : E6Neighbour) ≠ .three := by decide
  have hne₂₃ : (E6Neighbour.six : E6Neighbour) ≠ .three := by decide
  obtain ⟨G₁, hq', h₁₂', hδ, hsurj, hspan, huniq⟩ :=
    E8Pilot.exists_swapFactors_unique_of_swapParam_triangle (seitzSetting_of_f4Work_E6_two hw e)
      (isSolvable_outer_of_mulEquiv_E6 e) e (swapPairExclusion_adjointGroup_E6_two hK2)
      hw.orderOf_eq hw.inf_eq P₁ P₂ P₃ hinj₁ hinj₂ hinj₃ hrange₁ hrange₂ hrange₃ (hXL _)
      (hXL _) (hXL _) (horth _ _ hne₁₂) (horth _ _ hne₁₃) (horth _ _ hne₁₂.symm)
      (horth _ _ hne₂₃) (horth _ _ hne₁₃.symm) (horth _ _ hne₂₃.symm)
      ((hov _ _ hne₁₂).symm ▸ hsimple _ _ hne₁₂) ((hov _ _ hne₁₃).symm ▸ hsimple _ _ hne₁₃)
      ((hov _ _ hne₂₃).symm ▸ hsimple _ _ hne₂₃) ((hov _ _ hne₁₂).symm ▸ hcenter _ _ hne₁₂)
      ((hov _ _ hne₁₃).symm ▸ hcenter _ _ hne₁₃) ((hov _ _ hne₂₃).symm ▸ hcenter _ _ hne₂₃)
      ((hov _ _ hne₁₂).symm ▸ hq _ _) ((hov _ _ hne₁₃).symm ▸ hq _ _)
      ((hov _ _ hne₂₃).symm ▸ hq _ _) hq1
      (by rw [hov _ _ hne₁₂, hov _ _ hne₁₃, hov _ _ hne₂₃]; exact hgen)
  refine ⟨G₁, hq', h₁₂', hδ, hsurj, ?_, huniq⟩
  rw [hspan, hXN, hXN, hXN]
  rfl

theorem false_of_swapRow_E6_two (hO : E6TwoOverlapInput K) {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .E6 K) {A : Subgroup (adjointGroup .E6 K)} (hAJ : A ≤ posJ K)
    (hA : Nat.card A = 3)
    (htX : t ∈ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))
    (hSw : NeighbourOvergroupSLSwapKind
      (QuotientGroup.mk' (oddCore (centralizer
        (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))) ⟨t, htX⟩)
      (((rootLeviG e).subgroupOf
        (centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)))))) : False := by
  obtain ⟨G₁, hq, h₁₂, -, -, -, huniq⟩ := exists_swapFactors_E6_two hO hw e hAJ hA htX hSw
  have : IsSimpleGroup G := hw.standard.simple
  exact F4Pilot.false_of_simple_of_swap_of_isQuasisimple hw.orderOf_eq hq h₁₂ rfl huniq

end Assembly

end CFSG.SeitzReduction.E6Pilot
