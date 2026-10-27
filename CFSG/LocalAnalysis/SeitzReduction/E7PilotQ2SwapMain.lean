module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2SwapParam
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2SwapPair
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)
open E7Neighbour

local instance e7PilotQ2SwapMainNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

namespace E7Neighbour

@[expose] def thirdRoot : E7Neighbour → E7Neighbour → Fin (Tag.rank .E7) → ℤ
  | high, seven => ![0, 1, 1, 2, 2, 2, 1]
  | seven, high => ![0, 1, 1, 2, 2, 2, 1]
  | high, four => ![0, 1, 1, 1, 0, 0, 0]
  | four, high => ![0, 1, 1, 1, 0, 0, 0]
  | seven, four => ![0, 1, 0, 1, 1, 0, 0]
  | four, seven => ![0, 1, 0, 1, 1, 0, 0]
  | N, _ => N.root

end E7Neighbour

@[expose] def overlapRootsD4 (N N' : E7Neighbour) : Set (Fin (Tag.rank .E7) → ℤ) :=
  orthRoots N.root ∩ orthRoots N'.root ∩ orthRoots (N.thirdRoot N')

@[expose] def overlapCommonRoot : Fin (Tag.rank .E7) → ℤ := ![0, 0, 1, 1, 1, 0, 0]

theorem isRoot_overlapCommonRoot : IsRoot .E7 overlapCommonRoot := by
  have h := IsRoot.reflect 4 (IsRoot.reflect 3 (isRoot_single .E7 2))
  convert h using 1
  decide +kernel

theorem overlapCommonRoot_mem_overlapRootsD4 (N N' : E7Neighbour) :
    overlapCommonRoot ∈ overlapRootsD4 N N' := by
  refine ⟨⟨⟨isRoot_overlapCommonRoot, ?_⟩, ⟨isRoot_overlapCommonRoot, ?_⟩⟩,
    ⟨isRoot_overlapCommonRoot, ?_⟩⟩ <;> cases N <;> cases N' <;> decide +kernel

theorem single_mem_overlapRootsD4 (j : Fin (Tag.rank .E7)) :
    Pi.single j 1 ∈ overlapRootsD4 .high .seven ∨ Pi.single j 1 ∈ overlapRootsD4 .high .four ∨
      Pi.single j 1 ∈ overlapRootsD4 .seven .four := by
  have key : ∀ j : Fin (Tag.rank .E7),
      (iform high.root (Pi.single j 1) = 0 ∧ iform seven.root (Pi.single j 1) = 0 ∧
          iform (high.thirdRoot seven) (Pi.single j 1) = 0) ∨
        (iform high.root (Pi.single j 1) = 0 ∧ iform four.root (Pi.single j 1) = 0 ∧
          iform (high.thirdRoot four) (Pi.single j 1) = 0) ∨
        (iform seven.root (Pi.single j 1) = 0 ∧ iform four.root (Pi.single j 1) = 0 ∧
          iform (seven.thirdRoot four) (Pi.single j 1) = 0) := by
    decide +kernel
  rcases key j with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact .inl ⟨⟨⟨isRoot_single _ j, h1⟩, ⟨isRoot_single _ j, h2⟩⟩, ⟨isRoot_single _ j, h3⟩⟩
  · exact .inr (.inl ⟨⟨⟨isRoot_single _ j, h1⟩, ⟨isRoot_single _ j, h2⟩⟩,
      ⟨isRoot_single _ j, h3⟩⟩)
  · exact .inr (.inr ⟨⟨⟨isRoot_single _ j, h1⟩, ⟨isRoot_single _ j, h2⟩⟩,
      ⟨isRoot_single _ j, h3⟩⟩)

theorem neg_mem_orthRoots {θ α : Fin (Tag.rank .E7) → ℤ} (h : α ∈ orthRoots θ) :
    -α ∈ orthRoots θ :=
  ⟨IsRoot.neg h.1, by rw [iform_neg_right_E7, h.2, neg_zero]⟩

theorem neg_mem_overlapRootsD4 {N N' : E7Neighbour} {α : Fin (Tag.rank .E7) → ℤ}
    (h : α ∈ overlapRootsD4 N N') : -α ∈ overlapRootsD4 N N' :=
  ⟨⟨neg_mem_orthRoots h.1.1, neg_mem_orthRoots h.1.2⟩, neg_mem_orthRoots h.2⟩

theorem amalgamRoots_singleton_subset_overlapRootsD4 {N N' : E7Neighbour} {j : Fin (Tag.rank .E7)}
    (h : Pi.single j 1 ∈ overlapRootsD4 N N') : amalgamRoots {j} ⊆ overlapRootsD4 N N' := by
  rintro γ ⟨i, hi, rfl | rfl⟩ <;> rw [Finset.mem_singleton] at hi <;> subst hi
  · exact h
  · exact neg_mem_overlapRootsD4 h

section Model

variable (K : Type) [Field K]

@[expose] noncomputable def overlapSpanD4 (N N' : E7Neighbour) : Subgroup (adjointGroup .E7 K) :=
  (rootSpan .E7 K (overlapRootsD4 N N')).subgroupOf (adjointGroup .E7 K)

@[expose] def E7TwoOverlapInput : Prop :=
  Nat.card K = 2 →
  ∀ A : Subgroup (adjointGroup .E7 K), A ≤ posJE7 K → Nat.card A = Nat.card K + 1 →
    ∀ N N' : E7Neighbour, N ≠ N' →
      perfectCore (N.levi K ⊓ centralizer
          ((A.map (MulAut.conj (N'.rep K)).toMonoidHom : Subgroup (adjointGroup .E7 K)) :
            Set (adjointGroup .E7 K))) = overlapSpanD4 K N N' ∧
        IsSimpleGroup (overlapSpanD4 K N N') ∧ center (overlapSpanD4 K N N') = ⊥

variable {K}

theorem levi_singleton_le_overlapSpanD4 {N N' : E7Neighbour} {j : Fin (Tag.rank .E7)}
    (h : Pi.single j 1 ∈ overlapRootsD4 N N') :
    CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup {j} ≤ overlapSpanD4 K N N' := by
  rw [levi_adjDatumE7_eq]
  exact Subgroup.subgroupOf_mono _
    (rootSpan_mono_E7 (amalgamRoots_singleton_subset_overlapRootsD4 h))

theorem overlapSpanD4_sup_eq_top :
    overlapSpanD4 K .high .seven ⊔ overlapSpanD4 K .high .four ⊔ overlapSpanD4 K .seven .four =
      ⊤ := by
  refine top_unique (top_le_of_levi_singleton_le_E7 fun j => ?_)
  rcases single_mem_overlapRootsD4 j with h | h | h
  · exact le_sup_of_le_left (le_sup_of_le_left (levi_singleton_le_overlapSpanD4 h))
  · exact le_sup_of_le_left (le_sup_of_le_right (levi_singleton_le_overlapSpanD4 h))
  · exact le_sup_of_le_right (levi_singleton_le_overlapSpanD4 h)

theorem pinnedX_overlapCommonRoot_mem_overlapSpanD4 (N N' : E7Neighbour) :
    (⟨pinnedX .E7 K overlapCommonRoot 1, pinnedX_mem_adjointGroup _ 1⟩ : adjointGroup .E7 K) ∈
      overlapSpanD4 K N N' := by
  rw [overlapSpanD4, mem_subgroupOf]
  exact (le_iSup₂ (f := fun α (_ : α ∈ overlapRootsD4 N N') => rootSubgroup .E7 K α) _
    (overlapCommonRoot_mem_overlapRootsD4 N N')) (Subgroup.subset_closure ⟨1, rfl⟩)

theorem pinnedX_overlapCommonRoot_ne_one [CharP K 2] :
    (⟨pinnedX .E7 K overlapCommonRoot 1, pinnedX_mem_adjointGroup _ 1⟩ : adjointGroup .E7 K) ≠ 1 :=
  fun h => by
    have h2 := E6Pilot.orderOf_pinnedX_one_adjointGroup (K := K) (τ := .E7) overlapCommonRoot
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)

theorem rootPairSL2_le_levi_E7 {N N' : E7Neighbour} (h : N ≠ N') :
    (rootSubgroup .E7 K N'.root ⊔ rootSubgroup .E7 K (-N'.root)).subgroupOf
      (adjointGroup .E7 K) ≤ N.levi K := by
  refine Subgroup.subgroupOf_mono _ (sup_le ?_ ?_)
  · exact le_iSup₂ (f := fun α (_ : α ∈ orthRoots N.root) => rootSubgroup .E7 K α) N'.root
      ⟨N'.isRoot_root, iform_root_root_eq_zero h⟩
  · exact le_iSup₂ (f := fun α (_ : α ∈ orthRoots N.root) => rootSubgroup .E7 K α) (-N'.root)
      ⟨IsRoot.neg N'.isRoot_root, by rw [iform_neg_right_E7, iform_root_root_eq_zero h, neg_zero]⟩

theorem map_conj_rep_le_levi_E7 {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K)
    {N N' : E7Neighbour} (h : N ≠ N') :
    A.map (MulAut.conj (N'.rep K)).toMonoidHom ≤ N.levi K :=
  (Subgroup.map_mono hAJ).trans ((map_conj_rep_rootSL2 N').le.trans (rootPairSL2_le_levi_E7 h))

end Model

section Assembly

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] def HR8SwapE7Two (e : L ≃* adjointGroup .E7 K) (t : G) : Prop :=
  ∃ A : Subgroup (adjointGroup .E7 K), A ≤ posJE7 K ∧ Nat.card A = Nat.card K + 1 ∧
    ∃ htX : t ∈ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G),
      NeighbourOvergroupOmegaSwap
        (QuotientGroup.mk' (oddCore (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))) ⟨t, htX⟩)
        (((((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype).subgroupOf
          (centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)))))

@[expose] def HR8FieldE7Two (e : L ≃* adjointGroup .E7 K) (t : G) (f : ℕ) : Prop :=
  ∃ A : Subgroup (adjointGroup .E7 K), A ≤ posJE7 K ∧ Nat.card A = Nat.card K + 1 ∧
    ∃ htX : t ∈ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G),
      NeighbourOvergroupOmegaField
        (QuotientGroup.mk' (oddCore (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))) ⟨t, htX⟩)
        (((((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype).subgroupOf
          (centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))))) 6 f

@[expose] noncomputable def nonsplitNeighbourE7G (e : L ≃* adjointGroup .E7 K)
    (A : Subgroup (adjointGroup .E7 K)) (N : E7Neighbour) : Subgroup G :=
  ((A.map (MulAut.conj (N.rep K)).toMonoidHom).map e.symm.toMonoidHom).map L.subtype

variable [Finite G]

theorem exists_swapFactors_E7_two (hO : E7TwoOverlapInput K) {t : G} (hw : E7Work L K t 1)
    (e : L ≃* adjointGroup .E7 K) {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K)
    (hA : Nat.card A = Nat.card K + 1)
    (htX : t ∈ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))
    (hSw : NeighbourOvergroupOmegaSwap
      (QuotientGroup.mk' (oddCore (centralizer
        (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))) ⟨t, htX⟩)
      (((((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype).subgroupOf
        (centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)))))) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        centralizerPerfectCore (nonsplitNeighbourE7G e A .high ⊔ nonsplitNeighbourE7G e A .seven) ⊔
          centralizerPerfectCore
            (nonsplitNeighbourE7G e A .high ⊔ nonsplitNeighbourE7G e A .four) ⊔
            centralizerPerfectCore
              (nonsplitNeighbourE7G e A .seven ⊔ nonsplitNeighbourE7G e A .four) ∧
      ∀ g : G, g⁻¹ * t * g ∈
          normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
        g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have : Finite (adjointGroup .E7 K) := by
    have : Finite (ModGL Tag.E7 K) := finite_modGL
    infer_instance
  obtain ⟨P, hinj, hrange⟩ := exists_swapParam_nonsplit_E7_two hw e hAJ hA rfl htX rfl hSw
  clear hSw htX
  generalize hXdef : (A.map e.symm.toMonoidHom).map L.subtype = X at hrange
  generalize hDdef : ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype = D
    at P hinj hrange
  have hn : ∀ N : E7Neighbour,
      ((e.symm (N.rep K) : L) : G) * t = t * ((e.symm (N.rep K) : L) : G) :=
    fun N => mem_centralizer_iff.1 hw.mem_centralizer _ (e.symm (N.rep K)).2
  have hconj : ∀ N : E7Neighbour,
      ∃ P' : SwapParam t (D.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom),
        Function.Injective P'.Ψ ∧ P'.Ψ.range =
          centralizerPerfectCore (X.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom) :=
    fun N => by
      obtain ⟨P', h1, h2⟩ := E8Pilot.exists_swapParam_conj P hinj _ (hn N)
      exact ⟨P', h1, by rw [h2, hrange, F4Pilot.map_centralizerPerfectCore]⟩
  obtain ⟨P₁, hinj₁, hrange₁⟩ := hconj .high
  obtain ⟨P₂, hinj₂, hrange₂⟩ := hconj .seven
  obtain ⟨P₃, hinj₃, hrange₃⟩ := hconj .four
  have hXN : ∀ N : E7Neighbour, X.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom =
      ((A.map (MulAut.conj (N.rep K)).toMonoidHom).map e.symm.toMonoidHom).map L.subtype :=
    fun N => by
      rw [← hXdef]
      exact (E8Pilot.map_map_symm_map_conj e A (N.rep K)).symm
  have hDN : ∀ N : E7Neighbour, D.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom =
      ((N.levi K).map e.symm.toMonoidHom).map L.subtype := fun N => by
    rw [← map_conj_rep_perpLevi N, ← hDdef]
    exact (E8Pilot.map_map_symm_map_conj e (EPilot.perpLevi .E7 K) (N.rep K)).symm
  have horth : ∀ N N' : E7Neighbour, N ≠ N' →
      X.map (MulAut.conj ((e.symm (N'.rep K) : L) : G)).toMonoidHom ≤
        D.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom := fun N N' h => by
    rw [hXN, hDN]
    exact Subgroup.map_mono (Subgroup.map_mono (map_conj_rep_le_levi_E7 hAJ h))
  have hXL : ∀ N : E7Neighbour,
      X.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom ≤ L := fun N => by
    rw [hXN]
    exact map_subtype_le _
  have hov : ∀ N N' : E7Neighbour, N ≠ N' →
      perfectCore (D.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom ⊓
          centralizer ((X.map (MulAut.conj ((e.symm (N'.rep K) : L) : G)).toMonoidHom :
            Subgroup G) : Set G)) =
        ((overlapSpanD4 K N N').map e.symm.toMonoidHom).map L.subtype := fun N N' h => by
    rw [hDN, hXN, ← E8Pilot.map_map_symm_inf_centralizer, ← CFSG.Quasithin.map_perfectCore,
      ← CFSG.Quasithin.map_perfectCore, (hO hK2 A hAJ hA N N' h).1]
  have hsimple : ∀ N N' : E7Neighbour, N ≠ N' →
      IsSimpleGroup (((overlapSpanD4 K N N').map e.symm.toMonoidHom).map L.subtype :
        Subgroup G) :=
    fun N N' h => by
      have := (hO hK2 A hAJ hA N N' h).2.1
      exact (E8Pilot.mapMapSymmEquiv e (overlapSpanD4 K N N')).symm.isSimpleGroup
  have hcenter : ∀ N N' : E7Neighbour, N ≠ N' →
      center (((overlapSpanD4 K N N').map e.symm.toMonoidHom).map L.subtype : Subgroup G) = ⊥ :=
    fun N N' h => F4Pilot.center_eq_bot_congr (E8Pilot.mapMapSymmEquiv e (overlapSpanD4 K N N'))
      (hO hK2 A hAJ hA N N' h).2.2
  set q : G := ((e.symm ⟨pinnedX .E7 K overlapCommonRoot 1, pinnedX_mem_adjointGroup _ 1⟩ : L) : G)
    with hqdef
  have hq : ∀ N N' : E7Neighbour,
      q ∈ ((overlapSpanD4 K N N').map e.symm.toMonoidHom).map L.subtype := fun N N' =>
    ⟨_, ⟨_, pinnedX_overlapCommonRoot_mem_overlapSpanD4 N N', rfl⟩, rfl⟩
  have hq1 : q ≠ 1 := fun h => pinnedX_overlapCommonRoot_ne_one (K := K)
    (e.symm.injective (Subtype.ext (by rw [map_one]; exact h)))
  have hgen : ((overlapSpanD4 K .high .seven).map e.symm.toMonoidHom).map L.subtype ⊔
      ((overlapSpanD4 K .high .four).map e.symm.toMonoidHom).map L.subtype ⊔
        ((overlapSpanD4 K .seven .four).map e.symm.toMonoidHom).map L.subtype = L := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_sup,
      overlapSpanD4_sup_eq_top, Subgroup.map_top_of_surjective _ e.symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hne₁₂ : (E7Neighbour.high : E7Neighbour) ≠ .seven := by decide
  have hne₁₃ : (E7Neighbour.high : E7Neighbour) ≠ .four := by decide
  have hne₂₃ : (E7Neighbour.seven : E7Neighbour) ≠ .four := by decide
  obtain ⟨G₁, hq', h₁₂', hδ, hsurj, hspan, huniq⟩ :=
    E8Pilot.exists_swapFactors_unique_of_swapParam_triangle hw.seitz
      (isSolvable_outer_of_mulEquiv_E7_of_finite e) e (swapPairExclusion_adjointGroup_E7_two hK2)
      hw.orderOf_eq (hw.inf_eq e) P₁ P₂ P₃ hinj₁ hinj₂ hinj₃ hrange₁ hrange₂ hrange₃ (hXL _)
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

theorem false_of_swapRow_E7_two (hO : E7TwoOverlapInput K) {t : G} (hw : E7Work L K t 1)
    (e : L ≃* adjointGroup .E7 K) (hS : HR8SwapE7Two e t) : False := by
  obtain ⟨A, hAJ, hA, htX, hSw⟩ := hS
  obtain ⟨G₁, hq, h₁₂, -, -, -, huniq⟩ := exists_swapFactors_E7_two hO hw e hAJ hA htX hSw
  have : IsSimpleGroup G := hw.seitz.1
  exact F4Pilot.false_of_simple_of_swap_of_isQuasisimple hw.orderOf_eq hq h₁₂ rfl huniq

end Assembly

end CFSG.SeitzReduction.E7Pilot
