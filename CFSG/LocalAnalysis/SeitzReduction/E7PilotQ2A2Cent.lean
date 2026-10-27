module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2OverlapCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction.EPilot CFSG.RankThree.Chevalley
open scoped Pointwise

local instance e7PilotQ2A2CentNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def a2Root : Fin (Tag.rank .E7) → ℤ := ![1, 2, 3, 4, 3, 2, 1]

theorem iform_a2Root_single_check : ∀ j : Fin (Tag.rank .E7),
    iform a2Root (Pi.single j 1) = (if j = 2 then 1 else 0) - (if j = 0 then 1 else 0) := by
  decide +kernel

theorem iform_a2Root (v : Fin (Tag.rank .E7) → ℤ) : iform a2Root v = v 2 - v 0 := by
  rw [F4Pilot.iform_eq_sum_mul_iform_single]
  simp only [iform_a2Root_single_check, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem iform_a2Root_self : iform a2Root a2Root = 2 := by
  rw [iform_a2Root]
  rfl

theorem corootPair_a2Root (v : Fin (Tag.rank .E7) → ℤ) :
    corootPair a2Root v = v 2 - v 0 := by
  rw [corootPair, iform_a2Root, iform_a2Root_self]
  omega

theorem isRoot_a2Root : IsRoot .E7 a2Root :=
  mem_rootFinset.1 (by decide +kernel)

theorem height_a2Root_pos : 0 < height a2Root := by decide

theorem a2Root_apply_zero : a2Root 0 = 1 := rfl

set_option maxRecDepth 100000 in
theorem not_mem_rootFinset_add_a2Root_check :
    ∀ α ∈ rootFinset .E7, α 0 = 0 → 0 < height α → α + a2Root ∉ rootFinset .E7 := by
  decide +kernel

theorem not_isRoot_add_a2Root {α : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (h0 : α 0 = 0) (hpos : 0 < height α) :
    ¬ IsRoot .E7 (α + a2Root) := fun h =>
  not_mem_rootFinset_add_a2Root_check α (mem_rootFinset.2 hα) h0 hpos (mem_rootFinset.2 h)

@[expose] def a2PerpNodes : Set (Fin (Tag.rank .E7)) := {j | j ≠ 0 ∧ j ≠ 2}

theorem eq_zero_or_eq_two_of_not_mem_a2PerpNodes {i : Fin (Tag.rank .E7)}
    (hi : i ∉ a2PerpNodes) : i = 0 ∨ i = 2 := by
  by_contra h
  exact hi ⟨fun h0 => h (Or.inl h0), fun h2 => h (Or.inr h2)⟩

theorem mem_parabolicRoots_a2PerpNodes {γ : Fin (Tag.rank .E7) → ℤ} :
    γ ∈ parabolicRoots .E7 a2PerpNodes ↔ IsRoot .E7 γ ∧ γ 0 = 0 ∧ γ 2 = 0 := by
  constructor
  · rintro ⟨hr, h⟩
    exact ⟨hr, h 0 fun h' => h'.1 rfl, h 2 fun h' => h'.2 rfl⟩
  · rintro ⟨hr, h0, h2⟩
    refine ⟨hr, fun i hi => ?_⟩
    rcases eq_zero_or_eq_two_of_not_mem_a2PerpNodes hi with rfl | rfl
    exacts [h0, h2]

theorem a2PerpNodes_subset_perpNodes : a2PerpNodes ⊆ perpNodes .E7 := fun _ h => h.1

theorem parabolicRoots_a2PerpNodes_subset_perpRoots :
    parabolicRoots .E7 a2PerpNodes ⊆ perpRoots .E7 := by
  rw [← parabolicRoots_perpNodes]
  exact fun γ hγ => ⟨hγ.1, fun i hi => hγ.2 i fun h' => hi (a2PerpNodes_subset_perpNodes h')⟩

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def a2SL2 : Subgroup (ModGL .E7 K) :=
  rootSubgroup .E7 K a2Root ⊔ rootSubgroup .E7 K (-a2Root)

theorem rootSpan_a2PerpNodes_le_centralizer_highRootSL2 :
    rootSpan .E7 K (parabolicRoots .E7 a2PerpNodes) ≤
      centralizer (highRootSL2 .E7 K : Set (ModGL .E7 K)) :=
  rootSpan_le_centralizer_rootPair_E7 (isRoot_highRoot _) fun α hα => by
    obtain ⟨hr, h0, -⟩ := mem_parabolicRoots_a2PerpNodes.1 hα
    refine ⟨hr, ?_⟩
    rw [iform_comm, iform_highRoot_E7, h0]

theorem rootSpan_a2PerpNodes_le_centralizer_a2SL2 :
    rootSpan .E7 K (parabolicRoots .E7 a2PerpNodes) ≤
      centralizer (a2SL2 K : Set (ModGL .E7 K)) :=
  rootSpan_le_centralizer_rootPair_E7 isRoot_a2Root fun α hα => by
    obtain ⟨hr, h0, h2⟩ := mem_parabolicRoots_a2PerpNodes.1 hα
    refine ⟨hr, ?_⟩
    rw [iform_comm, iform_a2Root, h0, h2]
    rfl

theorem parabolicLeviUnipotent_le_centralizer_pinnedX_a2Root (c : K) :
    parabolicLeviUnipotent .E7 K (perpNodes .E7) ≤
      centralizer ({pinnedX .E7 K a2Root c} : Set (ModGL .E7 K)) := by
  refine iSup₂_le fun α hα y hy => mem_centralizer_singleton_iff.2 ?_
  obtain ⟨⟨hαr, hα0⟩, -, hpos⟩ := hα
  have h0 : α 0 = 0 := hα0 0 zero_not_mem_perpNodes_E7
  have hne : α ≠ a2Root := by
    rintro rfl
    exact absurd h0 (by decide)
  have hne' : α ≠ -a2Root := by
    rintro rfl
    exact absurd h0 (by decide)
  exact ((simply_laced_root_commutator_unit .E7 (Or.inr (Or.inr (Or.inl rfl))) hαr
    isRoot_a2Root hne hne').2 (not_isRoot_add_a2Root hαr h0 hpos) K y hy _
    (mem_rootSubgroup.2 ⟨c, rfl⟩)).eq

theorem mem_parabolicWeylGroup_a2PerpNodes {w : WeylGroup .E7}
    (hw : w ∈ parabolicWeylGroup .E7 (perpNodes .E7)) (hβ : w • a2Root = a2Root) :
    w ∈ parabolicWeylGroup .E7 a2PerpNodes := by
  have hw' : ∀ v : Fin (Tag.rank .E7) → ℤ, ∀ i ∉ perpNodes .E7, (w • v) i = v i := by
    have h : w ∈ (parabolicWeylGroup .E7 (perpNodes .E7) : Set (WeylGroup .E7)) := hw
    rw [(parabolic_Weyl_coordinate_stabilizer .E7 (perpNodes .E7)).1] at h
    exact h
  have h0 : ∀ v : Fin (Tag.rank .E7) → ℤ, (w • v) 0 = v 0 := fun v =>
    hw' v 0 zero_not_mem_perpNodes_E7
  show w ∈ (parabolicWeylGroup .E7 a2PerpNodes : Set (WeylGroup .E7))
  rw [(parabolic_Weyl_coordinate_stabilizer .E7 a2PerpNodes).1]
  intro v i hi
  rcases eq_zero_or_eq_two_of_not_mem_a2PerpNodes hi with rfl | rfl
  · exact h0 v
  · have e1 := iform_a2Root (w • v)
    have e2 := iform_a2Root v
    rw [← hβ, iform_smul] at e1
    have e3 := h0 v
    omega

theorem mem_parabolicSubgroup_a2PerpNodes_of_commute (hK1 : ∀ u : Kˣ, u = 1)
    {g : ModGL .E7 K} (hgD : g ∈ rootSpan .E7 K (perpRoots .E7))
    (hgx : g * pinnedX .E7 K a2Root 1 = pinnedX .E7 K a2Root 1 * g) :
    g ∈ parabolicSubgroup .E7 K a2PerpNodes := by
  have hH := torusGroup_eq_bot_of_forall_units_eq_one (τ := .E7) hK1
  have hgC : g ∈ adjointGroup .E7 K := rootSpan_le_adjointGroup' _ hgD
  have hDM : rootSpan .E7 K (perpRoots .E7) ≤ parabolicLevi .E7 K (perpNodes .E7) := by
    rw [← parabolicRoots_perpNodes, ← subsystemGroup_eq_rootSpan]
    exact le_sup_right
  have hgM : g ∈ parabolicLevi .E7 K (perpNodes .E7) := hDM hgD
  have hgP : g ∈ parabolicSubgroup .E7 K (perpNodes .E7) :=
    parabolicLevi_le_parabolicSubgroup _ hgM
  have hcells := standard_parabolic_cells .E7 K
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell_of_mem_adjointGroup hgC
  have hwJ₁ : w ∈ parabolicWeylGroup .E7 (perpNodes .E7) := by
    have hg' : g ∈ (parabolicSubgroup .E7 K (perpNodes .E7) : Set (ModGL .E7 K)) := hgP
    rw [hcells.1] at hg'
    obtain ⟨v, hv, hgv⟩ := Set.mem_iUnion₂.1 hg'
    by_contra hne
    exact Set.disjoint_left.1 (hcells.2.1 w v fun h => hne (h ▸ hv)) hw hgv
  obtain ⟨b, hb, b', hb', hgbb⟩ := mem_bruhatCell.1 hw
  have hB := borelGroup_eq_mul_parabolic (τ := .E7) (K := K) (perpNodes .E7)
  have hb2 : b ∈ (parabolicRadical .E7 K (perpNodes .E7) : Set (ModGL .E7 K)) *
      ((torusGroup .E7 K : Set (ModGL .E7 K)) *
        (parabolicLeviUnipotent .E7 K (perpNodes .E7) : Set (ModGL .E7 K))) := by
    rw [← hB]
    exact hb
  have hb2' : b' ∈ (parabolicRadical .E7 K (perpNodes .E7) : Set (ModGL .E7 K)) *
      ((torusGroup .E7 K : Set (ModGL .E7 K)) *
        (parabolicLeviUnipotent .E7 K (perpNodes .E7) : Set (ModGL .E7 K))) := by
    rw [← hB]
    exact hb'
  obtain ⟨q₁, hq₁, _, ⟨h₁, hh₁, v₁, hv₁, rfl⟩, rfl⟩ := hb2
  obtain ⟨q₂, hq₂, _, ⟨h₂, hh₂, v₂, hv₂, rfl⟩, rfl⟩ := hb2'
  rw [SetLike.mem_coe, hH, mem_bot] at hh₁ hh₂
  subst hh₁ hh₂
  set n := canonicalRep (coxeterSystem .E7) K w with hn
  have hnM : n ∈ parabolicLevi .E7 K (perpNodes .E7) := canonicalRep_mem_parabolicLevi hwJ₁
  have hVM := parabolicLeviUnipotent_le_parabolicLevi (τ := .E7) (K := K) (perpNodes .E7)
  have hvn : v₁ * n ∈ parabolicLevi .E7 K (perpNodes .E7) := mul_mem (hVM hv₁) hnM
  have hm : v₁ * n * v₂ ∈ parabolicLevi .E7 K (perpNodes .E7) := mul_mem hvn (hVM hv₂)
  have hq : q₁ * (v₁ * n * q₂ * (v₁ * n)⁻¹) ∈ parabolicRadical .E7 K (perpNodes .E7) :=
    mul_mem hq₁ ((mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical _
      (parabolicLevi_le_parabolicSubgroup _ hvn)) q₂).1 hq₂)
  have hgeq : q₁ * (v₁ * n * q₂ * (v₁ * n)⁻¹) * (v₁ * n * v₂) = 1 * g := by
    rw [← hgbb]
    group
  have hgm : v₁ * n * v₂ = g := (eq_of_mul_eq_of_parabolic hq (one_mem _) hm hgM hgeq).2
  set x := pinnedX .E7 K a2Root 1 with hx
  have hc1 : v₁ * x = x * v₁ := mem_centralizer_singleton_iff.1
    (parabolicLeviUnipotent_le_centralizer_pinnedX_a2Root 1 hv₁)
  have hc2 : v₂ * x = x * v₂ := mem_centralizer_singleton_iff.1
    (parabolicLeviUnipotent_le_centralizer_pinnedX_a2Root 1 hv₂)
  have hkey : n * x = x * n := by
    have h1 : v₁ * (n * x) * v₂ = v₁ * (x * n) * v₂ := by
      calc v₁ * (n * x) * v₂ = v₁ * n * (x * v₂) := by group
        _ = v₁ * n * (v₂ * x) := by rw [hc2]
        _ = (v₁ * n * v₂) * x := by group
        _ = x * (v₁ * n * v₂) := by rw [hgm]; exact hgx
        _ = (x * v₁) * n * v₂ := by group
        _ = (v₁ * x) * n * v₂ := by rw [hc1]
        _ = v₁ * (x * n) * v₂ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w isRoot_a2Root
  have hnx : pinnedX .E7 K (w • a2Root) (ε * 1) = pinnedX .E7 K a2Root 1 := by
    rw [← hεc 1, ← hn, hkey, mul_inv_cancel_right]
  have hwβ : w • a2Root = a2Root :=
    F4Pilot.eq_of_pinnedX_eq_pinnedX (IsRoot.smul isRoot_a2Root w)
      ⟨isRoot_a2Root, height_a2Root_pos⟩
      (by rw [mul_one]; exact left_ne_zero_of_mul_eq_one hε) hnx
  have hwJ₂ := mem_parabolicWeylGroup_a2PerpNodes hwJ₁ hwβ
  have hmem : g ∈ (parabolicSubgroup .E7 K a2PerpNodes : Set (ModGL .E7 K)) := by
    rw [hcells.1]
    exact Set.mem_biUnion hwJ₂ hw
  exact hmem

@[expose] def a2RadicalRootsPerp : Set (Fin (Tag.rank .E7) → ℤ) :=
  {γ ∈ parabolicRadicalRoots .E7 a2PerpNodes | γ 0 = 0}

theorem parabolicRadicalRoots_a2PerpNodes_eq :
    parabolicRadicalRoots .E7 a2PerpNodes =
      parabolicRadicalRoots .E7 (perpNodes .E7) ∪ a2RadicalRootsPerp := by
  ext γ
  constructor
  · intro hγ
    by_cases h0 : γ 0 = 0
    · exact Or.inr ⟨hγ, h0⟩
    · refine Or.inl ⟨hγ.1, fun h => h0 ?_⟩
      exact h.1.2 0 zero_not_mem_perpNodes_E7
  · rintro (hγ | ⟨hγ, -⟩)
    · exact ⟨hγ.1, fun h => hγ.2 ⟨⟨h.1.1, fun i hi => h.1.2 i fun h' => hi
        (a2PerpNodes_subset_perpNodes h')⟩, h.2⟩⟩
    · exact hγ

theorem a2RadicalRootsPerp_subset_perpRoots : a2RadicalRootsPerp ⊆ perpRoots .E7 :=
  fun _ hγ => ⟨hγ.1.1.1, hγ.2⟩

theorem rootReflection_a2Root_isNeg {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : γ ∈ a2RadicalRootsPerp) :
    IsRoot .E7 (rootReflection a2Root • γ) ∧ height (rootReflection a2Root • γ) < 0 := by
  obtain ⟨⟨⟨hr, hpos⟩, hnot⟩, h0⟩ := hγ
  have hδ : rootReflection a2Root • γ = γ - (γ 2 - γ 0) • a2Root := by
    rw [rootReflection_smul isRoot_a2Root, corootPair_a2Root]
  have hδr : IsRoot .E7 (rootReflection a2Root • γ) := IsRoot.smul hr _
  have h2 : γ 2 ≠ 0 := fun h2 => hnot ⟨mem_parabolicRoots_a2PerpNodes.2 ⟨hr, h0, h2⟩, hr, hpos⟩
  have hnn := (IsRoot.height_pos_iff hr).1 hpos
  have hd0 : (rootReflection a2Root • γ) 0 = -γ 2 := by
    rw [hδ]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, a2Root_apply_zero, h0]
    ring
  refine ⟨hδr, ?_⟩
  rcases IsRoot.height_pos_or_neg hδr with hp | hn
  · exfalso
    have a := (IsRoot.height_pos_iff hδr).1 hp 0
    have b := hnn 2
    rw [hd0] at a
    omega
  · exact hn

theorem mem_rootSpan_a2PerpNodes_of_mem_parabolicSubgroup [CharP K 2] (hK1 : ∀ u : Kˣ, u = 1)
    {g : ModGL .E7 K} (hgD : g ∈ rootSpan .E7 K (perpRoots .E7))
    (hgP : g ∈ parabolicSubgroup .E7 K a2PerpNodes)
    (hgJ' : g ∈ centralizer (a2SL2 K : Set (ModGL .E7 K))) :
    g ∈ rootSpan .E7 K (parabolicRoots .E7 a2PerpNodes) := by
  have hH := torusGroup_eq_bot_of_forall_units_eq_one (τ := .E7) hK1
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := parabolic_root_radical_Levi_factors .E7 K a2PerpNodes
  obtain ⟨⟨q, m⟩, ⟨hq, hm, rfl⟩, -⟩ := huniq g hgP
  have hm' : m ∈ rootSpan .E7 K (parabolicRoots .E7 a2PerpNodes) := by
    have := F4Pilot.parabolicLevi_le_torusGroup_sup (τ := .E7) (K := K) a2PerpNodes hm
    rwa [hH, bot_sup_eq] at this
  have hmD : m ∈ rootSpan .E7 K (perpRoots .E7) :=
    rootSpan_mono parabolicRoots_a2PerpNodes_subset_perpRoots hm'
  have hqD : q ∈ rootSpan .E7 K (perpRoots .E7) := by
    have := mul_mem hgD (inv_mem hmD)
    rwa [mul_inv_cancel_right] at this
  have hqJ' : q ∈ centralizer (a2SL2 K : Set (ModGL .E7 K)) := by
    have := mul_mem hgJ' (inv_mem (rootSpan_a2PerpNodes_le_centralizer_a2SL2 hm'))
    rwa [mul_inv_cancel_right] at this
  suffices hq1 : q = 1 by
    rw [hq1, one_mul]
    exact hm'
  have hqR : q ∈ rootSpan .E7 K a2RadicalRootsPerp := by
    have hq' : q ∈ rootSpan .E7 K (parabolicRadicalRoots .E7 (perpNodes .E7) ∪
        a2RadicalRootsPerp) := by
      rw [← parabolicRadicalRoots_a2PerpNodes_eq]
      exact hq
    have hS₁ : ∀ α ∈ parabolicRadicalRoots .E7 (perpNodes .E7), IsRoot .E7 α ∧ 0 < height α :=
      fun α hα => hα.1
    have hS₂ : ∀ α ∈ a2RadicalRootsPerp, IsRoot .E7 α ∧ 0 < height α := fun α hα => hα.1.1
    have hdisj : Disjoint (parabolicRadicalRoots .E7 (perpNodes .E7)) a2RadicalRootsPerp := by
      rw [Set.disjoint_left]
      rintro γ hγ ⟨-, h0⟩
      exact hγ.2 ⟨⟨hγ.1.1, fun i hi => by
        have : i = 0 := by
          by_contra h
          exact hi h
        rw [this, h0]⟩, hγ.1⟩
    have hclosed : ∀ α ∈ parabolicRadicalRoots .E7 (perpNodes .E7) ∪ a2RadicalRootsPerp,
        ∀ β ∈ parabolicRadicalRoots .E7 (perpNodes .E7) ∪ a2RadicalRootsPerp, ∀ a b : ℕ,
        1 ≤ a → 1 ≤ b → IsRoot .E7 (a • α + b • β) →
          a • α + b • β ∈ parabolicRadicalRoots .E7 (perpNodes .E7) ∪ a2RadicalRootsPerp := by
      rw [← parabolicRadicalRoots_a2PerpNodes_eq]
      exact fun α hα β hβ a b ha hb h => add_mem_parabolicRadicalRoots hα.1 hβ ha hb h
    obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ :=
      exists_mul_rootSpan_eq K hS₁ hS₂ hdisj hclosed hq'
    have hu₂D : u₂ ∈ rootSpan .E7 K (perpRoots .E7) :=
      rootSpan_mono a2RadicalRootsPerp_subset_perpRoots hu₂
    have hu₁D : u₁ ∈ rootSpan .E7 K (perpRoots .E7) := by
      have := mul_mem hqD (inv_mem hu₂D)
      rwa [← hu, mul_inv_cancel_right] at this
    have hu₁1 : u₁ = 1 := by
      have h : u₁ ∈ parabolicRadical .E7 K (perpNodes .E7) ⊓ rootSpan .E7 K (perpRoots .E7) :=
        mem_inf.2 ⟨hu₁, hu₁D⟩
      rwa [parabolicRadical_perpNodes_inf_rootSpan_perpRoots, mem_bot] at h
    rw [← hu, hu₁1, one_mul]
    exact hu₂
  obtain ⟨-, hrange, -, -, hn, -⟩ := even_Chevalley_pinned_root_SL2_maps .E7 K isRoot_a2Root
  obtain ⟨-, -, hnmon, hnw⟩ := hn 1
  have hnJ : rootWeylSL2 .E7 K a2Root 1 ∈ a2SL2 K := by
    rw [a2SL2, ← hrange]
    exact ⟨_, rfl⟩
  have hqn : rootWeylSL2 .E7 K a2Root 1 * q * (rootWeylSL2 .E7 K a2Root 1)⁻¹ = q := by
    rw [mem_centralizer_iff.1 hqJ' _ hnJ, mul_inv_cancel_right]
  have hneg : q ∈ negUnipotent .E7 K := by
    have hmem : rootWeylSL2 .E7 K a2Root 1 * q * (rootWeylSL2 .E7 K a2Root 1)⁻¹ ∈
        (rootSpan .E7 K a2RadicalRootsPerp).map
          (MulAut.conj (rootWeylSL2 .E7 K a2Root 1)).toMonoidHom := ⟨q, hqR, rfl⟩
    rw [map_conj_rootSpan_of_mem_monomialSubgroup hnmon (fun α hα => hα.1.1.1), hnw, hqn] at hmem
    refine rootSpan_le_negUnipotent ?_ hmem
    rintro _ ⟨γ, hγ, rfl⟩
    exact rootReflection_a2Root_isNeg hγ
  have h := mem_inf.2 ⟨rootSpan_le_posUnipotent (fun α hα => hα.1.1) hqR, hneg⟩
  rwa [CFSG.LieType.Chevalley.posUnipotent_inf_negUnipotent, mem_bot] at h

theorem adjointGroup_inf_centralizer_highRootSL2_inf_centralizer_a2SL2 [CharP K 2]
    (hK1 : ∀ u : Kˣ, u = 1) :
    adjointGroup .E7 K ⊓ centralizer (highRootSL2 .E7 K : Set (ModGL .E7 K)) ⊓
        centralizer (a2SL2 K : Set (ModGL .E7 K)) =
      rootSpan .E7 K (parabolicRoots .E7 a2PerpNodes) := by
  refine le_antisymm (fun g hg => ?_) (le_inf (le_inf (rootSpan_le_adjointGroup' _)
    rootSpan_a2PerpNodes_le_centralizer_highRootSL2) rootSpan_a2PerpNodes_le_centralizer_a2SL2)
  obtain ⟨hg1, hgJ'⟩ := mem_inf.1 hg
  obtain ⟨hgC, hgJ⟩ := mem_inf.1 hg1
  have hgD : g ∈ rootSpan .E7 K (perpRoots .E7) := by
    rw [← adjointGroup_inf_centralizer_highRootSL2_eq_of_charTwo (Or.inr (Or.inl rfl))]
    exact mem_inf.2 ⟨hgC, hgJ⟩
  have hx : pinnedX .E7 K a2Root 1 ∈ a2SL2 K :=
    mem_sup_left (mem_rootSubgroup.2 ⟨1, rfl⟩)
  have hgP := mem_parabolicSubgroup_a2PerpNodes_of_commute hK1 hgD
    (mem_centralizer_iff.1 hgJ' _ hx).symm
  exact mem_rootSpan_a2PerpNodes_of_mem_parabolicSubgroup hK1 hgD hgP hgJ'

end CFSG.SeitzReduction.E7Pilot
