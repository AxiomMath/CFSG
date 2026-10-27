module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2OverlapRoots

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction.EPilot CFSG.RankThree.Chevalley
open scoped Pointwise

local instance e7PilotQ2OverlapCentNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩


variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def d6HighRootSL2 : Subgroup (ModGL .E7 K) :=
  rootSubgroup .E7 K d6HighRoot ⊔ rootSubgroup .E7 K (-d6HighRoot)

theorem rootSpan_le_centralizer_rootPair_E7 {S : Set (Fin (Tag.rank .E7) → ℤ)}
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (hS : ∀ α ∈ S, IsRoot .E7 α ∧ iform α β = 0) :
    rootSpan .E7 K S ≤ centralizer ((rootSubgroup .E7 K β ⊔ rootSubgroup .E7 K (-β) :
      Subgroup (ModGL .E7 K)) : Set (ModGL .E7 K)) := by
  rw [le_centralizer_iff]
  refine sup_le ?_ ?_ <;> rw [le_centralizer_iff] <;>
    refine iSup₂_le fun α hα x hx => mem_centralizer_iff.2 fun y hy => ?_
  · exact (commute_of_iform_eq_zero (Or.inr (Or.inl rfl)) (hS α hα).1 hβ (hS α hα).2 hx hy).symm.eq
  · refine (commute_of_iform_eq_zero (Or.inr (Or.inl rfl)) (hS α hα).1 (IsRoot.neg hβ) ?_ hx
      hy).symm.eq
    rw [iform_neg_right_E7, (hS α hα).2, neg_zero]

theorem rootSpan_overlapNodes_le_centralizer_highRootSL2 :
    rootSpan .E7 K (parabolicRoots .E7 overlapNodes) ≤
      centralizer (highRootSL2 .E7 K : Set (ModGL .E7 K)) :=
  rootSpan_le_centralizer_rootPair_E7 (isRoot_highRoot _) fun α hα =>
    ⟨hα.1, by rw [iform_comm]; exact iform_highRoot_of_mem_parabolicRoots_overlapNodes hα⟩

theorem rootSpan_overlapNodes_le_centralizer_d6HighRootSL2 :
    rootSpan .E7 K (parabolicRoots .E7 overlapNodes) ≤
      centralizer (d6HighRootSL2 K : Set (ModGL .E7 K)) :=
  rootSpan_le_centralizer_rootPair_E7 isRoot_d6HighRoot fun α hα =>
    ⟨hα.1, by rw [iform_comm]; exact iform_d6HighRoot_of_mem_parabolicRoots_overlapNodes hα⟩

theorem zero_not_mem_perpNodes_E7 : (0 : Fin (Tag.rank .E7)) ∉ perpNodes .E7 := fun h => h rfl

theorem parabolicLeviUnipotent_le_centralizer_pinnedX_d6HighRoot (c : K) :
    parabolicLeviUnipotent .E7 K (perpNodes .E7) ≤
      centralizer ({pinnedX .E7 K d6HighRoot c} : Set (ModGL .E7 K)) := by
  refine iSup₂_le fun α hα y hy => mem_centralizer_singleton_iff.2 ?_
  obtain ⟨⟨hαr, hα0⟩, -, hpos⟩ := hα
  by_cases heq : α = d6HighRoot
  · subst heq
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · have hne' : α ≠ -d6HighRoot := by
      rintro rfl
      have : height (-d6HighRoot) < 0 := by decide
      omega
    exact ((simply_laced_root_commutator_unit .E7 (Or.inr (Or.inr (Or.inl rfl))) hαr
      isRoot_d6HighRoot heq hne').2
      (not_isRoot_add_d6HighRoot hαr (hα0 0 zero_not_mem_perpNodes_E7) hpos) K y hy _
      (mem_rootSubgroup.2 ⟨c, rfl⟩)).eq

theorem mem_parabolicWeylGroup_overlapNodes {w : WeylGroup .E7}
    (hw : w ∈ parabolicWeylGroup .E7 (perpNodes .E7)) (hθ' : w • d6HighRoot = d6HighRoot) :
    w ∈ parabolicWeylGroup .E7 overlapNodes := by
  have hw' : ∀ v : Fin (Tag.rank .E7) → ℤ, ∀ i ∉ perpNodes .E7, (w • v) i = v i := by
    have h : w ∈ (parabolicWeylGroup .E7 (perpNodes .E7) : Set (WeylGroup .E7)) := hw
    rw [(parabolic_Weyl_coordinate_stabilizer .E7 (perpNodes .E7)).1] at h
    exact h
  have h0 : ∀ v : Fin (Tag.rank .E7) → ℤ, (w • v) 0 = v 0 := fun v =>
    hw' v 0 zero_not_mem_perpNodes_E7
  show w ∈ (parabolicWeylGroup .E7 overlapNodes : Set (WeylGroup .E7))
  rw [(parabolic_Weyl_coordinate_stabilizer .E7 overlapNodes).1]
  intro v i hi
  rcases eq_zero_or_eq_five_of_not_mem_overlapNodes hi with rfl | rfl
  · exact h0 v
  · have e1 := iform_d6HighRoot (w • v)
    have e2 := iform_d6HighRoot v
    rw [← hθ', iform_smul] at e1
    have e3 := h0 v
    omega

theorem mem_parabolicSubgroup_overlapNodes_of_commute (hK1 : ∀ u : Kˣ, u = 1)
    {g : ModGL .E7 K} (hgD : g ∈ rootSpan .E7 K (perpRoots .E7))
    (hgx : g * pinnedX .E7 K d6HighRoot 1 = pinnedX .E7 K d6HighRoot 1 * g) :
    g ∈ parabolicSubgroup .E7 K overlapNodes := by
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
  set x := pinnedX .E7 K d6HighRoot 1 with hx
  have hc1 : v₁ * x = x * v₁ := mem_centralizer_singleton_iff.1
    (parabolicLeviUnipotent_le_centralizer_pinnedX_d6HighRoot 1 hv₁)
  have hc2 : v₂ * x = x * v₂ := mem_centralizer_singleton_iff.1
    (parabolicLeviUnipotent_le_centralizer_pinnedX_d6HighRoot 1 hv₂)
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
  obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w isRoot_d6HighRoot
  have hnx : pinnedX .E7 K (w • d6HighRoot) (ε * 1) = pinnedX .E7 K d6HighRoot 1 := by
    rw [← hεc 1, ← hn, hkey, mul_inv_cancel_right]
  have hwθ' : w • d6HighRoot = d6HighRoot :=
    F4Pilot.eq_of_pinnedX_eq_pinnedX (IsRoot.smul isRoot_d6HighRoot w)
      ⟨isRoot_d6HighRoot, height_d6HighRoot_pos⟩
      (by rw [mul_one]; exact left_ne_zero_of_mul_eq_one hε) hnx
  have hwJ₂ := mem_parabolicWeylGroup_overlapNodes hwJ₁ hwθ'
  have hmem : g ∈ (parabolicSubgroup .E7 K overlapNodes : Set (ModGL .E7 K)) := by
    rw [hcells.1]
    exact Set.mem_biUnion hwJ₂ hw
  exact hmem

theorem highRoot_E7_apply_zero : highRoot .E7 0 = 2 := rfl

theorem highRoot_E7_apply_five : highRoot .E7 5 = 2 := rfl

theorem d6HighRoot_apply_zero : d6HighRoot 0 = 0 := rfl

theorem d6HighRoot_apply_five : d6HighRoot 5 = 2 := rfl

theorem rootReflection_highRoot_d6HighRoot_isNeg {β : Fin (Tag.rank .E7) → ℤ}
    (hβ : β ∈ parabolicRadicalRoots .E7 overlapNodes) :
    IsRoot .E7 (rootReflection (highRoot .E7) • (rootReflection d6HighRoot • β)) ∧
      height (rootReflection (highRoot .E7) • (rootReflection d6HighRoot • β)) < 0 := by
  obtain ⟨⟨hr, hpos⟩, hnot⟩ := hβ
  have hγ : rootReflection d6HighRoot • β = β - (β 5 - β 0) • d6HighRoot := by
    rw [rootReflection_smul isRoot_d6HighRoot, corootPair_d6HighRoot]
  have hγr : IsRoot .E7 (rootReflection d6HighRoot • β) := IsRoot.smul hr _
  have hδ : rootReflection (highRoot .E7) • (rootReflection d6HighRoot • β) =
      rootReflection d6HighRoot • β - (rootReflection d6HighRoot • β) 0 • highRoot .E7 := by
    rw [rootReflection_smul (isRoot_highRoot _), EPilot.corootPair_highRoot (Or.inr (Or.inl rfl))]
    rfl
  have hδr : IsRoot .E7 (rootReflection (highRoot .E7) • (rootReflection d6HighRoot • β)) :=
    IsRoot.smul hγr _
  have h0 : (rootReflection (highRoot .E7) • (rootReflection d6HighRoot • β)) 0 = -β 0 := by
    rw [hδ, hγ]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, d6HighRoot_apply_zero,
      highRoot_E7_apply_zero]
    ring
  have h5 : (rootReflection (highRoot .E7) • (rootReflection d6HighRoot • β)) 5 = -β 5 := by
    rw [hδ, hγ]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, d6HighRoot_apply_zero,
      d6HighRoot_apply_five, highRoot_E7_apply_five]
    ring
  have hnn := (IsRoot.height_pos_iff hr).1 hpos
  have hne : β 0 ≠ 0 ∨ β 5 ≠ 0 := by
    by_contra hc
    have hc0 : β 0 = 0 := by
      by_contra h
      exact hc (Or.inl h)
    have hc5 : β 5 = 0 := by
      by_contra h
      exact hc (Or.inr h)
    exact hnot ⟨mem_parabolicRoots_overlapNodes.2 ⟨hr, hc0, hc5⟩, hr, hpos⟩
  refine ⟨hδr, ?_⟩
  rcases IsRoot.height_pos_or_neg hδr with hp | hn
  · exfalso
    have hall := (IsRoot.height_pos_iff hδr).1 hp
    have a := hall 0
    have b := hall 5
    rw [h0] at a
    rw [h5] at b
    have c := hnn 0
    have d := hnn 5
    omega
  · exact hn

theorem mem_rootSpan_overlapNodes_of_mem_parabolicSubgroup [CharP K 2] (hK1 : ∀ u : Kˣ, u = 1)
    {g : ModGL .E7 K} (hgP : g ∈ parabolicSubgroup .E7 K overlapNodes)
    (hgJ : g ∈ centralizer (highRootSL2 .E7 K : Set (ModGL .E7 K)))
    (hgJ' : g ∈ centralizer (d6HighRootSL2 K : Set (ModGL .E7 K))) :
    g ∈ rootSpan .E7 K (parabolicRoots .E7 overlapNodes) := by
  have hH := torusGroup_eq_bot_of_forall_units_eq_one (τ := .E7) hK1
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := parabolic_root_radical_Levi_factors .E7 K overlapNodes
  obtain ⟨⟨q, m⟩, ⟨hq, hm, rfl⟩, -⟩ := huniq g hgP
  have hm' : m ∈ rootSpan .E7 K (parabolicRoots .E7 overlapNodes) := by
    have := F4Pilot.parabolicLevi_le_torusGroup_sup (τ := .E7) (K := K) overlapNodes hm
    rwa [hH, bot_sup_eq] at this
  have hqJ : q ∈ centralizer (highRootSL2 .E7 K : Set (ModGL .E7 K)) := by
    have := mul_mem hgJ (inv_mem (rootSpan_overlapNodes_le_centralizer_highRootSL2 hm'))
    rwa [mul_inv_cancel_right] at this
  have hqJ' : q ∈ centralizer (d6HighRootSL2 K : Set (ModGL .E7 K)) := by
    have := mul_mem hgJ' (inv_mem (rootSpan_overlapNodes_le_centralizer_d6HighRootSL2 hm'))
    rwa [mul_inv_cancel_right] at this
  suffices hq1 : q = 1 by
    rw [hq1, one_mul]
    exact hm'
  obtain ⟨-, -, -, -, hn₁, -⟩ := even_Chevalley_pinned_root_SL2_maps .E7 K (isRoot_highRoot .E7)
  obtain ⟨-, -, hn₁mon, hn₁w⟩ := hn₁ 1
  obtain ⟨-, hrange₂, -, -, hn₂, -⟩ := even_Chevalley_pinned_root_SL2_maps .E7 K isRoot_d6HighRoot
  obtain ⟨-, -, hn₂mon, hn₂w⟩ := hn₂ 1
  have hn₁J : rootWeylSL2 .E7 K (highRoot .E7) 1 ∈ highRootSL2 .E7 K :=
    E6Pilot.rootSL2_highRoot_mem_highRootSL2 _
  have hn₂J : rootWeylSL2 .E7 K d6HighRoot 1 ∈ d6HighRootSL2 K := by
    rw [d6HighRootSL2, ← hrange₂]
    exact ⟨_, rfl⟩
  have hq₁ : rootWeylSL2 .E7 K (highRoot .E7) 1 * q *
      (rootWeylSL2 .E7 K (highRoot .E7) 1)⁻¹ = q := by
    rw [mem_centralizer_iff.1 hqJ _ hn₁J, mul_inv_cancel_right]
  have hq₂ : rootWeylSL2 .E7 K d6HighRoot 1 * q * (rootWeylSL2 .E7 K d6HighRoot 1)⁻¹ = q := by
    rw [mem_centralizer_iff.1 hqJ' _ hn₂J, mul_inv_cancel_right]
  have hneg : q ∈ negUnipotent .E7 K := by
    have hmem : rootWeylSL2 .E7 K (highRoot .E7) 1 * (rootWeylSL2 .E7 K d6HighRoot 1 * q *
        (rootWeylSL2 .E7 K d6HighRoot 1)⁻¹) * (rootWeylSL2 .E7 K (highRoot .E7) 1)⁻¹ ∈
        ((parabolicRadical .E7 K overlapNodes).map
          (MulAut.conj (rootWeylSL2 .E7 K d6HighRoot 1)).toMonoidHom).map
          (MulAut.conj (rootWeylSL2 .E7 K (highRoot .E7) 1)).toMonoidHom :=
      ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    rw [parabolicRadical, map_conj_rootSpan_of_mem_monomialSubgroup hn₂mon (fun α hα => hα.1.1),
      map_conj_rootSpan_of_mem_monomialSubgroup hn₁mon (by
        rintro _ ⟨β, hβ, rfl⟩
        exact IsRoot.smul hβ.1.1 _), hn₁w, hn₂w, hq₂, hq₁] at hmem
    refine rootSpan_le_negUnipotent ?_ hmem
    rintro _ ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
    exact rootReflection_highRoot_d6HighRoot_isNeg hβ
  have h := mem_inf.2 ⟨parabolicRadical_le_posUnipotent _ hq, hneg⟩
  rwa [CFSG.LieType.Chevalley.posUnipotent_inf_negUnipotent, mem_bot] at h

theorem adjointGroup_inf_centralizer_highRootSL2_inf_centralizer_d6HighRootSL2 [CharP K 2]
    (hK1 : ∀ u : Kˣ, u = 1) :
    adjointGroup .E7 K ⊓ centralizer (highRootSL2 .E7 K : Set (ModGL .E7 K)) ⊓
        centralizer (d6HighRootSL2 K : Set (ModGL .E7 K)) =
      rootSpan .E7 K (parabolicRoots .E7 overlapNodes) := by
  refine le_antisymm (fun g hg => ?_) (le_inf (le_inf (rootSpan_le_adjointGroup' _)
    rootSpan_overlapNodes_le_centralizer_highRootSL2)
      rootSpan_overlapNodes_le_centralizer_d6HighRootSL2)
  obtain ⟨hg1, hgJ'⟩ := mem_inf.1 hg
  obtain ⟨hgC, hgJ⟩ := mem_inf.1 hg1
  have hgD : g ∈ rootSpan .E7 K (perpRoots .E7) := by
    rw [← adjointGroup_inf_centralizer_highRootSL2_eq_of_charTwo (Or.inr (Or.inl rfl))]
    exact mem_inf.2 ⟨hgC, hgJ⟩
  have hx : pinnedX .E7 K d6HighRoot 1 ∈ d6HighRootSL2 K :=
    mem_sup_left (mem_rootSubgroup.2 ⟨1, rfl⟩)
  have hgP := mem_parabolicSubgroup_overlapNodes_of_commute hK1 hgD
    (mem_centralizer_iff.1 hgJ' _ hx).symm
  exact mem_rootSpan_overlapNodes_of_mem_parabolicSubgroup hK1 hgP hgJ hgJ'

end CFSG.SeitzReduction.E7Pilot
