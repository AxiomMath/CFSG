module

public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
public import CFSG.LieType.Chevalley.SingleEdgePerfect

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped commutatorElement

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem xUnit_mem_graphFixedPosUnipotent
    {j : Fin t.tag.rank} (hj : t.perm j = j) {c : K}
    (hc : σ c = c) : xUnit t.tag K j c ∈ graphFixedPosUnipotent t K σ := by
  refine Subgroup.mem_inf.2 ⟨?_, xUnit_mem_adjointGroup j c, ?_⟩
  · rw [← pinnedX_single]
    exact le_iSup₂_of_le (f := fun α (_ : IsRoot t.tag α ∧ 0 < height α) => rootSubgroup t.tag K α)
      (Pi.single j 1) ⟨isRoot_single _ j, by rw [height_single]; exact one_pos⟩ le_rfl
      (Subgroup.subset_closure ⟨c, rfl⟩)
  · change twistHom t K σ (xUnit t.tag K j c) = xUnit t.tag K j c
    rw [twistHom_xUnit, hj, hc]

theorem yUnit_mem_graphFixedNegUnipotent
    {j : Fin t.tag.rank} (hj : t.perm j = j) {c : K}
    (hc : σ c = c) : yUnit t.tag K j c ∈ graphFixedNegUnipotent t K σ := by
  refine Subgroup.mem_inf.2 ⟨?_, yUnit_mem_adjointGroup j c, ?_⟩
  · rw [← pinnedX_neg_single]
    exact le_iSup₂_of_le (f := fun α (_ : IsRoot t.tag α ∧ height α < 0) => rootSubgroup t.tag K α)
      (-Pi.single j 1) ⟨isRoot_neg_single _ j, by rw [height_neg, height_single]; omega⟩ le_rfl
      (Subgroup.subset_closure ⟨c, rfl⟩)
  · change twistHom t K σ (yUnit t.tag K j c) = yUnit t.tag K j c
    rw [twistHom_yUnit, hj, hc]

theorem weylElt_mem_graphFixedRootGroup
    {j : Fin t.tag.rank} (hj : t.perm j = j) :
    weylElt t.tag K j 1 ∈ graphFixedRootGroup t K σ := by
  have hx := graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
    (xUnit_mem_graphFixedPosUnipotent (σ := σ) hj (map_one σ))
  have hy := graphFixedNegUnipotent_le_graphFixedRootGroup t K σ
    (yUnit_mem_graphFixedNegUnipotent (σ := σ) hj (by rw [map_neg, map_one]))
  rw [weylElt_eq_xUnit_mul, Units.val_one, inv_one, Units.val_one]
  exact mul_mem (mul_mem hx hy) hx

theorem conj_mem_commutator_self {G : Type*} [Group G] {H : Subgroup G} {g x : G} (hg : g ∈ H)
    (hx : x ∈ ⁅H, H⁆) : g * x * g⁻¹ ∈ ⁅H, H⁆ := by
  rw [← Subgroup.map_subtype_commutator] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, mem_commutator_of_eq_conj hy rfl, rfl⟩

theorem E6_fixed_singletons_derived
    (K : Type) [Field K] (σ : K →+* K)
    (i : Fin TwistTag.E6.tag.rank) (hi : i.val = 1 ∨ i.val = 3) (c : K) (hc : σ c = c) :
    xUnit TwistTag.E6.tag K i c ∈
        ⁅graphFixedRootGroup .E6 K σ, graphFixedRootGroup .E6 K σ⁆ ∧
      yUnit TwistTag.E6.tag K i c ∈
        ⁅graphFixedRootGroup .E6 K σ, graphFixedRootGroup .E6 K σ⁆ := by
  obtain ⟨l, hl, hli, hil, hρi⟩ : ∃ l : Fin TwistTag.E6.tag.rank, TwistTag.E6.perm l = l ∧
      TwistTag.E6.tag.cartan l i = -1 ∧ TwistTag.E6.tag.cartan i l = -1 ∧
      TwistTag.E6.perm i = i := by
    rcases hi with h | h
    · obtain rfl : i = ⟨1, by decide⟩ := Fin.ext h
      exact ⟨⟨3, by decide⟩, rfl, rfl, rfl, rfl⟩
    · obtain rfl : i = ⟨3, by decide⟩ := Fin.ext h
      exact ⟨⟨1, by decide⟩, rfl, rfl, rfl, rfl⟩
  have hn := weylElt_mem_graphFixedRootGroup (K := K) (σ := σ) hl
  have hx : ∀ d : K, σ d = d → xUnit TwistTag.E6.tag K i d ∈
      ⁅graphFixedRootGroup .E6 K σ, graphFixedRootGroup .E6 K σ⁆ := fun d hd => by
    have hcomm := Subgroup.commutator_mem_commutator
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
        (xUnit_mem_graphFixedPosUnipotent (σ := σ) hl (map_one σ)))
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
        (xUnit_mem_graphFixedPosUnipotent (σ := σ) hρi hd))
    rw [(a2_simple_root_commutatorElement K hli hil 1 d).1, one_mul] at hcomm
    have h := conj_mem_commutator_self (inv_mem hn) hcomm
    rwa [show (weylElt TwistTag.E6.tag K l 1)⁻¹ * (weylElt TwistTag.E6.tag K l 1 *
        xUnit TwistTag.E6.tag K i d * (weylElt TwistTag.E6.tag K l 1)⁻¹) *
          (weylElt TwistTag.E6.tag K l 1)⁻¹⁻¹ = xUnit TwistTag.E6.tag K i d by group] at h
  refine ⟨hx c hc, ?_⟩
  have h := conj_mem_commutator_self (weylElt_mem_graphFixedRootGroup (K := K) (σ := σ) hρi)
    (hx (-c) (by rw [map_neg, hc]))
  rwa [weylElt_mul_xUnit_mul_inv, neg_neg] at h

end CFSG.LieType.Chevalley
