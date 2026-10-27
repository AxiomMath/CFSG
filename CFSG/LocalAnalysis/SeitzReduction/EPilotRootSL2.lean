module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Levi

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

section Full


theorem highTorusLine_le_normalizer_perpLevi :
    highTorusLine τ K ≤ normalizer (rootSpan τ K (perpRoots τ) : Set (ModGL τ K)) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [(commute_of_mem_highTorusLine_of_mem_rootSpan ht hy).eq, mul_inv_cancel_right]
    exact hy
  · have hz := (commute_of_mem_highTorusLine_of_mem_rootSpan (inv_mem ht) hy).eq
    have e : y = t * y * t⁻¹ := by
      calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
        _ = (t * y * t⁻¹) * t⁻¹ * t := by rw [hz]
        _ = t * y * t⁻¹ := by group
    rw [e]
    exact hy

theorem centralizer_highRootSL2_eq [Finite K] [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hq : 4 ≤ Nat.card K) :
    adjointGroup τ K ⊓ centralizer (highRootSL2 τ K : Set (ModGL τ K)) =
      rootSpan τ K (perpRoots τ) := by
  have hK : ringChar K = 2 := ringChar.eq K 2
  refine le_antisymm (fun g hg => ?_)
    (le_inf (rootSpan_le_adjointGroup' _) (rootSpan_perpRoots_le_centralizer_highRootSL2 hτ))
  obtain ⟨hgC, hgJ⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  have hd := rootDiagUnit_highDiag_mem_highRootSL2 (K := K) hτ c
  have hgd : g ∈ toralCentralizer τ K (highDiag τ c) := by
    refine mem_toralCentralizer.2 ⟨hgC, ?_⟩
    rw [Subgroup.mem_centralizer_iff.1 hgJ _ hd, mul_inv_cancel_right]
  rw [(toralCentralizer_highDiag_eq_sup hτ hK hc).1, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ highTorusLine_le_normalizer_perpLevi] at hgd
  obtain ⟨t, ht, x, hx, rfl⟩ := Set.mem_mul.1 hgd
  have hxJ := rootSpan_perpRoots_le_centralizer_highRootSL2 hτ hx
  have htJ : t ∈ centralizer (highRootSL2 τ K : Set (ModGL τ K)) := by
    have := mul_mem hgJ (inv_mem hxJ)
    rwa [mul_inv_cancel_right] at this
  obtain ⟨l, rfl⟩ := mem_highTorusLine.1 ht
  have hcomm : Commute (rootDiagUnit τ (highDiag τ l)) (pinnedX τ K (highRoot τ) 1) :=
    (Subgroup.mem_centralizer_iff.1 htJ _
      (rootSubgroup_highRoot_le_highRootSL2 (Subgroup.subset_closure ⟨1, rfl⟩))).symm
  rw [eq_one_of_commute_pinnedX_highRoot hτ hK hcomm, highDiag_one, rootDiagUnit_one, one_mul]
  exact hx

theorem centralizer_highRootSL2_subgroupOf [Finite K] [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : 4 ≤ Nat.card K) :
    centralizer ((highRootSL2 τ K).subgroupOf (adjointGroup τ K) : Set (adjointGroup τ K)) =
      (rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K) := by
  ext g
  rw [Subgroup.mem_subgroupOf, ← centralizer_highRootSL2_eq hτ hq, Subgroup.mem_inf]
  refine ⟨fun h => ⟨g.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩,
    fun h => Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  · have := Subgroup.mem_centralizer_iff.1 h ⟨y, highRootSL2_le_adjointGroup hy⟩
      (Subgroup.mem_subgroupOf.2 hy)
    exact congrArg Subtype.val this
  · exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h.2 y (Subgroup.mem_subgroupOf.1 hy))

theorem centralizer_perpLevi_subgroupOf [Finite K] [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : 4 ≤ Nat.card K) :
    centralizer ((rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K) :
        Set (adjointGroup τ K)) =
      (highRootSL2 τ K).subgroupOf (adjointGroup τ K) := by
  ext g
  rw [Subgroup.mem_subgroupOf, ← centralizer_perpLevi_eq hτ hq, Subgroup.mem_inf]
  refine ⟨fun h => ⟨g.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩,
    fun h => Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  · have := Subgroup.mem_centralizer_iff.1 h ⟨y, rootSpan_le_adjointGroup' _ hy⟩
      (Subgroup.mem_subgroupOf.2 hy)
    exact congrArg Subtype.val this
  · exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h.2 y (Subgroup.mem_subgroupOf.1 hy))

end Full

end CFSG.SeitzReduction.EPilot
