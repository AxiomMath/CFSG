module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowBlock

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification
open CFSG.OddStandard.SmallF3.HypA2 (TypU isSLTwoOver_of_mulEquiv)

theorem a2lDatum_of_subgroup_component {G : Type} [Group G] (H : Subgroup G) [Finite H] {z : G}
    (hzH : z ∈ H) (hz : z * z = 1) (hz1 : z ≠ 1) {Q : Subgroup G} {q₀ : ℕ} (hodd : Odd q₀)
    (h5 : 5 ≤ q₀) (hQc : CFSG.Assembly.IsComponentOf Q (H ⊓ centralizer ({z} : Set G)))
    (hzQ : z ∈ Q) (hN : HarrisLit.IsSLTwoOver q₀ ↥Q) (hTU : TypU ↥Q) : a2lDatum ↥H := by
  obtain ⟨hQle, hQs, hQq⟩ := hQc
  have hQH : Q ≤ H := hQle.trans inf_le_left
  let t : H := ⟨z, hzH⟩
  let eJ : ↥(Q.subgroupOf H) ≃* ↥Q := subgroupOfEquivOfLe hQH
  have hcent : (H ⊓ centralizer ({z} : Set G)).subgroupOf H = centralizer ({t} : Set H) := by
    ext g
    rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h.2, fun h => ⟨g.2, congrArg Subtype.val h⟩⟩
  have hsub : CFSG.Assembly.IsSubnormal (Q.subgroupOf H) (centralizer ({t} : Set H)) := by
    rw [← hcent]
    exact hQs.comap H.subtype
  refine a2lDatum_of_block (P := H) (MonoidHom.id H) Function.surjective_id ?_ hodd h5 (t := t)
    (J := Q.subgroupOf H) (N := Q.subgroupOf H) (Subtype.ext hz) ?_ le_rfl hzQ ?_ hsub ?_
    (fun x _ hx => hx) (isSLTwoOver_of_mulEquiv eJ.symm hN) (a2l_typU_of_mulEquiv eJ.symm hTU)
  · intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
    rw [hx]
    exact one_mem _
  · intro h
    exact hz1 (congrArg Subtype.val h)
  · intro x hx
    have hxQ : (x : G) ∈ centralizer ({z} : Set G) := (hQle (mem_subgroupOf.1 hx)).2
    rw [mem_centralizer_singleton_iff] at hxQ ⊢
    exact Subtype.ext hxQ
  · exact (AssemblyBPredicates.isQuasisimple_iff_native _).1 hQq |> fun h =>
      CFSG.IsQuasisimple.of_mulEquiv eJ h

end CFSG.OddStandard.SmallF3.HypA2Leaves
