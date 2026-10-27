module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG2B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {NQ : Subgroup G} {N : Subgroup ↥NQ} [N.Normal]

theorem z4j_V_facts_lift {Vc Vsub : Subgroup ↥NQ} {Vh : Subgroup (↥NQ ⧸ N)}
    (hVc : Z4JLift N Vc Vh) (hVsub : Vsub ≤ Vc)
    (hn : ∀ g ∈ Vh, ∀ v ∈ Vsub.map (z4iπ N), g * v * g⁻¹ ∈ Vsub.map (z4iπ N))
    (h4 : Nat.card (Vsub.map (z4iπ N)) = 4)
    (he : ∀ a ∈ Vsub.map (z4iπ N), ∀ b ∈ Vsub.map (z4iπ N), a * b = b * a ∧ a * a = 1) :
    (∀ g ∈ Vc.map NQ.subtype, ∀ v ∈ Vsub.map NQ.subtype, g * v * g⁻¹ ∈ Vsub.map NQ.subtype) ∧
      Nat.card (Vsub.map NQ.subtype) = 4 ∧
      ∀ a ∈ Vsub.map NQ.subtype, ∀ b ∈ Vsub.map NQ.subtype, a * b = b * a ∧ a * a = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg v hv
    obtain ⟨c, hcVc, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨x, hxVsub, rfl⟩ := Subgroup.mem_map.mp hv
    have hcVh : z4iπ N c ∈ Vh := by
      rw [← hVc.map_eq]
      exact Subgroup.mem_map_of_mem (z4iπ N) hcVc
    have hin : z4iπ N c * z4iπ N x * (z4iπ N c)⁻¹ ∈ Vsub.map (z4iπ N) :=
      hn (z4iπ N c) hcVh (z4iπ N x) (Subgroup.mem_map_of_mem (z4iπ N) hxVsub)
    obtain ⟨x', hx'Vsub, hx'eq⟩ := Subgroup.mem_map.mp hin
    have hmem : c * x * c⁻¹ ∈ Vc :=
      Vc.mul_mem (Vc.mul_mem hcVc (hVsub hxVsub)) (Vc.inv_mem hcVc)
    have hEq : x' = c * x * c⁻¹ := by
      refine hVc.inj (hVsub hx'Vsub) hmem ?_
      rw [map_mul, map_mul, map_inv]
      exact hx'eq
    refine Subgroup.mem_map.mpr ⟨x', hx'Vsub, ?_⟩
    rw [hEq, map_mul, map_mul, map_inv]
  · rw [Subgroup.card_subtype, ← hVc.card_map hVsub]
    exact h4
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨hab, haa⟩ := he (z4iπ N a') (Subgroup.mem_map_of_mem (z4iπ N) ha')
      (z4iπ N b') (Subgroup.mem_map_of_mem (z4iπ N) hb')
    have hab' : a' * b' = b' * a' := hVc.comm (hVsub ha') (hVsub hb') hab
    have haa' : a' * a' = 1 := hVc.mul_self_eq_one (hVsub ha') haa
    exact ⟨by simpa using congrArg NQ.subtype hab',
      by simpa using congrArg NQ.subtype haa'⟩

theorem z4j_card_cent_lift {Vc : Subgroup ↥NQ} {Vh : Subgroup (↥NQ ⧸ N)}
    (hVc : Z4JLift N Vc Vh) {b : ↥NQ} (hb : b ∈ Vc) :
    Nat.card ↥(Vc.map NQ.subtype ⊓ centralizer ({(b : G)} : Set G)) =
      Nat.card ↥(Vh ⊓ centralizer ({z4iπ N b} : Set (↥NQ ⧸ N))) := by
  rw [← hVc.card_cent hb]
  have hmap : (Vc ⊓ centralizer ({b} : Set ↥NQ)).map NQ.subtype =
      Vc.map NQ.subtype ⊓ centralizer ({(b : G)} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyV, hyc⟩, rfl⟩
      refine ⟨⟨y, hyV, rfl⟩, ?_⟩
      have hyc' : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp hyc
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hyc')
    · rintro ⟨⟨y, hyV, rfl⟩, hyc⟩
      refine ⟨y, ⟨hyV, ?_⟩, rfl⟩
      have hyc' : (y : G) * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp hyc
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hyc')
  rw [← hmap]
  exact Subgroup.card_map_of_injective NQ.subtype_injective

theorem z4j_comm_lift {Vc Vsub : Subgroup ↥NQ} {Vh : Subgroup (↥NQ ⧸ N)}
    (hVc : Z4JLift N Vc Vh) (hVsub : Vsub ≤ Vc) {b : ↥NQ} (hb : b ∈ Vc)
    (hbV : z4iπ N b ∈ centralizer ((Vsub.map (z4iπ N) : Subgroup (↥NQ ⧸ N)) : Set (↥NQ ⧸ N))) :
    Vsub.map NQ.subtype ≤ centralizer ({(b : G)} : Set G) := by
  rintro x ⟨v, hv, rfl⟩
  have hall : ∀ w ∈ Vsub.map (z4iπ N), z4iπ N b * w = w * z4iπ N b := fun w hw =>
    ((Subgroup.mem_centralizer_iff.mp hbV) w hw).symm
  have hbv : b * v = v * b := (hVc.centralizes_iff hVsub hb).mpr hall v hv
  exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hbv.symm)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
