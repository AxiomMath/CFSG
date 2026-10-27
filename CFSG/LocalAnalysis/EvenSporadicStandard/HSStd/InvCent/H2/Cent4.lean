module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Config

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

namespace H2Cfg

variable {G : Type} [Group G] {t v : G} {J : Subgroup G}

theorem exists_equiv_alt5 [Finite G] (h4 : CatCentFour) (cfg : H2Cfg G t v J) {S : Subgroup G}
    (hS : IsSimpleGroup ↥S) (hnab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) (hcat : Catalog ↥S)
    (hV : kleinV t v ≤ S) (hinf : S ⊓ centralizer ({t} : Set G) ≤ kleinV t v) :
    Nonempty (↥S ≃* alternatingGroup (Fin 5)) := by
  have hcard : Nat.card ↥((kleinV t v).subgroupOf S) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv).trans cfg.card_kleinV
  refine h4 ↥S hS ?_ hcat ((kleinV t v).subgroupOf S) hcard ?_
  · obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (by simpa using congrArg Subtype.val h)⟩
  · intro w hw hw1
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hxw : (x : G) * (w : G) = (w : G) * (x : G) := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hx
        simpa using congrArg Subtype.val this
      have hwV : (w : G) ∈ kleinV t v := Subgroup.mem_subgroupOf.mp hw
      have hw0 : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
      have hxcent : (x : G) ∈ centralizer ({t} : Set G) := by
        rw [← cfg.centralizer_eq_of_mem hwV hw0]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hxw
      exact hinf ⟨x.2, hxcent⟩
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact cfg.comm_of_mem (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hw)

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
