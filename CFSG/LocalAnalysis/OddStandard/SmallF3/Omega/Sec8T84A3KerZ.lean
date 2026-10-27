module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Odd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace A3

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}

private theorem simple_oddCore_Om6M {L : Subgroup G} (hL : IsOm6M L) :
    IsSimpleGroup (L ⧸ oddCore L) :=
  (CFSG.LieType.Simplicity.fam_classical_converse (L ⧸ oddCore L)
    ⟨.PSU, 4, 3, 1, hL.2.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)⟩).2.2

private theorem center_eq_oddCore_Om6M {L : Subgroup G} (hL : IsOm6M L) :
    center ↥L = oddCore ↥L :=
  center_eq_oddCore_of_simple hL.1 (simple_oddCore_Om6M hL)

theorem centerIn_le_oddCoreIn_N (h8A : Asc82Lemma8A) (hctx : Sec8Ctx G t L S z g B)
    (hL : IsOm6M L) : centerIn L ≤ oddCoreIn (Nsub8 t B) := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hc
  have hcommL : ∀ x ∈ L, x * (c' : G) = (c' : G) * x := by
    intro x hx
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hc' (⟨x, hx⟩ : ↥L))
  have hct : (c' : G) * t = t * (c' : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hctx.toSec3SettingLB.component.1 c'.2)
  have hcentA : (c' : G) ∈ centralizer (Asub8 t B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hAc : Asub8 t B ≤ centralizer ({↑c'} : Set G) := by
      rw [Asub8]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hct.symm
      · intro b hb
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommL b (hctx.B_le hb).1)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hAc ha)
  have hz : (c' : G) ∈ Asub8 t B ⊔ oddCoreIn (Nsub8 t B) := by
    rw [← sec8t84a1_centA h8A hctx]
    exact hcentA
  have hcO : c' ∈ oddCore ↥L := by
    rw [← center_eq_oddCore_Om6M hL]
    exact hc'
  have hcOddMem : (c' : G) ∈ oddCoreIn L := by
    rw [oddCoreIn, CFSG.inSubgroup]
    exact Subgroup.mem_map.mpr ⟨c', hcO, rfl⟩
  have hodd : Odd (orderOf (c' : G)) := odd_orderOf_of_mem_oddCoreIn hcOddMem
  refine mem_of_odd_of_mem_sup (A := Asub8 t B) (O := oddCoreIn (Nsub8 t B))
    (IsPGroup.of_card (n := 5) (by rw [(sec8t84a1_A_elem hctx).2]))
    (fun o ho => odd_orderOf_of_mem_oddCoreIn ho) ?_ hz hodd
  intro a ha o ho
  have hOcent : oddCoreIn (Nsub8 t B) ≤ centralizer (Asub8 t B : Set G) := by
    rw [sec8t84a1_centA h8A hctx]
    exact le_sup_right
  exact Subgroup.mem_centralizer_iff.mp (hOcent ho) a ha

end A3

end CFSG.OddStandard.SmallF3.Omega

