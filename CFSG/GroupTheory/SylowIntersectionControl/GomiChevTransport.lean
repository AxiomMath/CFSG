module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Chev

public section

namespace CFSG.GroupTheory

open Subgroup

section Quotient

variable {X : Type} [Group X]

theorem IsGomiChevTwo.quotient_center [Finite X] (h : IsGomiChevTwo X) :
    IsGomiChevTwo (X ⧸ center X) := by
  obtain ⟨hQ, -, hC⟩ := h
  have : Group.IsPerfect X := hQ.1
  have : IsSimpleGroup (X ⧸ center X) := hQ.2.1
  have hZ : center (X ⧸ center X) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot X
  have eZ : (X ⧸ center X) ⧸ center (X ⧸ center X) ≃* X ⧸ center X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hQ' : IsQuasisimple (X ⧸ center X) := by
    refine ⟨inferInstance, eZ.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hQ.2.2
    exact ⟨eZ.symm a, eZ.symm b, fun h => hab (by simpa using congrArg eZ h)⟩
  refine ⟨hQ', ?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 (X ⧸ center X)) with hpc | hpc
    · exact hpc
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have htop : IsPGroup 2 (⊤ : Subgroup (X ⧸ center X)) :=
        hpc ▸ CFSG.pCore_isPGroup (p := 2) (G := X ⧸ center X)
      have hQp : IsPGroup 2 (X ⧸ center X) := htop.of_equiv Subgroup.topEquiv
      have : Group.IsNilpotent (X ⧸ center X) := hQp.isNilpotent
      exact Group.IsNilpotent.center_ne_bot (X ⧸ center X) hZ
  · exact CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.isChevTwo_of_mulEquiv eZ.symm hC

end Quotient

section Map

variable {G : Type} [Group G]

theorem nonempty_mulEquiv_map_mk' {L Z : Subgroup G} [Z.Normal]
    (hLZ : Z.subgroupOf L = center ↥L) :
    Nonempty (↥(L.map (QuotientGroup.mk' Z)) ≃* ↥L ⧸ center ↥L) := by
  let f : ↥L →* G ⧸ Z := (QuotientGroup.mk' Z).domRestrict L
  have hker : f.ker = Z.subgroupOf L := by
    change ((QuotientGroup.mk' Z).domRestrict L).ker = Z.subgroupOf L
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  have hrange : f.range = L.map (QuotientGroup.mk' Z) := by
    change ((QuotientGroup.mk' Z).domRestrict L).range = L.map (QuotientGroup.mk' Z)
    rw [MonoidHom.domRestrict_range]
  have hker' : f.ker = center ↥L := by rw [hker, hLZ]
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker'))⟩

theorem IsGomiChevTwo.map_mk' [Finite G] {L Z : Subgroup G} [Z.Normal] (hL : IsGomiChevTwo ↥L)
    (hLZ : Z.subgroupOf L = center ↥L) : IsGomiChevTwo ↥(L.map (QuotientGroup.mk' Z)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_map_mk' hLZ
  exact (IsGomiChevTwo.quotient_center hL).of_mulEquiv e.symm

theorem nonempty_mulEquiv_quotient_center_map_mk' {L Z : Subgroup G} [Z.Normal]
    (hL : CFSG.IsQuasisimple ↥L) (hLZ : Z.subgroupOf L = center ↥L) :
    Nonempty (↥(L.map (QuotientGroup.mk' Z)) ⧸ center ↥(L.map (QuotientGroup.mk' Z)) ≃*
      ↥L ⧸ center ↥L) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_map_mk' hLZ
  have : Group.IsPerfect ↥L := hL.1
  have hZ : center (↥L ⧸ center ↥L) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot ↥L
  have hZbar : center (↥(L.map (QuotientGroup.mk' Z))) = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, hZ, Subgroup.map_bot]
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZbar).trans QuotientGroup.quotientBot).trans e⟩

theorem map_conj_inf_centralizer_eq_bot {L : Subgroup G}
    (hZ : L ⊓ centralizer (L : Set G) = ⊥) (g : G) :
    L.map (MulAut.conj g).toMonoidHom ⊓
      centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  obtain ⟨⟨y, hy, rfl⟩, hzc⟩ := mem_inf.mp hz
  have hyc : y ∈ L ⊓ centralizer (L : Set G) := by
    refine mem_inf.mpr ⟨hy, mem_centralizer_iff.mpr fun w hw => ?_⟩
    have h1 : g * w * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * w * g⁻¹) :=
      mem_centralizer_iff.mp hzc _ ⟨w, hw, rfl⟩
    calc w * y = g⁻¹ * (g * w * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * (g * w * g⁻¹)) * g := by rw [h1]
      _ = y * w := by group
  rw [hZ, mem_bot] at hyc
  simp [hyc]

end Map

end CFSG.GroupTheory
