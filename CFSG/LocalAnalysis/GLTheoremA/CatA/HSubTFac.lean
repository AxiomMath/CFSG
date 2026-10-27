module

public import CFSG.LieType.SemisimpleCentralizers.HeldLinearComponents
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open
open CFSG.LieType.SemisimpleCentralizers Held

theorem isComponentOf_top_subgroupOf {G : Type} [Group G] {L X : Subgroup G}
    (h : IsComponentOf L X) : IsComponentOf (L.subgroupOf X) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact CFSG.Open.IsSubnormal.of_mathlib (h.2.1.subgroupOf)
  · have hiso : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe h.1
    exact (CFSG.Open.IsQuasisimple.congr hiso).mpr h.2.2

theorem conj_fix_of_commute {G : Type} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {c : G} (hc : c ∈ B) {h : G} (hh : h ∈ A) :
    c * h * c⁻¹ = h := by
  have e := hcomm h hh c hc
  calc c * h * c⁻¹ = (c * h) * c⁻¹ := rfl
    _ = (h * c) * c⁻¹ := by rw [← e]
    _ = h := by group

theorem normal_subgroupOf_sup_left {G : Type} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : (A.subgroupOf (A ⊔ B)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff le_sup_left]
  have hN : A ⊔ B ≤ Subgroup.normalizer (A : Set G) := by
    apply sup_le
    · exact Subgroup.le_normalizer
    · intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [conj_fix_of_commute hcomm hb hh]
        exact hh
      · intro hh
        have h2 := conj_fix_of_commute hcomm (B.inv_mem hb) hh
        have h3 : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
        rw [h3] at h2
        rw [h2]
        exact hh
  intro a k ha hk
  exact (Subgroup.mem_normalizer_iff.mp (hN hk) a).mp ha

theorem normal_subgroupOf_sup_right {G : Type} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : (B.subgroupOf (A ⊔ B)).Normal := by
  have hcomm' : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have h := normal_subgroupOf_sup_left (A := B) (B := A) hcomm'
  rw [sup_comm]
  exact h

theorem comp_le_or_le {G : Type} [Group G] [Finite G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L (A ⊔ B)) : L ≤ A ∨ L ≤ B := by
  haveI := normal_subgroupOf_sup_left hcomm
  haveI := normal_subgroupOf_sup_right hcomm
  have hL' := isComponentOf_top_subgroupOf hL
  rcases CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes
      (L.subgroupOf (A ⊔ B)) (A.subgroupOf (A ⊔ B)) hL' with hA | hA
  · left
    intro x hx
    have hxX : (⟨x, hL.1 hx⟩ : ↥(A ⊔ B)) ∈ L.subgroupOf (A ⊔ B) := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_subgroupOf.mp (hA hxX)
  · rcases CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes
        (L.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B)) hL' with hB | hB
    · right
      intro x hx
      have hxX : (⟨x, hL.1 hx⟩ : ↥(A ⊔ B)) ∈ L.subgroupOf (A ⊔ B) := Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_subgroupOf.mp (hB hxX)
    · exfalso
      have hxA : ∀ x ∈ L, ∀ a ∈ A, x * a = a * x := by
        intro x hx a ha
        have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hA
          (show (⟨x, hL.1 hx⟩ : ↥(A ⊔ B)) ∈ L.subgroupOf (A ⊔ B) from Subgroup.mem_subgroupOf.mpr hx)
        have h2 := (Subgroup.mem_centralizer_iff.mp hc) ⟨a, Subgroup.mem_sup_left ha⟩
          (show (⟨a, Subgroup.mem_sup_left ha⟩ : ↥(A ⊔ B)) ∈ A.subgroupOf (A ⊔ B) from ha)
        exact (congrArg Subtype.val h2).symm
      have hxB : ∀ x ∈ L, ∀ b ∈ B, x * b = b * x := by
        intro x hx b hb
        have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hB
          (show (⟨x, hL.1 hx⟩ : ↥(A ⊔ B)) ∈ L.subgroupOf (A ⊔ B) from Subgroup.mem_subgroupOf.mpr hx)
        have h2 := (Subgroup.mem_centralizer_iff.mp hc) ⟨b, Subgroup.mem_sup_right hb⟩
          (show (⟨b, Subgroup.mem_sup_right hb⟩ : ↥(A ⊔ B)) ∈ B.subgroupOf (A ⊔ B) from hb)
        exact (congrArg Subtype.val h2).symm
      have hxcen : ∀ x ∈ L, A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
        intro x hx
        refine sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hxA x hx a ha).symm)
          (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hxB x hx b hb).symm)
      have hLcomm : ∀ y ∈ L, ∀ z ∈ L, y * z = z * y := by
        intro y hy z hz
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hxcen y hy (hL.1 hz))).symm
      have hcomm_sub : ∀ a b : ↥(L.subgroupOf (A ⊔ B)), a * b = b * a := by
        intro a b
        exact Subtype.ext (Subtype.ext (hLcomm _ (Subgroup.mem_subgroupOf.mp a.2) _
          (Subgroup.mem_subgroupOf.mp b.2)))
      exact (Held.not_isQuasisimple_of_comm hcomm_sub) hL'.2.2

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
