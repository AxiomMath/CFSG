module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotHR8Setting

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

section Kinds

variable {Y : Type} [Group Y]

@[expose] def NeighbourOvergroupE7Field (s : Y) (D : Subgroup Y) (f : ℕ) : Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
      ∃ hsN : s ∈ normalizer (Kc : Set Y), E7Overgroup Kc (Kc.normalizerMonoidHom ⟨s, hsN⟩) f

@[expose] def NeighbourOvergroupE7Swap (s : Y) (D : Subgroup Y) : Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
      ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ Nonempty (Kc ⧸ center Kc ≃* D)

theorem NeighbourOvergroupE7.field_or_swap {s : Y} {D : Subgroup Y} {f : ℕ}
    (h : NeighbourOvergroupE7 s D f) :
    NeighbourOvergroupE7Field s D f ∨ NeighbourOvergroupE7Swap s D := by
  obtain ⟨Kc, hKc, hDK, h1 | h2⟩ := h
  · exact .inl ⟨Kc, hKc, hDK, h1⟩
  · exact .inr ⟨Kc, hKc, hDK, h2⟩

end Kinds

section Root


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def rootTorusG (e : L ≃* adjointGroup .E8 K) : Subgroup G :=
  (((EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K)).map e.symm.toMonoidHom).map
    L.subtype

@[expose] noncomputable def rootLeviG (e : L ≃* adjointGroup .E8 K) : Subgroup G :=
  ((e7Levi K).map e.symm.toMonoidHom).map L.subtype

theorem mem_centralizer_rootTorusG (e : L ≃* adjointGroup .E8 K) {t : G}
    (ht : t ∈ centralizer (L : Set G)) : t ∈ centralizer (rootTorusG e : Set G) :=
  centralizer_le (map_subtype_le _) ht

@[expose] def HR8FieldE8 (e : L ≃* adjointGroup .E8 K) (t : G) (f : ℕ) : Prop :=
  ∃ htX : t ∈ centralizer (rootTorusG e : Set G),
    NeighbourOvergroupE7Field
      (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩)
      (((rootLeviG e).subgroupOf (centralizer (rootTorusG e : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G))))) f

@[expose] def HR8SwapE8 (e : L ≃* adjointGroup .E8 K) (t : G) : Prop :=
  ∃ htX : t ∈ centralizer (rootTorusG e : Set G),
    NeighbourOvergroupE7Swap
      (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩)
      (((rootLeviG e).subgroupOf (centralizer (rootTorusG e : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G)))))

end Root

section HR8


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem hr8FieldE8_or_hr8SwapE8 (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : E7NotOddLieInput) (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput)
    {t : G} {f : ℕ} (hw : E8Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .E8 K) :
    HR8FieldE8 e t f ∨ HR8SwapE8 e t := by
  have htX := mem_centralizer_rootTorusG e hw.mem_centralizer
  rcases (neighbour_overgroup_E8_torus_of_seitzSetting_of_leafInputs hGLS hXodd hMinn hMcomp
    hw.seitz hf hw.card_eq e hw.mem_centralizer hw.orderOf_eq (Or.inr rfl) htX rfl).field_or_swap
    with h | h
  · exact .inl ⟨htX, h⟩
  · exact .inr ⟨htX, h⟩

end HR8

end CFSG.SeitzReduction.E8Pilot
