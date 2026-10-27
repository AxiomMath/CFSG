module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard

@[expose] def OddMultTrivial (s : TauCeti.SporadicName) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → Odd (Nat.card (center L)) →
    IsSporadic (L ⧸ center L) s → center L = ⊥

variable {s : TauCeti.SporadicName} {H : Type} [Group H] [Finite H] {L : Subgroup H}

theorem OddCover.center_eq_bot (hmult : OddMultTrivial s) (h : OddCover s L) :
    center ↥L = ⊥ :=
  hmult ↥L h.1 h.2.1 h.2.2

theorem OddCover.isSporadic_of_mult (hmult : OddMultTrivial s) (h : OddCover s L) :
    IsSporadic ↥L s :=
  isSporadic_of_center_eq_bot (h.center_eq_bot hmult) h.2.2

omit [Finite H] in
theorem OddCover.not_mem_centralizer_of_orderOf_two (h : OddCover s L) {u : H} (huL : u ∈ L)
    (hu2 : orderOf u = 2) : u ∉ centralizer (L : Set H) := by
  intro hc
  have hz : (⟨u, huL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 hc g g.2)
  have hdvd : orderOf u ∣ Nat.card (center ↥L) := by
    have h1 := orderOf_dvd_natCard (⟨⟨u, huL⟩, hz⟩ : ↥(center ↥L))
    rwa [← Subgroup.orderOf_coe, Subgroup.coe_mk, Subgroup.orderOf_mk] at h1
  rw [hu2] at hdvd
  exact absurd (h.2.1.of_dvd_nat hdvd) (by decide)

end CFSG.EvenSporadicStandard.Induction
