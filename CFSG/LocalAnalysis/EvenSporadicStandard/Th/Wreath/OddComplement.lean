module

public import CFSG.GroupTheory.CentralSylowComplement
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.EndgameHyp

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem QHyp.exists_odd_complement {L A D Q : Subgroup G} {t : G} (hQ : QHyp L A D t Q) :
    ∃ O : Subgroup G, (∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x)) ∧
      ∀ x, (∀ q ∈ Q, x * q = q * x) → ∃ q ∈ Q, ∃ o ∈ O, x = q * o := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ x, x ∈ centralizer (Q : Set G) ↔ ∀ q ∈ Q, x * q = q * x := fun x => by
    rw [mem_centralizer_iff]
    exact forall₂_congr fun q _ => eq_comm
  have hQX : Q ≤ centralizer (Q : Set G) := fun x hx => (hmem x).2 fun q hq => hQ.comm x hx q hq
  have hidx : ¬ 2 ∣ Q.relIndex (centralizer (Q : Set G)) :=
    CFSG.GroupTheory.relIndex_not_dvd_of_maximal hQX hQ.pgroup fun P hP hPp hQP =>
      hQ.maximal P (hP.trans (centralizer_le hQ.D_le)) hPp hQP
  obtain ⟨O, hOX, hO, -, hdecomp⟩ :=
    CFSG.GroupTheory.exists_complement_of_central_sylow_two hQX hQ.pgroup
      (fun x hx => (hmem x).1 hx) hidx
  refine ⟨O, fun x => ⟨fun hx => ⟨(hmem x).1 (hOX hx), (hO x (hOX hx)).1 hx⟩,
    fun ⟨hx, hodd⟩ => (hO x ((hmem x).2 hx)).2 hodd⟩, fun x hx => hdecomp x ((hmem x).2 hx)⟩

end CFSG.EvenSporadicStandard.ThStd
