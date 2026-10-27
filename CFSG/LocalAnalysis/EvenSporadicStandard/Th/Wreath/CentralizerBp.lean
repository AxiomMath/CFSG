module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndSchur
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Index

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThLocalIn2.inf_centralizer_Aa_eq (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) :
    L ⊓ centralizer (Aa : Set G) = Aa := by
  refine le_antisymm ?_ (le_inf (le_trans W2.Aa_le W.B_le) ?_)
  · rintro c ⟨hcL, hcAa⟩
    have hcB : c ∈ B := (W.mem_B_iff c hcL).2 fun a ha =>
      (mem_centralizer_iff.1 hcAa a (W2.A_le ha)).symm
    rcases W2.mem_Aa_or_mul_b W hcB with h | h
    · exact h
    · exfalso
      have hbb : b * b = 1 := by rw [← sq]; exact W2.b_sq
      have hceq : c = (c * b) * b := by rw [mul_assoc, hbb, mul_one]
      refine W2.b_not_mem_centralizer W (mem_centralizer_iff.2 fun x hx => ?_)
      have h1 : ((c * b) * b) * x = x * ((c * b) * b) := by
        rw [← hceq]
        exact (mem_centralizer_iff.1 hcAa x hx).symm
      have h2 : (c * b) * x = x * (c * b) := W2.Aa_comm _ h _ hx
      have h3 : (c * b) * (b * x) = (c * b) * (x * b) := by
        calc (c * b) * (b * x) = ((c * b) * b) * x := by group
          _ = x * ((c * b) * b) := h1
          _ = (x * (c * b)) * b := by group
          _ = ((c * b) * x) * b := by rw [← h2]
          _ = (c * b) * (x * b) := by group
      exact (mul_left_cancel h3).symm
  · intro x hx
    exact mem_centralizer_iff.2 fun y hy => (W2.Aa_comm x hx y hy).symm

variable [Finite G]

end CFSG.EvenSporadicStandard.ThStd
