module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Five

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem s56_mem_Q2_iff {m : G} : m ∈ d.s56Q2 ↔ m ∈ d.M ∧ ∀ e ∈ d.E, e * m = m * e := by
  rw [s56Q2, mem_inf, mem_centralizer_iff]
  exact Iff.rfl

theorem Hyp.s56_mem_A_iff (hd : d.Hyp) {a : G} : a ∈ d.A ↔ a ∈ d.E ∨ d.t * a ∈ d.E :=
  mem_sup_zpowers_iff hd.t_mul_self fun p hp => hd.L_comm_t (s56_E_le_L d hp)

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
