module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer

section Access

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {Q T U : Subgroup G} {t g : G}

theorem Ctx10.T4CS (h : Ctx10 G z k S M p Q T U t g) : Signalizer.T4CS z k S T := by
  by_cases h1 : TypeOneCase G k
  · exact Or.inl ⟨h1, (h.choice.T_one h1).1⟩
  · refine Or.inr ⟨h1, U, h.choice.U_le, h.choice.U_four, h.z_mem_U,
      ⟨t, ?_, ?_, (h.choice.T_two h1).2.1⟩, (h.choice.T_two h1).2.2.2.1, (h.choice.T_two h1).1,
      (h.choice.T_two h1).2.2.1⟩
    · rw [h.choice.U_gen]
      exact Subgroup.mem_sup_right (mem_zpowers t)
    · exact isConj_iff.mpr ⟨g⁻¹, by rw [h.choice.t_conj]; group⟩

end Access

end CFSG.GH74.GLS.Stage2.Bender.Thm2
