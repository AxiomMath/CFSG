module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE17D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE17F
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE17H
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE17I

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem l41_q1elem_of (h : L41GPh16 t L S x₁ x₂ lam rho) :
    ∀ q ∈ l41Q1 t x₁ x₂ rho, q * q ∈ l41Y t x₁ x₂ rho := by
  rcases h.q1facts.quot_Q1 with ⟨φ, -, hker⟩ | e
  · intro q hq
    have hsq : φ ⟨q, hq⟩ * φ ⟨q, hq⟩ = 1 := by
      ext i
      have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
      exact h2 _
    have hmem : (⟨q, hq⟩ * ⟨q, hq⟩ : ↥(l41Q1 t x₁ x₂ rho)) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      exact hsq
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  · exfalso
    have hab := e17_Q1_comm h e
    obtain ⟨a, ha, ha4⟩ := e17_exists_pow4 e (e17_Omega1_le_Y h hab)
    obtain ⟨γ, -, hγ4, E, hE, hE2, h32, hγE, hcomm⟩ := e17_gamma h hab ⟨a, ha, ha4⟩
    exact hγ4 (e17_no_gamma h hE hE2 h32 hγE hcomm)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l41_q1elem_holds : L41Q1ElemStmt :=
  fun h => S4A.l41_q1elem_of h.toG

end CFSG.OddStandard.SmallF3.HarrisU33
