module

public import CFSG.ClassicalInvolution.Uniform.UThmStmtA

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

section Counting

variable {t : MemberType} {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}

theorem IsClassicalMemberU.oddCore_eq_bot_of_natCard_eq (h : IsClassicalMemberU t L z)
    (hs : t.IsSolvableType) (hc : Nat.card L = 24) : classicalInvolutionOddCore L = ⊥ := by
  obtain ⟨e⟩ := h.nonempty_equiv_sl2Three hs
  have hq : Nat.card (L ⧸ classicalInvolutionOddCore L) = 24 := by
    rw [Nat.card_congr e.toEquiv]
    exact natCard_sl2Three
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore L)
  rw [hq, hc] at h1
  have h2 : Nat.card (classicalInvolutionOddCore L) = 1 := by omega
  exact Subgroup.eq_bot_of_card_eq _ h2

end Counting

section Exact

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem OmegaLieU.exactMembers (hΩ : HypOmegaModU (.sl2 p f) Ω) (D : OmegaLieU p f Ω) :
    ExactMembers Ω := by
  intro L hL
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  by_cases h3 : p ^ f = 3
  · exact hz.oddCore_eq_bot_of_natCard_eq h3 (D.card_eq h3 L hL)
  · have hp2 : p ≠ 2 := hz.admissible.2.1
    have hq : 5 ≤ p ^ f :=
      (three_le_iff_five_le hp2 h3).mp
        (three_le_pow_of_odd_prime hz.admissible.1 hp2 hz.admissible.2.2)
    exact (D.toOmegaLieOfSpec fun i => ((D.valid i).nonempty_modelSpec h3).some).exactMembers hp2
      hq ((hypOmegaModU_iff_hypOmegaMod hp2 hq).mp hΩ) L hL

end Exact

end CFSG.ClassicalInvolution.Uniform
