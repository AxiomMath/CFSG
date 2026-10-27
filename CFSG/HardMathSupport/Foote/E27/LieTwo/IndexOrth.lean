module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.OrthKills
public import CFSG.HardMathSupport.Foote.E27.LieTwo.IndexSp

public section

namespace CFSG.HardMathSupport.Foote.E27

open TauCeti CFSG.Assembly.LowTwoRank

section Certificates

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_typeD_two
    (h : E27Config X K R T z) (hz : z ∈ K) {r : ℕ}
    {q : PrimePower} (hv : (LieTypeIndex.D r q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩)) (hp2 : q.p = 2)
    (hq : q.p ^ q.exponent = 2) (hr : r = 4 ∨ r = 5) : False := by
  obtain ⟨e⟩ := e
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp2 e
  obtain ⟨hp, hf⟩ := prime_pow_eq_two q.prime_p q.exponent_pos hq
  rw [hp, hf] at hm
  rcases hr with rfl | rfl
  · exact h.false_of_omegaPlus_four hz hm
  · exact h.false_of_omegaPlus_five hz hm

theorem E27Config.false_of_typeTwistedD_two
    (h : E27Config X K R T z) (hz : z ∈ K) {r : ℕ}
    {q : PrimePower} (hv : (LieTypeIndex.twistedD r q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩)) (hp2 : q.p = 2)
    (hq : q.p ^ q.exponent = 2) (hr : r = 4 ∨ r = 5) : False := by
  obtain ⟨e⟩ := e
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp2 e
  obtain ⟨hp, hf⟩ := prime_pow_eq_two q.prime_p q.exponent_pos hq
  rw [hp, hf] at hm
  rcases hr with rfl | rfl
  · exact h.false_of_omegaMinus_four hm
  · exact h.false_of_omegaMinus_five hz hm

end Certificates

end CFSG.HardMathSupport.Foote.E27
