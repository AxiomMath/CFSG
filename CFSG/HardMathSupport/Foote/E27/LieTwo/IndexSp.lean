module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.SpSix
public import CFSG.HardMathSupport.Foote.E27.LieTwo.SpEight

public section

namespace CFSG.HardMathSupport.Foote.E27

open TauCeti CFSG.Assembly.LowTwoRank

theorem prime_pow_eq_two {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : p ^ f = 2) :
    p = 2 ∧ f = 1 := by
  have hp2 : p = 2 := by
    have : p ∣ 2 := hq ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective le_rfl (by simpa using hq)⟩

section Certificates

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_typeB_three_two (h : E27Config X K R T z) {q : PrimePower}
    (hv : (LieTypeIndex.B 3 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.B 3 q, hv⟩)) (hp2 : q.p = 2)
    (hq : q.p ^ q.exponent = 2) : False := by
  obtain ⟨e⟩ := e
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hp2 le_rfl e
  obtain ⟨hp, hf⟩ := prime_pow_eq_two q.prime_p q.exponent_pos hq
  rw [hp, hf] at hm
  exact h.false_of_psp_six hm

theorem E27Config.false_of_typeB_four_two (h : E27Config X K R T z) (hz : z ∈ K) {q : PrimePower}
    (hv : (LieTypeIndex.B 4 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.B 4 q, hv⟩)) (hp2 : q.p = 2)
    (hq : q.p ^ q.exponent = 2) : False := by
  obtain ⟨e⟩ := e
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 4 q hv hp2
    (by norm_num) e
  obtain ⟨hp, hf⟩ := prime_pow_eq_two q.prime_p q.exponent_pos hq
  rw [hp, hf] at hm
  exact h.false_of_psp_eight hz hm

end Certificates

end CFSG.HardMathSupport.Foote.E27
