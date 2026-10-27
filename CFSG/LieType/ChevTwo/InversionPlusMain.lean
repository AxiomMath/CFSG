module

public import CFSG.LieType.ChevTwo.InversionCases
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthFam
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthFamD4
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthFamMinus4
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthFamPlus4

public section

namespace CFSG.LieType.ChevTwo

open CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

theorem invertsOddElt_of_kleinBigInv {S : Type} [Group S] (hK : KleinBigInv S)
    {A : Subgroup (MulAut S)} (hA : OuterKleinFour A) : InvertsOddElt A := by
  obtain ⟨hAe, hcard, hAI⟩ := hA
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← pow_two]; exact hAe.2 a ha
  obtain ⟨α, hαA, x, p, hp, hp7, hord⟩ := hK A hcomm hsq hcard hAI
  have hodd : Odd p := by
    rcases hp.eq_two_or_odd' with h2 | h2
    · omega
    · exact h2
  have hα2 : α * α = 1 := hsq α hαA
  refine ⟨α, hαA, ?_, α x * x⁻¹, by rw [hord]; exact hodd, by rw [hord]; omega, ?_⟩
  · rintro rfl
    have h1 : (1 : MulAut S) x * x⁻¹ = 1 := by simp
    rw [h1, orderOf_one] at hord
    exact hp.one_lt.ne hord
  · have h1 : α (α x) = x := by
      have := congrArg (fun τ : MulAut S => τ x) hα2
      simpa using this
    rw [map_mul, map_inv, h1, mul_inv_rev, inv_inv]

theorem chev2RankTwoInverts_orthPlus : OrthPlusInverts := by
  intro S _ h A hA
  obtain ⟨n, f, hm⟩ := h
  obtain ⟨-, -, hn4⟩ := hm.1
  refine invertsOddElt_of_kleinBigInv ?_ hA
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · obtain rfl : n = 4 := by omega
    by_cases hf : f = 2
    · subst hf
      exact kleinBigInv_POmegaPlus_four_q4 hm
    · exact kleinBigInv_POmegaPlus_four hf hm
  · by_cases hf : f = 2
    · subst hf
      exact kleinBigInv_POmegaPlus_ge_five_q4 h5 hm
    · exact kleinBigInv_POmegaPlus_ge_five h5 (Or.inl hf) hm

theorem chev2RankTwoInverts_orthMinus : OrthMinusInverts := by
  intro S _ h A hA
  obtain ⟨n, f, hm⟩ := h
  refine invertsOddElt_of_kleinBigInv ?_ hA
  by_cases hf : f = 2
  · subst hf
    exact kleinBigInv_POmegaMinus_four hm
  · exact kleinBigInv_POmegaMinus (Or.inl hf) hm

end CFSG.LieType.ChevTwo
