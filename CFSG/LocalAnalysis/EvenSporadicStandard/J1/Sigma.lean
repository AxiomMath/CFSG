module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Orbit

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

theorem sigma_orbit {σ : G} (hσ : σ ∈ H.NL) (h7 : orderOf σ = 7) :
    (∀ e ∈ H.E, e ≠ 1 → σ * e * σ⁻¹ ≠ e) ∧
    ∀ e ∈ H.E, ∀ e' ∈ H.E, e ≠ 1 → e' ≠ 1 → ∃ i : ℕ, σ ^ i * e * (σ ^ i)⁻¹ = e' := by
  obtain ⟨hσL, hσN⟩ := H.mem_NL_iff.1 hσ
  set φ : MulAut H.E := H.E.normalizerMonoidHom ⟨σ, hσN⟩ with hφ
  have happly : ∀ e : H.E, (φ e : G) = σ * e * σ⁻¹ := fun e => rfl
  have hpow : ∀ (i : ℕ) (e : H.E), ((φ ^ i) e : G) = σ ^ i * e * (σ ^ i)⁻¹ := by
    intro i
    induction i with
    | zero => intro e; simp
    | succ n ih =>
      intro e
      rw [pow_succ', MulAut.mul_apply, happly, ih]
      simp only [pow_succ', mul_inv_rev, mul_assoc]
  have hσ7 : σ ^ 7 = 1 := by rw [← h7]; exact pow_orderOf_eq_one σ
  have hφ7 : orderOf φ = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    refine orderOf_eq_prime ?_ ?_
    · ext e
      have := hpow 7 e
      rw [hσ7] at this
      simpa using this
    · intro h1
      have hc : ∀ e ∈ H.E, e * σ = σ * e := fun e he => by
        have := hpow 1 ⟨e, he⟩
        rw [h1] at this
        simp only [pow_one] at this
        have h2 : e = σ * e * σ⁻¹ := this
        calc e * σ = σ * e * σ⁻¹ * σ := by rw [← h2]
          _ = σ * e := by group
      have hσE : σ ∈ H.E := by
        rw [← H.centralizer_E]
        exact ⟨Subgroup.mem_centralizer_iff.2 fun e he => hc e he, hσL⟩
      have h2 := H.sq_E σ hσE
      have : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
      rw [h7] at this
      omega
  obtain ⟨hfree, htrans⟩ := orbit_of_prime_order (by simpa using H.card_E) φ hφ7
  refine ⟨fun e he he1 hc => ?_, fun e he e' he' he1 he'1 => ?_⟩
  · apply hfree ⟨e, he⟩ (fun h => he1 (congrArg Subtype.val h)) 
    exact Subtype.ext (by simpa [happly] using hc)
  · obtain ⟨i, hi⟩ := htrans ⟨e, he⟩ ⟨e', he'⟩ (fun h => he1 (congrArg Subtype.val h))
      (fun h => he'1 (congrArg Subtype.val h))
    refine ⟨i, ?_⟩
    have := congrArg Subtype.val hi
    rw [hpow] at this
    exact this

end Setting

end CFSG.EvenSporadicStandard.J1Std
