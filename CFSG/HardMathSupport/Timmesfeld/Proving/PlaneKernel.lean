module

public import CFSG.HardMathSupport.Timmesfeld.Proving.PlaneImage

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

variable {X : Type*} [Group X]

theorem exists_ne_one_centralizes_of_range_lt {p : ℕ} {K D : Subgroup X}
    (hDN : D ≤ Subgroup.normalizer (K : Set X)) (hcard : Nat.card D = p ^ 2)
    (hlt : Nat.card (planeAct hDN).range < p ^ 2) :
    ∃ d ∈ D, d ≠ 1 ∧ ∀ k ∈ K, d * k = k * d := by
  have hsum := Subgroup.card_ker_mul_card_range (planeAct hDN)
  rw [hcard] at hsum
  have hker1 : Nat.card (planeAct hDN).ker ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hsum
    rw [hsum] at hlt
    exact lt_irrefl _ hlt
  have hbot : (planeAct hDN).ker ≠ ⊥ := fun h => hker1 (Subgroup.card_eq_one.mpr h)
  obtain ⟨d, hd⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hdker : planeAct hDN (d : D) = 1 := MonoidHom.mem_ker.mp d.2
  have hdD : ((d : D) : X) ≠ 1 := by
    intro h
    apply hd
    exact Subtype.ext (Subtype.ext h)
  refine ⟨((d : D) : X), (d : D).2, hdD, ?_⟩
  intro k hk
  have hφ := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : X)) hdker
  simp [planeAct, Subgroup.inclusion] at hφ
  exact mul_inv_eq_iff_eq_mul.mp hφ

end CFSG.HardMathSupport.Timmesfeld.Proving
