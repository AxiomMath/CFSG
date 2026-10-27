module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem three_dvd_card_of_mem_inner_of_pow_three {G : Type} [Group G] [Finite G]
    (hZ : Subgroup.center G = ⊥) {η : MulAut G}
    (hη : η ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G)
    (hη3 : η ^ 3 = 1) (hη1 : η ≠ 1) : 3 ∣ Nat.card G := by
  obtain ⟨g, hg⟩ := hη
  have hη3' : (MulAut.conj g) ^ 3 = 1 := by rw [hg]; exact hη3
  have hη1' : MulAut.conj g ≠ 1 := by rw [hg]; exact hη1
  have hconjpow : (MulAut.conj g) ^ 3 = MulAut.conj (g ^ 3) := by
    rw [← MonoidHom.map_pow]
  have hconj_one : MulAut.conj (g ^ 3) = 1 := by
    rw [← hconjpow]; exact hη3'
  have hcent : g ^ 3 ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : (MulAut.conj (g ^ 3)) y = y := by
      simpa using congrArg (fun f : MulAut G => f y) hconj_one
    have h1' : (g ^ 3) * y * (g ^ 3)⁻¹ = y := by
      simpa [MulAut.conj_apply, MulAut.mul_apply, pow_succ, pow_two, mul_assoc] using h1
    have h2 : (g ^ 3) * y = y * (g ^ 3) := by
      calc (g ^ 3) * y = (g ^ 3 * y * (g ^ 3)⁻¹) * (g ^ 3) := by group
        _ = y * (g ^ 3) := by rw [h1']
    exact h2.symm
  have h3 : g ^ 3 = 1 := by
    rw [hZ] at hcent; simpa using hcent
  have hg1 : g ≠ 1 := by
    intro h
    apply hη1'
    rw [h]
    exact map_one (MulAut.conj : G →* MulAut G)
  have hord : orderOf g = 3 := by
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 h3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1
    · exact h
  rw [← hord]
  exact orderOf_dvd_natCard g

end CFSG.LocalAnalysis.GLTheoremA
