module


public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CyclicCentralizerEquality

theorem eq_of_cyclic_exponent_prime {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X C : Subgroup G} (hXC : X ≤ C) (hcyc : IsCyclic C) (hexp : ∀ c ∈ C, c ^ p = 1)
    (hX : Nat.card X = p) : C = X := by
  obtain ⟨c, hc⟩ := hcyc.exists_generator
  have h1 : Nat.card C = orderOf c := (orderOf_eq_card_of_forall_mem_zpowers hc).symm
  have h2 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one (by
    have := hexp c c.2
    exact Subtype.ext (by simpa using this))
  have h3 : Nat.card C ∣ p := h1 ▸ h2
  have h4 : p ∣ Nat.card C := hX ▸ Subgroup.card_dvd_of_le hXC
  have h5 : Nat.card C = p := Nat.dvd_antisymm h3 h4
  exact (Subgroup.eq_of_le_of_card_ge hXC (by rw [h5, hX])).symm

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CyclicCentralizerEquality
