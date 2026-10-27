module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Faith
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Orbit

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

namespace SL23Pair

variable {K : Type} [Group K] [Finite K] {A B : Subgroup K} (h : SL23Pair K A B)

include h

theorem rank_le_sixteen (E : Subgroup (MulAut K)) (hcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (hsq : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 16 := by
  have hcard : Nat.card (E.map h.theta) = Nat.card E :=
    (Nat.card_congr (Subgroup.equivMapOfInjective E h.theta h.theta_injective).toEquiv).symm
  have hcomm' : ∀ e ∈ E.map h.theta, ∀ f ∈ E.map h.theta, e * f = f * e := by
    intro e he f hf
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
    obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.mp hf
    rw [← map_mul, ← map_mul, hcomm e' he' f' hf']
  have hsq' : ∀ e ∈ E.map h.theta, e * e = 1 := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
    rw [← map_mul, hsq e' he', map_one]
  have hle := card_le_two_pow_of_supp (E.map h.theta) hcomm' hsq' Finset.univ
    (fun _ _ _ _ => Finset.mem_univ _)
  rw [hcard] at hle
  have h8 : (Finset.univ : Finset (Fin 4 ⊕ Fin 4)).card = 8 := by decide
  rw [h8] at hle
  calc Nat.card E ≤ 2 ^ (8 / 2) := hle
    _ = 16 := by norm_num

end SL23Pair

end CFSG.OddStandard.SmallF3.Omega.K5
