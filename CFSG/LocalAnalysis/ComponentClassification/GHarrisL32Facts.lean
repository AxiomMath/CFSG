module

public import Certificates.Certificate22602

public section

namespace CFSG.ComponentClassification.GHarris.SCert.SE

theorem pow_four_cases : ∀ s : SE, s ^ 4 = 1 ∨ s ^ 4 = gen 0 ∨ s ^ 4 = invRep 1 ∨
    s ^ 4 = invRep 1 * gen 0 := by
  decide +kernel

theorem ay_pow_four : (gen 8 * gen 7) ^ 4 = gen 0 := by decide

theorem ay_comm_x : gen 8 * gen 7 * gen 6 = gen 6 * (gen 8 * gen 7) := by decide

theorem normalizes_ay : ∀ c : SE, c * gen 6 = gen 6 * c →
    ∃ k : Fin 8, c⁻¹ * (gen 8 * gen 7) * c = (gen 8 * gen 7) ^ (k : ℕ) := by
  decide +kernel

theorem card_normalizer_ya3 : (Finset.univ.filter fun c : SE => c * invRep 1 = invRep 1 * c ∧
    ∃ k : Fin 8, c⁻¹ * (gen 7 * gen 4) * c = (gen 7 * gen 4) ^ (k : ℕ)).card = 32 := by
  decide +kernel

theorem exists_conj_ya3 (w : SE)
    (hw : w * invRep 1 = invRep 1 * w) (hw4 : w ^ 4 = gen 0) :
    ∃ s : SE, s⁻¹ * (gen 7 * gen 4) * s = w :=
  Certificates.certificate22602 w hw hw4

theorem conj_x_xz : (gen 2)⁻¹ * gen 6 * gen 2 = gen 6 * gen 0 := by decide

theorem card_inv_centralizer_x : (Finset.univ.filter fun c : SE =>
    c * gen 6 = gen 6 * c ∧ c * c = 1 ∧ c ≠ 1).card = 31 := by
  decide +kernel

theorem card_inv_centralizer_a1l : (Finset.univ.filter fun c : SE =>
    c * invRep 2 = invRep 2 * c ∧ c * c = 1 ∧ c ≠ 1).card = 23 := by
  decide +kernel

theorem pow_four_of_comm_a3a4 : ∀ c : SE, c * invRep 3 = invRep 3 * c → c ^ 4 = 1 := by
  decide +kernel

end CFSG.ComponentClassification.GHarris.SCert.SE
