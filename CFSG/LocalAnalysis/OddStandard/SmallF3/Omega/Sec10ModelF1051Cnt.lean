module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelF1051

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

local notation "z0" => Certificates.OmegaT0.z0 ()

theorem model1051
    {U : Subgroup P45} (hUA : U ≤ QA45.originalSubgroup) (hUz : ∀ u ∈ U, u * z0 = z0 * u)
    (hQU : Q32 ≤ U) (hel : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Q32 ∧ a * a ∈ Q32) {n : ℕ}
    (hn : 1 ≤ n) (hidx : Q32.relIndex U = 2 ^ n) :
    n ≤ 2 ∧ 2 ^ n * Nat.card {q : P45 // q ∈ Q32 ∧
      ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ zpowers z0} < 32 := by
  have hQ : Q32 = Certificates.OmegaS107.Q0 := Subgroup.ext fun _ => mem_Q32_iff_mem_Q0
  rw [hQ] at hQU hel hidx ⊢
  exact Certificates.certificate442004.ext U hUA hUz hQU hel n hn hidx

end CFSG.OddStandard.SmallF3.Omega
