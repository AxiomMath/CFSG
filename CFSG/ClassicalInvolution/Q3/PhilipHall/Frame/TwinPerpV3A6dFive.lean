module

public import Certificates.Certificate398601
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dAbs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE

theorem noOrderFive_aeBarOver {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (hA : ∀ σ ∈ A, σ ^ 5 = 1 → σ = 1) : NoOrderFive (aeBarOver A) := by
  intro g hg h5
  obtain ⟨w, hw, rfl⟩ := hg
  have hwA : (permHom n) w ∈ A := (Subgroup.mem_inf.mp hw).2
  have h1 : mkQ n (w ^ 5) = 1 := by rw [map_pow]; exact h5
  have h2 : w ^ 5 ∈ piSub n := (QuotientGroup.eq_one_iff (N := piSub n) _).mp h1
  have h3 : (permHom n) (w ^ 5) = 1 := by
    rcases mem_piSub.mp h2 with h | h
    · rw [h, map_one]
    · rw [h]
      rfl
  have h4 : (permHom n) w ^ 5 = 1 := by rw [← map_pow]; exact h3
  have h6 : (permHom n) w = 1 := hA _ hwA h4
  have h7 : w ∈ vecSub n := h6
  have h8 : w * w = 1 := vecSub_mul_self h7
  have h9 : mkQ n w * mkQ n w = 1 := by rw [← map_mul, h8, map_one]
  calc mkQ n w = mkQ n w ^ 5 := by
        calc mkQ n w = (mkQ n w * mkQ n w) * (mkQ n w * mkQ n w) * mkQ n w := by
              rw [h9, one_mul, one_mul]
          _ = mkQ n w ^ 5 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h5

section Five


theorem noFive_agl32 : ∀ σ ∈ agl32, σ ^ 5 = 1 → σ = 1 := by
  have h := Certificates.certificate398601
  unfold noFiveCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  intro σ hσ h5
  by_contra hne
  exact h.1 σ h5 hne hσ

theorem noFive_l32 : ∀ σ ∈ l32, σ ^ 5 = 1 → σ = 1 := by
  have h := Certificates.certificate398601
  unfold noFiveCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  intro σ hσ h5
  by_contra hne
  exact h.2 σ h5 hne hσ

theorem noOrderFive_e29Sub : NoOrderFive e29Sub := noOrderFive_aeBarOver agl32 noFive_agl32

theorem noOrderFive_e64Sub : NoOrderFive e64Sub := noOrderFive_aeBarOver l32 noFive_l32

end Five

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d
