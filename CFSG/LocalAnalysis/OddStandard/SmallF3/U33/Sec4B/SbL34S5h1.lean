module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5g0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0g2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0i

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem card_Z_inf_T_le (ha : Ctx4P t L S x₁ x₂ lam rho tau) (Z : Subgroup G)
    (hZP : ∀ z ∈ Z, ∀ p ∈ ctxPL t tau x₁ x₂, z * p * z⁻¹ * p⁻¹ ∈ fourGrp x₁ x₂) :
    Nat.card ↥(Z ⊓ closure ({t, tau} : Set G)) ≤ 2 := by
  by_contra hle
  push Not at hle
  have hc := ha.toCtx4L.toCtx4Q
  have hdvd : Nat.card ↥(Z ⊓ closure ({t, tau} : Set G)) ∣ 4 := by
    have h := Subgroup.card_dvd_of_le (H := Z ⊓ closure ({t, tau} : Set G))
      (K := closure ({t, tau} : Set G)) inf_le_right
    rwa [card_T hc] at h
  have hcard : Nat.card ↥(Z ⊓ closure ({t, tau} : Set G)) = 4 := by
    have hdvd' : Nat.card ↥(Z ⊓ closure ({t, tau} : Set G)) ∣ 2 ^ 2 := by
      norm_num at hdvd ⊢
      exact hdvd
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    interval_cases k <;> simp_all
  have hZT : Z ⊓ closure ({t, tau} : Set G) = closure ({t, tau} : Set G) :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [card_T hc, hcard]))
  have hTZ : closure ({t, tau} : Set G) ≤ Z := by
    rw [← hZT]
    exact inf_le_left
  have hVX : fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
    rw [fourGrp, ctxX]
    apply Subgroup.closure_mono
    intro b hb
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hb)
  have hX_le_P : ctxX t tau x₁ x₂ ≤ ctxPL t tau x₁ x₂ :=
    (X_le_O hc).trans (O_le_ctxPL ha.toCtx4A)
  have hconj : ∀ p ∈ ctxPL t tau x₁ x₂, ∀ k ∈ ctxX t tau x₁ x₂,
      p * k * p⁻¹ ∈ ctxX t tau x₁ x₂ := by
    intro p hp
    have hgen : ∀ a ∈ ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G),
        p * a * p⁻¹ ∈ ctxX t tau x₁ x₂ := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with h | h | h | h
      ·
        rw [h]
        have htZ : t ∈ Z := hTZ (Subgroup.subset_closure (by simp))
        have hh := hZP t htZ p hp
        have hinv : p * t * p⁻¹ * t⁻¹ ∈ fourGrp x₁ x₂ := by
          rw [show p * t * p⁻¹ * t⁻¹ = (t * p * t⁻¹ * p⁻¹)⁻¹ by group]
          exact inv_mem hh
        rw [show p * t * p⁻¹ = (p * t * p⁻¹ * t⁻¹) * t by group]
        exact mul_mem (hVX hinv) (Subgroup.subset_closure (by simp))
      ·
        rw [h]
        have htauZ : tau ∈ Z := hTZ (Subgroup.subset_closure (by simp))
        have hh := hZP tau htauZ p hp
        have hinv : p * tau * p⁻¹ * tau⁻¹ ∈ fourGrp x₁ x₂ := by
          rw [show p * tau * p⁻¹ * tau⁻¹ = (tau * p * tau⁻¹ * p⁻¹)⁻¹ by group]
          exact inv_mem hh
        rw [show p * tau * p⁻¹ = (p * tau * p⁻¹ * tau⁻¹) * tau by group]
        exact mul_mem (hVX hinv) (Subgroup.subset_closure (by simp))
      ·
        rw [h]
        have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
        have hcomm := P_comm_V ha p hp (x₁ ^ 2) hyV
        rw [show p * x₁ ^ 2 * p⁻¹ = x₁ ^ 2 by rw [hcomm]; group]
        exact Subgroup.subset_closure (by simp)
      ·
        rw [h]
        have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
        have hcomm := P_comm_V ha p hp ((x₁ * x₂) ^ 2) hzV
        rw [show p * (x₁ * x₂) ^ 2 * p⁻¹ = (x₁ * x₂) ^ 2 by rw [hcomm]; group]
        exact Subgroup.subset_closure (by simp)
    have hcl := conj_mem_closure (S := ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G)) (g := p) hgen
    intro k hk
    simpa only [ctxX] using hcl k hk
  exact ha.X_not_normal_P ⟨hX_le_P, hconj⟩

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
