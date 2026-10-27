module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAP

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 K K₂ : Subgroup Γ}

theorem y7c_K₂_comm_J (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hKt : conjSub t K = K) (hK₂ : CFSG.IsComponent K₂)
    (hne : K₂ ≠ K) : ∀ x ∈ K₂, ∀ j ∈ J, x * j = j * x := by
  have hJK' : J ≤ K := by simpa [hKt] using hJK
  intro x hx j hj
  exact y7c_comm_of_components hK₂ hK hne x hx j (hJK' hj)

theorem y7c_M6_le_K (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hKt : conjSub t K = K) (hK₂ : CFSG.IsComponent K₂)
    (hne : K₂ ≠ K) (hall : ∀ g : Γ, conjSub g K = K ∨ conjSub g K = K₂) : M6 ≤ K := by
  have hJK' : J ≤ K := by simpa [hKt] using hJK
  have hcomm : ∀ x ∈ K₂, ∀ k ∈ K, x * k = k * x :=
    y7c_comm_of_components hK₂ hK hne
  have hN_le : Subgroup.normalClosure (J : Set Γ) ≤ K ⊔ K₂ := by
    unfold Subgroup.normalClosure
    refine (Subgroup.closure_le (K := K ⊔ K₂)).mpr ?_
    intro x hx
    obtain ⟨j, hj, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    rw [← hc]
    have hmem : c * j * c⁻¹ ∈ conjSub c K :=
      y7c_mul_mem_conjSub (g := c) (y := j) (Y := K) (hJK' hj)
    rcases hall c with hcK | hcK
    · rw [hcK] at hmem
      exact (le_sup_left : K ≤ K ⊔ K₂) hmem
    · rw [hcK] at hmem
      exact (le_sup_right : K₂ ≤ K ⊔ K₂) hmem
  have hM6_le_sup : M6 ≤ K ⊔ K₂ :=
    calc M6 ≤ P := by rw [c.P_sup]; exact le_sup_left
      _ ≤ Subgroup.normalClosure (J : Set Γ) := y7c_P_le_N c
      _ ≤ K ⊔ K₂ := hN_le
  have hK₂_norm : K₂ ≤ Subgroup.normalizer (K : Set Γ) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    rw [Subgroup.commutator_le]
    intro x hx k hk
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcomm x hx k hk)]
    exact Subgroup.one_mem K
  have hnorm : (K ⊔ K₂ : Subgroup Γ) ≤ Subgroup.normalizer (K : Set Γ) :=
    sup_le (Subgroup.le_normalizer : K ≤ Subgroup.normalizer (K : Set Γ)) hK₂_norm
  have hcomm_K : ⁅J, M6⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro j hj m hm
    have hm_norm : m ∈ Subgroup.normalizer (K : Set Γ) := hnorm (hM6_le_sup hm)
    have hiff : j⁻¹ ∈ K ↔ m * j⁻¹ * m⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff (H := K)).mp hm_norm j⁻¹
    have hmem : m * j⁻¹ * m⁻¹ ∈ K := hiff.mp (K.inv_mem (hJK' hj))
    have hjeq : ⁅j, m⁆ = j * (m * j⁻¹ * m⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [hjeq]
    exact K.mul_mem (hJK' hj) hmem
  calc M6 ≤ ⁅J, M6⁆ := c.M6_gen
    _ ≤ K := hcomm_K

theorem y7c_cent_K₂_le_Q (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hKt : conjSub t K = K) (hK₂ : CFSG.IsComponent K₂)
    (hne : K₂ ≠ K) {x : Γ} (hx : x ∈ K₂) (hxt : x * t = t * x) : x ∈ Q := by
  obtain ⟨j, hj, q, hq, rfl⟩ := c.cent x hxt
  have hcommJ := y7c_K₂_comm_J c hK hJK hKt hK₂ hne
  have hxq : ∀ y ∈ J, (j * q) * y = y * (j * q) := fun y hy => hcommJ (j * q) hx y hy
  have hjcent : ∀ y ∈ J, j * y = y * j := by
    intro y hy
    have h1 : (j * q) * y = y * (j * q) := hxq y hy
    have h2 : q * y = y * q := c.Q_J q hq y hy
    have h3 : (j * y) * q = (y * j) * q := by
      calc (j * y) * q = j * (y * q) := by rw [mul_assoc]
        _ = j * (q * y) := by rw [h2]
        _ = (j * q) * y := by rw [mul_assoc]
        _ = y * (j * q) := h1
        _ = (y * j) * q := by rw [mul_assoc]
    exact mul_right_cancel h3
  have hj1 : j = 1 := y7c_J_center c hj hjcent
  rw [hj1, one_mul]
  exact hq

end CFSG.OddStandard.HigherRank.YamadaG23
