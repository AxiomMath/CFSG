module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR3A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IK0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {N Q Y V V' B K : Subgroup X} {ρ t τ l : X} [N.Normal]

private lemma zik_Q_comm (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ a ∈ Q.map (z4iπ N), ∀ b ∈ Q.map (z4iπ N), a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  simp only [← map_mul, h.Q_comm a ha b hb]

private lemma zik_card_Q (h : Z4IData N Q Y V V' B K ρ t τ l) :
    Nat.card (Q.map (z4iπ N)) = 64 := by
  rw [z4i_card_map N h.odd_N h.isPGroup_Q, h.card_Q]

private lemma zik_cent_Q (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ g : X ⧸ N, (∀ q ∈ Q.map (z4iπ N), g * q = q * g) → g ∈ Q.map (z4iπ N) := by
  intro g hg
  obtain ⟨g₀, rfl⟩ := z4iπ_surjective N g
  refine (z4iπ_mem_map_iff N).mpr (h.cent_Q g₀ ?_)
  intro q hq
  exact z4i_commute_of_map N h.Q_inf_N (fun x hx => h.normal_Q g₀ x hx) hq
    (hg (z4iπ N q) (Subgroup.mem_map_of_mem (z4iπ N) hq))

private lemma zik_Q_le_K (h : Z4IData N Q Y V V' B K ρ t τ l) :
    Q.map (z4iπ N) ≤ K.map (z4iπ N) :=
  Subgroup.map_mono h.Q_le_K

private lemma zik_relIndex_K (h : Z4IData N Q Y V V' B K ρ t τ l) :
    (Q.map (z4iπ N)).relIndex (K.map (z4iπ N)) = 4 := by
  rw [Subgroup.relIndex_map_map (z4iπ N) Q K, z4iπ_ker N, sup_eq_left.mpr h.N_le_K,
    h.relIndex_K]

private lemma zik_Q_eq (h : Z4IData N Q Y V V' B K ρ t τ l) :
    Q.map (z4iπ N) = B.map (z4iπ N) ⊔ V'.map (z4iπ N) := by
  rw [← Subgroup.map_sup, ← h.Q_eq]

private lemma zik_B_le_Q (h : Z4IData N Q Y V V' B K ρ t τ l) :
    B.map (z4iπ N) ≤ Q.map (z4iπ N) :=
  Subgroup.map_mono h.B_le_Q

private lemma zik_Y_le_Q (h : Z4IData N Q Y V V' B K ρ t τ l) :
    Y.map (z4iπ N) ≤ Q.map (z4iπ N) :=
  Subgroup.map_mono h.Y_le_Q

private lemma zik_Y_eq (h : Z4IData N Q Y V V' B K ρ t τ l) :
    Y.map (z4iπ N) = V.map (z4iπ N) ⊔ V'.map (z4iπ N) := by
  rw [← Subgroup.map_sup, ← h.Y_eq]

private lemma zik_V_inf_V' (h : Z4IData N Q Y V V' B K ρ t τ l) :
    V.map (z4iπ N) ⊓ V'.map (z4iπ N) = ⊥ := by
  have h1 := z4i_map_inf N h.odd_N h.isPGroup_Q h.V_le_Q h.V'_le_Q
  rw [h.V_inf_V', Subgroup.map_bot] at h1
  exact h1.symm

private lemma zik_card_V (h : Z4IData N Q Y V V' B K ρ t τ l) :
    Nat.card (V.map (z4iπ N)) = 4 := by
  rw [z4i_card_map N h.odd_N (h.isPGroup_Q.to_le h.V_le_Q), h.card_V]

private lemma zik_card_V' (h : Z4IData N Q Y V V' B K ρ t τ l) :
    Nat.card (V'.map (z4iπ N)) = 4 := by
  rw [z4i_card_map N h.odd_N (h.isPGroup_Q.to_le h.V'_le_Q), h.card_V']

private lemma zik_sq_mem_V (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ q ∈ Q.map (z4iπ N), q ^ 2 ∈ V.map (z4iπ N) := by
  rintro _ ⟨q, hq, rfl⟩
  simpa only [map_pow] using Subgroup.mem_map_of_mem (z4iπ N) (h.sq_mem_V q hq)

private lemma zik_K_cent_Y (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ k ∈ K.map (z4iπ N), ∀ y ∈ Y.map (z4iπ N), k * y = y * k := by
  rintro _ ⟨k, hk, rfl⟩ _ ⟨y, hy, rfl⟩
  simp only [← map_mul, h.K_cent_Y k hk y hy]

private lemma zik_comm_KQ (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ k ∈ K.map (z4iπ N), ∀ q ∈ Q.map (z4iπ N),
      k * q * k⁻¹ * q⁻¹ ∈ V.map (z4iπ N) := by
  rintro _ ⟨k, hk, rfl⟩ _ ⟨q, hq, rfl⟩
  simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem (z4iπ N) (h.comm_KQ k hk q hq)

private lemma zik_rho_pow_three (h : Z4IData N Q Y V V' B K ρ t τ l) :
    (z4iπ N ρ) ^ 3 = 1 := by
  have h3 : z4iπ N (ρ ^ 3) = 1 := by rw [h.rho_pow_three, map_one]
  simpa only [map_pow] using h3

private lemma zik_rho_norm (h : Z4IData N Q Y V V' B K ρ t τ l) {A : Subgroup X}
    (hA : ∀ x ∈ A, ρ * x * ρ⁻¹ ∈ A) :
    ∀ x ∈ A.map (z4iπ N), z4iπ N ρ * x * (z4iπ N ρ)⁻¹ ∈ A.map (z4iπ N) := by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem (z4iπ N) (hA x hx)

private lemma zik_rho_fpf_Q (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ q ∈ Q.map (z4iπ N), z4iπ N ρ * q * (z4iπ N ρ)⁻¹ = q → q = 1 := by
  rintro _ ⟨q, hq, rfl⟩ hq'
  have hcomm : z4iπ N ρ * z4iπ N q = z4iπ N q * z4iπ N ρ := by
    have h1 : (z4iπ N ρ * z4iπ N q * (z4iπ N ρ)⁻¹) * z4iπ N ρ =
        z4iπ N q * z4iπ N ρ := by rw [hq']
    calc z4iπ N ρ * z4iπ N q
        = (z4iπ N ρ * z4iπ N q * (z4iπ N ρ)⁻¹) * z4iπ N ρ := by group
      _ = z4iπ N q * z4iπ N ρ := h1
  have hρq : ρ * q = q * ρ :=
    z4i_commute_of_map N h.Q_inf_N h.rho_norm_Q hq hcomm
  have hfix : ρ * q * ρ⁻¹ = q := by rw [hρq]; group
  have hq1 : q = 1 := h.rho_fpf_Q q hq hfix
  rw [hq1, map_one]

private lemma zik_rho_fpf_KQ (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ k ∈ K.map (z4iπ N),
      z4iπ N ρ * k * (z4iπ N ρ)⁻¹ * k⁻¹ ∈ Q.map (z4iπ N) → k ∈ Q.map (z4iπ N) := by
  rintro _ ⟨k, hk, rfl⟩ hk'
  refine (z4iπ_mem_map_iff N).mpr (h.rho_fpf_KQ k hk ?_)
  exact (z4iπ_mem_map_iff N).mp (by simpa only [map_mul, map_inv] using hk')

theorem Z4IData.toZIKData (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ZIKData (Q.map (z4iπ N)) (Y.map (z4iπ N)) (V.map (z4iπ N)) (V'.map (z4iπ N))
      (B.map (z4iπ N)) (K.map (z4iπ N)) (z4iπ N ρ) :=
  { Q_comm := zik_Q_comm h
    card_Q := zik_card_Q h
    cent_Q := zik_cent_Q h
    Q_le_K := zik_Q_le_K h
    relIndex_K := zik_relIndex_K h
    Q_eq := zik_Q_eq h
    B_le_Q := zik_B_le_Q h
    Y_le_Q := zik_Y_le_Q h
    Y_eq := zik_Y_eq h
    V_inf_V' := zik_V_inf_V' h
    card_V := zik_card_V h
    card_V' := zik_card_V' h
    sq_mem_V := zik_sq_mem_V h
    K_cent_Y := zik_K_cent_Y h
    comm_KQ := zik_comm_KQ h
    rho_pow_three := zik_rho_pow_three h
    rho_norm_Q := zik_rho_norm h h.rho_norm_Q
    rho_norm_Y := zik_rho_norm h h.rho_norm_Y
    rho_norm_V := zik_rho_norm h h.rho_norm_V
    rho_norm_V' := zik_rho_norm h h.rho_norm_V'
    rho_norm_B := zik_rho_norm h h.rho_norm_B
    rho_norm_K := zik_rho_norm h h.rho_norm_K
    rho_fpf_Q := zik_rho_fpf_Q h
    rho_fpf_KQ := zik_rho_fpf_KQ h }

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
