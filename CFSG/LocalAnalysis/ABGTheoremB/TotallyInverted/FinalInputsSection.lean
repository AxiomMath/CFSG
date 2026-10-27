module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalLemmas1
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LinearAlgebra.SL2MinimalFaithfulSection

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem eq_p_of_dvd_q (hσ : σ.IsValid) (Δ : Data σ r) (h : r ∣ σ.q) : r = σ.p :=
  (Nat.prime_dvd_prime_iff_eq Δ.prime hσ.p_prime).mp (Δ.prime.dvd_of_dvd_pow h)

section Q

variable (Δ : Data σ r) (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q)
include hδq

theorem card_J : Nat.card Δ.J = σ.q * (σ.q ^ 2 - 1) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Δ.J_sl2 (J_inf_ON Δ hδq)
  rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard]

theorem Q_zero_sup_Qs_zero : Δ.Q 0 ⊔ Δ.Qs 0 = Δ.J := by
  have h := J_conj_eq Δ hδq 0
  rw [Fin.val_zero, pow_zero, conjSub_one] at h
  exact h.symm

theorem Q_zero_inf_Qs_zero : Δ.Q 0 ⊓ Δ.Qs 0 = ⊥ := by
  have hC : σ.C ≤ Subgroup.normalizer ((Δ.Q 0 ⊓ Δ.Qs 0 : Subgroup G) : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff.mp ((Δ.Q_C 0).1 hc) g,
      Subgroup.mem_normalizer_iff.mp ((Δ.Q_C 0).2 hc) g]
  rcases Q_irred Δ hδq 0 inf_le_left hC with h | h
  · exact h
  · exfalso
    apply Q_ne_Qs Δ hδq 0
    have hle : Δ.Q 0 ≤ Δ.Qs 0 := by
      rw [← h]
      exact inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_Q Δ hδq, card_Qs Δ hδq])

end Q

theorem abg_II_4_18_of (hσ : σ.IsValid) (Δ : Data σ r) : ABG_II_4_18 Δ := by
  intro hδq Y Z hZY hYZ hJY hJZ hcomm hexp hcard hfaith Q hQ
  have hJ := card_J Δ hδq
  have hinf := Q_zero_inf_Qs_zero Δ hδq
  have hsup := Q_zero_sup_Qs_zero Δ hδq
  obtain rfl := eq_p_of_dvd_q hσ Δ hδq.2
  rcases hQ with rfl | rfl
  · exact CFSG.SL2MinimalFaithful.card_section_fixed_le hσ.p_prime hσ.p_ne_two hσ.one_le_f hJ
      (Q_zero_le_J Δ) (Qs_zero_le_J Δ) (card_Q Δ hδq 0) (card_Qs Δ hδq 0) hinf hsup hZY hYZ
      hJY hJZ hcomm hexp hcard hfaith
  · exact CFSG.SL2MinimalFaithful.card_section_fixed_le hσ.p_prime hσ.p_ne_two hσ.one_le_f hJ
      (Qs_zero_le_J Δ) (Q_zero_le_J Δ) (card_Qs Δ hδq 0) (card_Q Δ hδq 0)
      (by rw [inf_comm]; exact hinf) (by rw [sup_comm]; exact hsup) hZY hYZ hJY hJZ hcomm hexp
      hcard hfaith

end CFSG.ABGTheoremB.TotallyInverted.Sec11
