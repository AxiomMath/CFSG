module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapReps

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

private theorem u_liftS8_apply_castLE (ρ : Perm (Fin 8)) (a : Fin 8) :
    liftS8 ρ (Fin.castLE (by norm_num : 8 ≤ 10) a) =
      Fin.castLE (by norm_num : 8 ≤ 10) (ρ a) := by
  rw [liftS8, Equiv.Perm.viaEmbeddingHom_apply, ← Fin.coe_castLEEmb,
    Equiv.Perm.viaEmbedding_apply]

private theorem u_exists_sq_of_isConj {ρ s : Perm (Fin 8)} (h : IsConj ρ s)
    {γ : Perm (Fin 8)} (hγ : γ * γ = s) : ∃ r : Perm (Fin 8), r * r = ρ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨c⁻¹ * γ * c, ?_⟩
  have hρ : ρ = c⁻¹ * s * c := by rw [← hc]; group
  rw [hρ, ← hγ]
  group

theorem exists_sq_of_sign_eq_one {ρ : Perm (Fin 8)} (h2 : ρ * ρ = 1) (hs : sign ρ = 1) :
    ∃ r : Perm (Fin 8), r * r = ρ := by
  have hct : ρ.cycleType = Multiset.replicate (Multiset.card ρ.cycleType) 2 :=
    cycleType_eq_replicate_two h2
  have hle : Multiset.card ρ.cycleType ≤ 4 := by
    have h := card_support_eq_two_mul_card_cycleType h2
    have hcard : ρ.support.card ≤ 8 := by simpa using Finset.card_le_univ ρ.support
    omega
  have heven : Even (Multiset.card ρ.cycleType) := by
    have h := hs
    rw [Equiv.Perm.sign_of_cycleType, hct, Multiset.sum_replicate, Multiset.card_replicate,
      smul_eq_mul, pow_add, pow_mul, Int.units_pow_two, one_mul] at h
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).1 h
  obtain ⟨j, hj⟩ := heven
  have hjle : j ≤ 2 := by omega
  interval_cases j
  · have hk : Multiset.card ρ.cycleType = 0 := by omega
    exact ⟨1, by rw [show ρ = 1 from (Equiv.Perm.card_cycleType_eq_zero).1 hk, mul_one]⟩
  · have hk : Multiset.card ρ.cycleType = 2 := by omega
    have hconj : IsConj ρ r₂' := by
      rw [Equiv.Perm.isConj_iff_cycleType_eq, hct, hk]
      rw [cycleType_eq_replicate_two r₂'_mul_self, card_cycleType_r₂']
    exact u_exists_sq_of_isConj hconj (γ := swap 0 2 * swap 2 1 * swap 1 3) (by decide)
  · have hk : Multiset.card ρ.cycleType = 4 := by omega
    have hconj : IsConj ρ ρ₄' := by
      rw [Equiv.Perm.isConj_iff_cycleType_eq, hct, hk]
      rw [cycleType_eq_replicate_two ρ₄'_mul_self, card_cycleType_ρ₄']
    exact u_exists_sq_of_isConj hconj
      (γ := (swap 0 2 * swap 2 1 * swap 1 3) * (swap 4 6 * swap 6 5 * swap 5 7))
      (by decide)

theorem exists_conj_swap_mul {ρ : Perm (Fin 8)} (h2 : ρ * ρ = 1) :
    ∃ (τ ρ' : Perm (Fin 8)) (i : Fin 2), ρ' 0 = 0 ∧ ρ' 1 = 1 ∧
      τ * ρ * τ⁻¹ = (swap 0 1) ^ (i : ℕ) * ρ' := by
  by_cases hρ1 : ρ = 1
  · subst hρ1
    exact ⟨1, 1, 0, by simp, by simp, by simp⟩
  · obtain ⟨a, ha⟩ : ∃ a : Fin 8, ρ a ≠ a := by
      by_contra h
      push_neg at h
      exact hρ1 (Equiv.ext h)
    have hρρ : ∀ x : Fin 8, ρ (ρ x) = x := by
      intro x
      have := congrArg (fun f : Perm (Fin 8) => f x) h2
      simpa using this
    set b : Fin 8 := ρ a with hb
    have hρb : ρ b = a := by rw [hb]; exact hρρ a
    have hne : a ≠ b := by rw [hb]; exact Ne.symm ha
    set τ0 : Perm (Fin 8) := swap a 0 with hτ0
    have hτ0a : τ0 a = 0 := by rw [hτ0]; exact Equiv.swap_apply_left a 0
    have hτ0b : τ0 b ≠ 0 := by
      rw [hτ0]
      intro h
      have h' : Equiv.swap a 0 b = Equiv.swap a 0 a := by
        rw [h, Equiv.swap_apply_left]
      exact hne ((Equiv.swap a 0).injective h').symm
    set τ1 : Perm (Fin 8) := swap (τ0 b) 1 with hτ1
    have hτ1_0 : τ1 0 = 0 := by
      rw [hτ1]
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hτ0b) (by decide : (0 : Fin 8) ≠ 1)
    have hτ1_b : τ1 (τ0 b) = 1 := by rw [hτ1]; exact Equiv.swap_apply_left (τ0 b) 1
    set τ : Perm (Fin 8) := τ1 * τ0 with hτ
    have hτa : τ a = 0 := by rw [hτ, Perm.mul_apply, hτ0a, hτ1_0]
    have hτb : τ b = 1 := by rw [hτ, Perm.mul_apply, hτ1_b]
    have hτinv0 : τ⁻¹ 0 = a := by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      exact hτa.symm
    have hτinv1 : τ⁻¹ 1 = b := by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      exact hτb.symm
    set ρ'' : Perm (Fin 8) := τ * ρ * τ⁻¹ with hρ''
    have hρ''0 : ρ'' 0 = 1 := by
      rw [hρ'', Perm.mul_apply, Perm.mul_apply, hτinv0, ← hb, hτb]
    have hρ''1 : ρ'' 1 = 0 := by
      rw [hρ'', Perm.mul_apply, Perm.mul_apply, hτinv1, hρb, hτa]
    set ρ' : Perm (Fin 8) := swap 0 1 * ρ'' with hρ'
    have hρ'0 : ρ' 0 = 0 := by rw [hρ', Perm.mul_apply, hρ''0, Equiv.swap_apply_right]
    have hρ'1 : ρ' 1 = 1 := by rw [hρ', Perm.mul_apply, hρ''1, Equiv.swap_apply_left]
    refine ⟨τ, ρ', ⟨1, by decide⟩, hρ'0, hρ'1, ?_⟩
    rw [← hρ'', pow_one, hρ', ← mul_assoc, Equiv.swap_mul_self, one_mul]

theorem exists_conj_of_sign_neg_one {ρ : Perm (Fin 8)} (h2 : ρ * ρ = 1) (hs : sign ρ = -1) :
    ∃ (c : Perm (Fin 10)) (ρ' : Perm (Fin 8)), ρ' * ρ' = 1 ∧ sign ρ' = 1 ∧
      c * liftS8 ρ * c⁻¹ = τ₀ * liftS8 ρ' := by
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, Equiv.Perm.sign_one] at hs
    exact absurd hs (by decide)
  obtain ⟨a, ha⟩ : ∃ a : Fin 8, ρ a ≠ a := by
    by_contra h
    push_neg at h
    exact hρ1 (Equiv.ext h)
  have hρρ : ∀ x : Fin 8, ρ (ρ x) = x := by
    intro x
    have := congrArg (fun f : Perm (Fin 8) => f x) h2
    simpa using this
  set b : Fin 8 := ρ a with hb
  have hρb : ρ b = a := by rw [hb]; exact hρρ a
  have hne : a ≠ b := by rw [hb]; exact Ne.symm ha
  set ρ' : Perm (Fin 8) := swap a b * ρ with hρ'
  have hcomm : ρ * swap a b = swap a b * ρ := by
    rw [Equiv.mul_swap_eq_swap_mul, ← hb, hρb, Equiv.swap_comm]
  have hρ'mul : ρ' * ρ' = 1 := by
    rw [hρ']
    calc (swap a b * ρ) * (swap a b * ρ)
        = swap a b * (ρ * swap a b) * ρ := by group
      _ = swap a b * (swap a b * ρ) * ρ := by rw [hcomm]
      _ = (swap a b * swap a b) * (ρ * ρ) := by group
      _ = 1 := by rw [Equiv.swap_mul_self, h2, mul_one]
  have hfixa : ρ' a = a := by
    rw [hρ', Perm.mul_apply, ← hb, Equiv.swap_apply_right]
  have hfixb : ρ' b = b := by
    rw [hρ', Perm.mul_apply, hρb, Equiv.swap_apply_left]
  have hsign' : sign ρ' = 1 := by
    rw [hρ', Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, hs]
    exact Int.units_mul_self (-1)
  set a' : Fin 10 := Fin.castLE (by norm_num : 8 ≤ 10) a with ha'
  set b' : Fin 10 := Fin.castLE (by norm_num : 8 ≤ 10) b with hb'
  have ha'lt : (a' : ℕ) < 8 := by rw [ha']; exact a.isLt
  have ha'b' : a' ≠ b' := by
    rw [ha', hb']
    exact fun h => hne (Fin.castLE_injective (by norm_num : 8 ≤ 10) h)
  have ha'9 : a' ≠ 9 := by
    intro h
    have hv : (a' : ℕ) = 9 := by rw [h]; rfl
    omega
  have hfix_a' : liftS8 ρ' a' = a' := by
    rw [ha', u_liftS8_apply_castLE, hfixa]
  have hfix_b' : liftS8 ρ' b' = b' := by
    rw [hb', u_liftS8_apply_castLE, hfixb]
  set c : Perm (Fin 10) := swap a' 8 * swap b' 9 with hc
  have hcomm1 : swap a' 8 * liftS8 ρ' = liftS8 ρ' * swap a' 8 :=
    swap_comm_of_fixed hfix_a' (liftS8_apply_eight ρ')
  have hcomm2 : swap b' 9 * liftS8 ρ' = liftS8 ρ' * swap b' 9 :=
    swap_comm_of_fixed hfix_b' (liftS8_apply_nine ρ')
  have hc_comm : c * liftS8 ρ' = liftS8 ρ' * c := by
    calc c * liftS8 ρ' = swap a' 8 * (swap b' 9 * liftS8 ρ') := by rw [hc]; group
      _ = swap a' 8 * (liftS8 ρ' * swap b' 9) := by rw [hcomm2]
      _ = (swap a' 8 * liftS8 ρ') * swap b' 9 := by group
      _ = (liftS8 ρ' * swap a' 8) * swap b' 9 := by rw [hcomm1]
      _ = liftS8 ρ' * c := by rw [hc]; group
  have hca' : c a' = 8 := by
    rw [hc, Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne ha'b' ha'9,
      Equiv.swap_apply_left]
  have hcb' : c b' = 9 := by
    rw [hc, Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm ha'9) (by decide : (9 : Fin 10) ≠ 8)]
  have hswapconj : c * swap a' b' * c⁻¹ = τ₀ := by
    rw [← Equiv.swap_apply_apply c a' b', hca', hcb']
    rfl
  have hρ_decomp : ρ = swap a b * ρ' := by
    rw [hρ', ← mul_assoc, Equiv.swap_mul_self, one_mul]
  have hlift : liftS8 ρ = swap a' b' * liftS8 ρ' := by
    rw [hρ_decomp, map_mul, liftS8_swap]
  refine ⟨c, ρ', hρ'mul, hsign', ?_⟩
  rw [hlift]
  calc c * (swap a' b' * liftS8 ρ') * c⁻¹
      = (c * swap a' b' * c⁻¹) * (c * liftS8 ρ' * c⁻¹) := by group
    _ = τ₀ * (c * liftS8 ρ' * c⁻¹) := by rw [hswapconj]
    _ = τ₀ * liftS8 ρ' := by rw [hc_comm]; group

theorem liftS8_swap_zero_one : liftS8 (swap (0 : Fin 8) 1) = swap (0 : Fin 10) 1 := by
  rw [liftS8_swap]
  congr 1 <;> exact Fin.ext rfl

theorem liftS8_apply_zero {ρ : Perm (Fin 8)} (h0 : ρ 0 = 0) : liftS8 ρ 0 = 0 := by
  have h : (0 : Fin 10) = Fin.castLE (by norm_num : 8 ≤ 10) (0 : Fin 8) := Fin.ext rfl
  rw [h, u_liftS8_apply_castLE, h0]

theorem liftS8_apply_one {ρ : Perm (Fin 8)} (h1 : ρ 1 = 1) : liftS8 ρ 1 = 1 := by
  have h : (1 : Fin 10) = Fin.castLE (by norm_num : 8 ≤ 10) (1 : Fin 8) := Fin.ext rfl
  rw [h, u_liftS8_apply_castLE, h1]

end CFSG.OddStandard.AltStdSec.SwapPartner
