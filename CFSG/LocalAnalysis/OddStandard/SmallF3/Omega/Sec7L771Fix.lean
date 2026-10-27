module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L77Stab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Comb5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private instance sec7l771_decidableIsEvenVec (v : Fin 5 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private def sec7l771_Sv (v : Fin 5 → ZMod 2) : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {σ | permVec σ v = v}
  one_mem' := sec7l77_permVec_one v
  mul_mem' := by
    intro σ τ hσ hτ
    show permVec (σ * τ) v = v
    rw [← sec7l77_permVec_mul, hτ, hσ]
  inv_mem' := by
    intro σ hσ
    have h := sec7l77_permVec_mul σ⁻¹ σ v
    rw [inv_mul_cancel, sec7l77_permVec_one, hσ] at h
    exact h

private theorem sec7l771_card_Sv_wt2_aux :
    ∀ v : Fin 5 → ZMod 2, IsEvenVec v → vecWeight v = 2 →
      Fintype.card {σ : Equiv.Perm (Fin 5) // permVec σ v = v} = 12 := by
  decide +kernel

private theorem sec7l771_card_Sv_inter_aux :
    ∀ v w : Fin 5 → ZMod 2, IsEvenVec v → IsEvenVec w → vecWeight v = 4 → vecWeight w = 4 →
      v ≠ w → Fintype.card {σ : Equiv.Perm (Fin 5) //
        permVec σ v = v ∧ permVec σ w = w} = 6 := by
  decide +kernel

private theorem sec7l771_card_Sv_wt2 (v : Fin 5 → ZMod 2) (hv : IsEvenVec v)
    (h2 : vecWeight v = 2) : Nat.card (sec7l771_Sv v) = 12 := by
  have hcard : Nat.card (sec7l771_Sv v) =
      Nat.card {σ : Equiv.Perm (Fin 5) // permVec σ v = v} :=
    Nat.card_congr (Equiv.refl _)
  rw [hcard, Nat.card_eq_fintype_card]
  exact sec7l771_card_Sv_wt2_aux v hv h2

private theorem sec7l771_card_Sv_inter (v w : Fin 5 → ZMod 2) (hv : IsEvenVec v)
    (hw : IsEvenVec w) (h4v : vecWeight v = 4) (h4w : vecWeight w = 4) (hne : v ≠ w) :
    Nat.card ↥(sec7l771_Sv v ⊓ sec7l771_Sv w) = 6 := by
  have hcard : Nat.card ↥(sec7l771_Sv v ⊓ sec7l771_Sv w) =
      Nat.card {σ : Equiv.Perm (Fin 5) // permVec σ v = v ∧ permVec σ w = w} :=
    Nat.card_congr (Equiv.refl _)
  rw [hcard, Nat.card_eq_fintype_card]
  exact sec7l771_card_Sv_inter_aux v w hv hw h4v h4w hne

private theorem sec7l771_weight4_aux :
    ∀ w : Fin 5 → ZMod 2, vecWeight w = 4 →
      ∃ p₀ : Fin 5, ∀ i, w i = if i = p₀ then 0 else 1 := by
  decide +kernel

private theorem sec7l771_card_W_aux :
    ∀ p₀ : Fin 5,
      (Finset.univ.filter (fun v : Fin 5 → ZMod 2 => IsEvenVec v ∧ v p₀ = 0)).card = 8 := by
  decide +kernel

private theorem sec7l771_exists_cycle_aux :
    ∀ p₀ : Fin 5, ∃ σ : Equiv.Perm (Fin 5), σ p₀ = p₀ ∧ σ ^ 3 = 1 ∧ σ ≠ 1 ∧
      ∀ v : Fin 5 → ZMod 2, IsEvenVec v → v p₀ = 0 → permVec σ v = v →
        v = 0 ∨ ∀ i, v i = if i = p₀ then 0 else 1 := by
  intro p₀
  fin_cases p₀ <;> decide +kernel

private theorem sec7l771_wt2_cases :
    ∀ (p₀ : Fin 5) (v : Fin 5 → ZMod 2), IsEvenVec v → v p₀ = 0 → vecWeight v = 2 →
      ∃ j k : Fin 5, j ≠ k ∧ j ≠ p₀ ∧ k ≠ p₀ ∧
        v = fun i => if i = j ∨ i = k then 1 else 0 := by
  decide +kernel

private theorem sec7l771_wt2_pair :
    ∀ p₀ j k : Fin 5, j ≠ k → j ≠ p₀ → k ≠ p₀ →
      ∃ u : Fin 5 → ZMod 2, ∃ σ : Equiv.Perm (Fin 5),
        IsEvenVec u ∧ σ p₀ = p₀ ∧ σ ^ 3 = 1 ∧
        ∀ i, (if i = j ∨ i = k then 1 else 0) = (u + permVec σ u) i := by
  intro p₀ j k
  fin_cases p₀ <;> fin_cases j <;> fin_cases k <;> decide +kernel

private theorem sec7l771_wt4_split :
    ∀ (p₀ : Fin 5) (v : Fin 5 → ZMod 2), IsEvenVec v → v p₀ = 0 → vecWeight v = 4 →
      ∃ j k l m : Fin 5, j ≠ k ∧ l ≠ m ∧ j ≠ p₀ ∧ k ≠ p₀ ∧ l ≠ p₀ ∧ m ≠ p₀ ∧
        v = (fun i => if i = j ∨ i = k then 1 else 0) +
            (fun i => if i = l ∨ i = m then 1 else 0) := by
  decide +kernel

theorem sec7l771_fix_even (H : Subgroup (Equiv.Perm (Fin 5))) (hH : 8 ∣ Nat.card H)
    {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hvH : ∀ σ ∈ H, permVec σ v = v) (hwH : ∀ σ ∈ H, permVec σ w = w) :
    vecWeight v = 4 ∧ v = w := by
  have hvH' : H ≤ sec7l771_Sv v := fun σ hσ => hvH σ hσ
  have hwH' : H ≤ sec7l771_Sv w := fun σ hσ => hwH σ hσ
  have hwt4v : vecWeight v = 4 := by
    rcases even_weight_cases_five v hv with h0 | h2 | h4
    · exact absurd h0 hv0
    · have hdvd := hH.trans (Subgroup.card_dvd_of_le hvH')
      have h12 := sec7l771_card_Sv_wt2 v hv h2
      rw [h12] at hdvd
      have hnot : ¬ (8 ∣ 12) := by norm_num
      exact absurd hdvd hnot
    · exact h4
  refine ⟨hwt4v, ?_⟩
  by_contra hne
  have hwt4w : vecWeight w = 4 := by
    rcases even_weight_cases_five w hw with h0 | h2 | h4
    · exact absurd h0 hw0
    · have hdvd := hH.trans (Subgroup.card_dvd_of_le hwH')
      have h12 := sec7l771_card_Sv_wt2 w hw h2
      rw [h12] at hdvd
      have hnot : ¬ (8 ∣ 12) := by norm_num
      exact absurd hdvd hnot
    · exact h4
  have hle : H ≤ sec7l771_Sv v ⊓ sec7l771_Sv w := le_inf hvH' hwH'
  have hdvd := hH.trans (Subgroup.card_dvd_of_le hle)
  have h6 := sec7l771_card_Sv_inter v w hv hw hwt4v hwt4w hne
  rw [h6] at hdvd
  have hnot : ¬ (8 ∣ 6) := by norm_num
  exact absurd hdvd hnot

theorem sec7l771_weight4 {w : Fin 5 → ZMod 2} (h4 : vecWeight w = 4) :
    ∃ p₀ : Fin 5, ∀ i, w i = if i = p₀ then 0 else 1 :=
  sec7l771_weight4_aux w h4

theorem sec7l771_card_W (p₀ : Fin 5) :
    Nat.card {v : Fin 5 → ZMod 2 // IsEvenVec v ∧ v p₀ = 0} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact sec7l771_card_W_aux p₀

theorem sec7l771_exists_cycle (p₀ : Fin 5) :
    ∃ σ : Equiv.Perm (Fin 5), σ p₀ = p₀ ∧ σ ^ 3 = 1 ∧ σ ≠ 1 ∧
      ∀ v : Fin 5 → ZMod 2, IsEvenVec v → v p₀ = 0 → permVec σ v = v →
        v = 0 ∨ v = fun i => if i = p₀ then 0 else 1 := by
  obtain ⟨σ, h1, h2, h3, h4⟩ := sec7l771_exists_cycle_aux p₀
  refine ⟨σ, h1, h2, h3, fun v hv hv0 hfix => ?_⟩
  rcases h4 v hv hv0 hfix with h | h
  · exact Or.inl h
  · exact Or.inr (funext h)

theorem sec7l771_W_gen (p₀ : Fin 5) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hv0 : v p₀ = 0) :
    ∃ (u₁ u₂ : Fin 5 → ZMod 2) (σ₁ σ₂ : Equiv.Perm (Fin 5)), IsEvenVec u₁ ∧ IsEvenVec u₂ ∧
      σ₁ p₀ = p₀ ∧ σ₂ p₀ = p₀ ∧ σ₁ ^ 3 = 1 ∧ σ₂ ^ 3 = 1 ∧
      v = (u₁ + permVec σ₁ u₁) + (u₂ + permVec σ₂ u₂) := by
  rcases even_weight_cases_five v hv with h0 | h2 | h4
  · subst h0
    refine ⟨0, 0, 1, 1, by simp [IsEvenVec], by simp [IsEvenVec], rfl, rfl,
      by simp, by simp, ?_⟩
    simp [sec7l77_permVec_one]
  · obtain ⟨j, k, hjk, hjp, hkp, hvjk⟩ := sec7l771_wt2_cases p₀ v hv hv0 h2
    obtain ⟨u, σ, hu, hσp, hσ3, hdec⟩ := sec7l771_wt2_pair p₀ j k hjk hjp hkp
    refine ⟨u, 0, σ, 1, hu, by simp [IsEvenVec], hσp, rfl, hσ3, by simp, ?_⟩
    have hdec' : (fun i => if i = j ∨ i = k then 1 else 0) = u + permVec σ u := funext hdec
    rw [hvjk, hdec']
    simp [sec7l77_permVec_one]
  · obtain ⟨j, k, l, m, hjk, hlm, hjp, hkp, hlp, hmp, hsplit⟩ :=
      sec7l771_wt4_split p₀ v hv hv0 h4
    obtain ⟨u₁, σ₁, hu₁, hσ₁p, hσ₁3, h₁⟩ := sec7l771_wt2_pair p₀ j k hjk hjp hkp
    obtain ⟨u₂, σ₂, hu₂, hσ₂p, hσ₂3, h₂⟩ := sec7l771_wt2_pair p₀ l m hlm hlp hmp
    refine ⟨u₁, u₂, σ₁, σ₂, hu₁, hu₂, hσ₁p, hσ₂p, hσ₁3, hσ₂3, ?_⟩
    have h₁' : (fun i => if i = j ∨ i = k then 1 else 0) = u₁ + permVec σ₁ u₁ := funext h₁
    have h₂' : (fun i => if i = l ∨ i = m then 1 else 0) = u₂ + permVec σ₂ u₂ := funext h₂
    rw [hsplit, h₁', h₂']

end CFSG.OddStandard.SmallF3.Omega
