module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

private instance ffOutFF6PD8_decD8 : DecidablePred (· ∈ ffD8p) := fun σ =>
  decidable_of_iff' (σ * ffD8g = ffD8g * σ) (mem_ffD8p_iff σ)

@[expose] def ffAct (σ : Equiv.Perm (Fin 5)) (J : Finset (Fin 5)) : Finset (Fin 5) :=
  J.map σ.toEmbedding

@[expose] def ffRot : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3

@[expose] def ffV4g : Finset (Equiv.Perm (Fin 5)) :=
  {1, Equiv.swap 0 2, Equiv.swap 1 3, Equiv.swap 0 2 * Equiv.swap 1 3}

@[expose] def ffE0s : Finset (Finset (Fin 5)) := {∅, {0, 2}, {1, 3}, {0, 1, 2, 3}}

theorem ffAct_mul (σ τ : Equiv.Perm (Fin 5)) (J : Finset (Fin 5)) :
    ffAct (σ * τ) J = ffAct σ (ffAct τ J) := by
  simp only [ffAct]
  rw [Finset.map_map]
  congr 1

theorem ffAct_one (J : Finset (Fin 5)) : ffAct 1 J = J := by
  rw [ffAct]
  rw [show Equiv.toEmbedding (1 : Equiv.Perm (Fin 5)) = Function.Embedding.refl (Fin 5) from rfl]
  exact Finset.map_refl

theorem ffAct_card (σ : Equiv.Perm (Fin 5)) (J : Finset (Fin 5)) : (ffAct σ J).card = J.card := by
  rw [ffAct, Finset.card_map]

theorem ffRot_mem_ffD8p : ffRot ∈ ffD8p := by
  rw [mem_ffD8p_iff]
  decide +kernel

theorem ffRot_mul_self_ne_one : ffRot * ffRot ≠ 1 := by
  decide +kernel

theorem ffD8p_elemAb_card_le (R : Subgroup (Equiv.Perm (Fin 5))) (hR : R ≤ ffD8p)
    (h2 : ∀ r ∈ R, r * r = 1) : Nat.card R ≤ 4 := by
  have hdvd : Nat.card R ∣ 8 := by
    have h := Subgroup.card_dvd_of_le hR
    rwa [ffD8p_card] at h
  have hdvd' : Nat.card R ∣ 2 ^ 3 := by simpa using hdvd
  obtain ⟨k, hk, hkR⟩ :=
    (Nat.dvd_prime_pow (p := 2) (by norm_num : Nat.Prime 2) (m := 3)).mp hdvd' 
  interval_cases k
  · rw [hkR]; norm_num
  · rw [hkR]; norm_num
  · rw [hkR]; norm_num
  · exfalso
    have htop : R = ffD8p :=
      Subgroup.eq_of_le_of_card_ge hR (by rw [hkR, ffD8p_card]; norm_num)
    exact ffRot_mul_self_ne_one (h2 ffRot (by rw [htop]; exact ffRot_mem_ffD8p))

theorem ffD8_fixed_orbit {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ ffD8p) (h1 : σ ≠ 1)
    (h2 : σ * σ = 1) {J : Finset (Fin 5)} (hJ : Even J.card)
    (h : ∀ τ ∈ ffD8p, ffAct σ (ffAct τ J) = ffAct τ J) :
    J = ∅ ∨ J = {0, 1, 2, 3} ∨ (σ ∈ ffV4g ∧ J ∈ ffE0s) := by
  revert σ J
  decide +kernel

theorem ffD8_invariant_even {J : Finset (Fin 5)} (hJ : Even J.card)
    (h : ∀ τ ∈ ffD8p, ffAct τ J = J) : J = ∅ ∨ J = {0, 1, 2, 3} := by
  revert J
  decide +kernel

theorem ffE0s_card : ffE0s.card = 4 := by
  decide +kernel

theorem ffE0s_act {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ ffD8p) {J : Finset (Fin 5)}
    (hJ : J ∈ ffE0s) : ffAct σ J ∈ ffE0s := by
  revert σ J
  decide +kernel

theorem ff_coset_E0 {J : Finset (Fin 5)} (hJ : Even J.card)
    (h02 : ffAct (Equiv.swap 0 2) J = J)
    (h : symmDiff (ffAct (Equiv.swap 1 3) J) (ffAct ffRot J) ∈ ffE0s) : J ∈ ffE0s := by
  revert J
  decide +kernel

theorem ff_perm_eq_one_of_fix_even (σ : Equiv.Perm (Fin 5))
    (h : ∀ J : Finset (Fin 5), Even J.card → ffAct σ J = J) : σ = 1 := by
  revert σ
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
