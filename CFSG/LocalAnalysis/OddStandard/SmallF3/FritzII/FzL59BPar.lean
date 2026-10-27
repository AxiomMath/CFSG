module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BCl

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S T₂ : Subgroup G}
  {x₁ x₂ lam rho tau s u : G} {b : Fin 3 → Fin 2 → G} {T₃ : Subgroup G}

theorem fzl59b_tau_pair (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃)
    (hs : ¬ IsConj t s) : (IsConj t tau ↔ ¬ IsConj t (t * tau)) := by
  have hts := fzl59b_isConj_ts h
  have htt := fzl59b_t_mul_self h
  rcases h.s_cases with h1 | h1
  · rw [← h1]
    exact ⟨fun h' => absurd h' hs, fun h' => absurd hts h'⟩
  · have h2 : tau = t * s := by rw [h1, ← mul_assoc, htt, one_mul]
    rw [← h1, h2]
    exact ⟨fun _ => hs, fun _ => hts⟩

theorem fzl59b_lemmaR (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃)
    (hz : ¬ IsConj t ((x₁ * x₂) ^ 2)) (hs : ¬ IsConj t s) {w : G} (hw : w ∈ invCent t)
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwt : w ≠ t) : (IsConj t w ↔ ¬ IsConj t (t * w)) := by
  have htz := fzl59b_isConj_tz h
  have htt := fzl59b_t_mul_self h
  have hτ := fzl59b_tau_pair h hs
  by_cases hwPL : w ∈ twoCore t ⊔ L
  · obtain ⟨k, hk, hkw⟩ := h.ctx.invol_PL w hwPL hw2 hw1
    rcases hkw with h1 | h1 | h1
    · exfalso
      apply hwt
      have hk' : k * t = t * k := fzl59b_mem_invCent.mp hk
      calc w = k⁻¹ * (k * w * k⁻¹) * k := by group
        _ = k⁻¹ * t * k := by rw [h1]
        _ = k⁻¹ * (k * t) := by rw [mul_assoc, ← hk']
        _ = t := by group
    · obtain ⟨c1, c2⟩ := fzl59b_conj_pair hk h1
      rw [c1, c2]
      exact ⟨fun h' => absurd h' hz, fun h' => absurd htz h'⟩
    · obtain ⟨c1, c2⟩ := fzl59b_conj_pair hk h1
      rw [c1, c2, ← mul_assoc, htt, one_mul]
      exact ⟨fun _ => hz, fun _ => htz⟩
  · have hw2' : w ^ 2 ∈ twoCore t := by
      rw [pow_two, hw2]
      exact one_mem _
    obtain ⟨k, hk, p, hp, hkw⟩ := h.ctx.invol_outer w hw hwPL hw2'
    rcases fzl59b_twoCore_eq h hp with hp1 | hp1
    · rw [hp1, one_mul] at hkw
      obtain ⟨c1, c2⟩ := fzl59b_conj_pair hk hkw
      rw [c1, c2]
      exact hτ
    · rw [hp1] at hkw
      obtain ⟨c1, c2⟩ := fzl59b_conj_pair hk hkw
      rw [c1, c2, ← mul_assoc, htt, one_mul]
      tauto

theorem fzl59b_key (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃)
    (hz : ¬ IsConj t ((x₁ * x₂) ^ 2)) (hs : ¬ IsConj t s) {e f : G} (hf : f * f = 1)
    (hef : e * f = f * e) (hf1 : f ≠ 1) (hne : e ≠ f) (hconj : IsConj t e) :
    (IsConj t f ↔ ¬ IsConj t (e * f)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  obtain ⟨f', hf'⟩ : ∃ f' : G, f' = g⁻¹ * f * g := ⟨_, rfl⟩
  have hfeq : f = g * f' * g⁻¹ := by rw [hf']; group
  have ht_eq : t = g⁻¹ * e * g := by rw [← hg]; group
  have hf'c : f' ∈ invCent t := by
    rw [fzl59b_mem_invCent]
    calc f' * t = (g⁻¹ * f * g) * (g⁻¹ * e * g) := by rw [← ht_eq, hf']
      _ = g⁻¹ * (f * e) * g := by group
      _ = g⁻¹ * (e * f) * g := by rw [hef]
      _ = (g⁻¹ * e * g) * (g⁻¹ * f * g) := by group
      _ = t * f' := by rw [← ht_eq, hf']
  have hf'2 : f' * f' = 1 := by
    calc f' * f' = g⁻¹ * (f * f) * g := by rw [hf']; group
      _ = 1 := by rw [hf, mul_one, inv_mul_cancel]
  have hf'1 : f' ≠ 1 := by
    intro h1
    apply hf1
    rw [hfeq, h1]
    group
  have hf't : f' ≠ t := by
    intro h1
    apply hne
    calc e = g * t * g⁻¹ := hg.symm
      _ = g * f' * g⁻¹ := by rw [h1]
      _ = f := hfeq.symm
  have hR := fzl59b_lemmaR h hz hs hf'c hf'2 hf'1 hf't
  have h1 : IsConj t f ↔ IsConj t f' := by
    rw [hfeq]
    exact fzl59b_isConj_conj g
  have h2 : IsConj t (e * f) ↔ IsConj t (t * f') := by
    have h3 : e * f = g * (t * f') * g⁻¹ := by
      calc e * f = (g * t * g⁻¹) * (g * f' * g⁻¹) := by rw [hg, ← hfeq]
        _ = g * (t * f') * g⁻¹ := by group
    rw [h3]
    exact fzl59b_isConj_conj g
  rw [h1, h2]
  exact hR

theorem fzl59b_parity (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃)
    (hz : ¬ IsConj t ((x₁ * x₂) ^ 2)) (hs : ¬ IsConj t s) {a c : G} (ha : a * a = 1)
    (hc : c * c = 1) (hac : a * c = c * a) (ha1 : a ≠ 1) (hc1 : c ≠ 1) (hne : a ≠ c) :
    (Xor (IsConj t a) (IsConj t c) ↔ IsConj t (a * c)) := by
  have hca : (a * c) * a = c := by
    calc (a * c) * a = a * (c * a) := by rw [mul_assoc]
      _ = a * (a * c) := by rw [← hac]
      _ = (a * a) * c := by rw [mul_assoc]
      _ = c := by rw [ha, one_mul]
  have hacne : a * c ≠ a := by
    intro h1
    apply hc1
    have h2 : a * c = a * 1 := by rw [h1, mul_one]
    exact mul_left_cancel h2
  have hcomm : (a * c) * a = a * (a * c) := by
    rw [hca, ← mul_assoc, ha, one_mul]
  by_cases h1 : IsConj t a
  · have h2 := fzl59b_key h hz hs hc hac hc1 hne h1
    unfold Xor
    tauto
  · by_cases h2 : IsConj t c
    · have h3 := fzl59b_key h hz hs ha hac.symm ha1 hne.symm h2
      rw [← hac] at h3
      unfold Xor
      tauto
    · by_cases h3 : IsConj t (a * c)
      · exfalso
        have h4 := fzl59b_key h hz hs ha hcomm ha1 hacne h3
        rw [hca] at h4
        tauto
      · unfold Xor
        tauto

end CFSG.OddStandard.SmallF3.FritzII
