module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7WreathE

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X]

namespace A7Data

variable {t : X} {L : Subgroup X} (A : A7Data t L)

omit [Finite X] in
theorem exists_ψ_eq_c0_of_not_mem {g : X} (hg : g ∈ A.T) (hgR : A.ψ ⟨g, hg⟩ ∉ R0) :
    ∃ k : X, ∃ hk : k ∈ A.T, A.ψ ⟨k, hk⟩ = c0 := by
  obtain ⟨r, hr, hψr⟩ := A.exists_mem_R_ψ_eq (mul_c0_mem_R0_of_not_mem (A.ψ_mem_P0 _) hgR)
  refine ⟨r⁻¹ * g, mul_mem (inv_mem hr.1) hg, ?_⟩
  have : (⟨r⁻¹ * g, mul_mem (inv_mem hr.1) hg⟩ : A.T) = (⟨r, hr.1⟩ : A.T)⁻¹ * ⟨g, hg⟩ := rfl
  rw [this, map_mul, map_inv, hψr, mul_inv_rev, inv_mul_cancel_right,
    show c0⁻¹ = c0 by decide]

theorem exists_involution_c0 (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))
    (hH : HaradaInput)
    (hnot : ¬ ∀ P : Subgroup X, IsPGroup 2 P →
      ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P) :
    Nat.card A.K = 2 ∧ ∃ k : X, ∃ hk : k ∈ A.T, k ^ 2 = 1 ∧ A.ψ ⟨k, hk⟩ = c0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨c, hc⟩, hcgen⟩ := IsCyclic.exists_generator (α := A.K)
  have hco : orderOf c = Nat.card A.K := by
    rw [← Subgroup.orderOf_mk c hc, orderOf_eq_card_of_forall_mem_zpowers hcgen]
  have hKp : IsPGroup 2 A.K := A.isPGroup_T.to_le inf_le_left
  obtain ⟨n, hn⟩ := hKp.exists_card_eq
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, pow_zero] at hn
      have := Subgroup.eq_bot_of_card_eq A.K hn
      have ht : t ∈ (⊥ : Subgroup X) := this ▸ A.t_mem_K
      have h2 := A.orderOf_t
      rw [mem_bot.mp ht, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact h
  have ht2 : t ^ 2 = 1 := by rw [← A.orderOf_t, pow_orderOf_eq_one]
  have hcontra : (∀ w : X, w ∈ normalizer (A.T : Set X) → w * t * w⁻¹ = t) → False :=
    fun hfix => hnot (A.gen4_of_fix e hfix)
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
  ·
    refine ⟨by rw [hn]; norm_num, ?_⟩
    have hK2 : ∀ κ ∈ A.K, κ = 1 ∨ κ = t := by
      have heq : zpowers t = A.K := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr A.t_mem_K)
        (by rw [hn, Nat.card_zpowers, A.orderOf_t]; norm_num)
      intro κ hκ
      rw [← heq] at hκ
      exact eq_one_or_eq_of_mem_zpowers ht2 hκ
    by_cases hR : ∀ g : A.T, A.ψ g ∈ R0
    · exact absurd (A.gen4_of_range_le hH (by rw [hn]; norm_num) hR) hnot
    push Not at hR
    obtain ⟨⟨g, hg⟩, hgR⟩ := hR
    obtain ⟨k, hk, hψk⟩ := A.exists_ψ_eq_c0_of_not_mem hg hgR
    have hkR : ∀ r ∈ A.R, k * r = r * k := fun r hr => A.commute_of_ψ_eq_c0 hk hψk hr
    rcases hK2 _ (A.sq_mem_K_of_commute hk hkR) with h1 | h1
    · exact ⟨k, hk, h1, hψk⟩
    · exfalso
      refine hcontra (A.fix_of_sq hk h1 (fun h hh _ => ?_))
      by_cases hψh : A.ψ ⟨h, hh⟩ ∈ R0
      · obtain ⟨r, hr, hψr⟩ := A.exists_mem_R_ψ_eq hψh
        have hm : r⁻¹ * h ∈ A.T := mul_mem (inv_mem hr.1) hh
        have hκ : r⁻¹ * h ∈ A.K := by
          rw [A.mem_K_iff hm]
          have : (⟨r⁻¹ * h, hm⟩ : A.T) = (⟨r, hr.1⟩ : A.T)⁻¹ * ⟨h, hh⟩ := rfl
          rw [this, map_mul, map_inv, hψr, inv_mul_cancel]
        have hkκ : k * (r⁻¹ * h) = (r⁻¹ * h) * k := by
          rcases hK2 _ hκ with h2 | h2
          · rw [h2, mul_one, one_mul]
          · rw [h2]; exact A.commute_t hk
        calc k * h = k * r * (r⁻¹ * h) := by group
          _ = r * (k * (r⁻¹ * h)) := by rw [hkR r hr]; group
          _ = r * ((r⁻¹ * h) * k) := by rw [hkκ]
          _ = h * k := by group
      · obtain ⟨r, hr, hψr⟩ :=
          A.exists_mem_R_ψ_eq (mul_c0_mem_R0_of_not_mem (A.ψ_mem_P0 _) hψh)
        have hm : r⁻¹ * h * k⁻¹ ∈ A.T := mul_mem (mul_mem (inv_mem hr.1) hh) (inv_mem hk)
        have hκ : r⁻¹ * h * k⁻¹ ∈ A.K := by
          rw [A.mem_K_iff hm]
          have : (⟨r⁻¹ * h * k⁻¹, hm⟩ : A.T) =
              (⟨r, hr.1⟩ : A.T)⁻¹ * ⟨h, hh⟩ * (⟨k, hk⟩ : A.T)⁻¹ := rfl
          rw [this, map_mul, map_mul, map_inv, map_inv, hψr, hψk, mul_inv_rev,
            inv_mul_cancel_right, show c0⁻¹ = c0 by decide]
          decide
        have hkκ : k * (r⁻¹ * h * k⁻¹) = (r⁻¹ * h * k⁻¹) * k := by
          rcases hK2 _ hκ with h2 | h2
          · rw [h2, mul_one, one_mul]
          · rw [h2]; exact A.commute_t hk
        calc k * h = k * r * (r⁻¹ * h * k⁻¹) * k := by group
          _ = r * (k * (r⁻¹ * h * k⁻¹)) * k := by rw [hkR r hr]; group
          _ = r * ((r⁻¹ * h * k⁻¹) * k) * k := by rw [hkκ]
          _ = h * k := by group
  ·
    exfalso
    have hco4 : orderOf c = 4 := by rw [hco, hn]; norm_num
    have hc2 : c ^ 2 = t := by
      refine A.eq_t_of_mem_K (pow_mem hc 2)
        (by rw [← pow_mul, show 2 * 2 = orderOf c by rw [hco4], pow_orderOf_eq_one]) ?_
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hco4] at this
      norm_num at this
    by_cases hall : ∀ i ∈ A.T, i ^ 2 = 1 → c * i = i * c
    · exact hcontra (A.fix_of_sq hc.1 hc2 hall)
    push Not at hall
    obtain ⟨i, hi, hi2, hic⟩ := hall
    exact hnot (A.gen4_of_dihedral e hH (by rw [hn]; norm_num) hc hco4 hi hi2 hic)
  ·
    exfalso
    have h8 : 8 ∣ orderOf c := by
      rw [hco, hn, show 8 = 2 ^ 3 by rfl]
      exact Nat.pow_dvd_pow 2 h3
    set g := c ^ (orderOf c / 8) with hg
    have hgo : orderOf g = 8 := by
      rw [hg, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos c) h8)
        (by norm_num)).ne' (Nat.div_dvd_of_dvd h8), Nat.div_div_self h8 (orderOf_pos c).ne']
    have hg4 : g ^ 4 = t := by
      refine A.eq_t_of_mem_K (pow_mem (pow_mem hc _) 4)
        (by rw [← pow_mul, show 4 * 2 = orderOf g by rw [hgo], pow_orderOf_eq_one]) ?_
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hgo] at this
      norm_num at this
    exact hcontra (A.fix_of_pow_four (pow_mem hc.1 _) hg4)

end A7Data

end CFSG.ComponentClassification.HSFLit
