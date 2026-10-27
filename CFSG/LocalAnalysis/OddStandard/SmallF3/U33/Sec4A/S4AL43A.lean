module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFusB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma mem_zpowers_sq_eq_one {z g : G} (hz : z * z = 1) (hg : g ∈ zpowers z) :
    g * g = 1 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have h2 : z ^ (2 : ℤ) = 1 := by
    have htwo : (2 : ℤ) = 1 + 1 := by norm_num
    rw [htwo, zpow_add, zpow_one, hz]
  calc z ^ m * z ^ m = z ^ (m + m) := (zpow_add z m m).symm
    _ = z ^ (2 * m) := by rw [show m + m = 2 * m by ring]
    _ = (z ^ (2 : ℤ)) ^ m := by rw [zpow_mul]
    _ = 1 := by rw [h2]; simp

theorem card_twoCore_cases (h : Hyp G t L) :
    Nat.card (twoCore t) = 2 ∨ Nat.card (twoCore t) = 4 ∨ 8 ≤ Nat.card (twoCore t) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := 2) (twoCore_isPGroup t)
  have hne : Nat.card (twoCore t) ≠ 1 := by
    intro h1
    have hbot : twoCore t = ⊥ :=
      Subgroup.eq_bot_of_card_le (H := twoCore t) (le_of_eq h1)
    have ht1 : t = 1 := by
      have hmem : t ∈ (⊥ : Subgroup G) := hbot ▸ h.mem_twoCore
      simpa using hmem
    exact t_ne_one h ht1
  rcases k with _ | _ | _ | k
  · exact absurd (by simpa using hk) hne
  · exact Or.inl (by simpa using hk)
  · exact Or.inr (Or.inl (by simpa using hk))
  · refine Or.inr (Or.inr ?_)
    rw [hk]
    change (8 : ℕ) ≤ 2 ^ (k + 3)
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem twoCore_eq_zpowers_of_card_eq_two (h : Hyp G t L) (hP : Nat.card (twoCore t) = 2) :
    twoCore t = zpowers t := by
  have hle : zpowers t = twoCore t := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr h.mem_twoCore
    · rw [hP, Nat.card_zpowers, h.ord_t]
  exact hle.symm

theorem exists_sq_root_of_four_le_card (h : Hyp G t L) (hP : 4 ≤ Nat.card (twoCore t)) :
    ∃ c ∈ twoCore t, c * c = t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := 2) (twoCore_isPGroup t)
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    have hle : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hk] at hP
    norm_num at hle
    omega
  haveI : Fintype (twoCore t) := Fintype.ofFinite _
  have hdvd : 4 ∣ Fintype.card (twoCore t) := by
    rw [← Nat.card_eq_fintype_card, hk]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
    refine ⟨2 ^ j, ?_⟩
    rw [pow_add]
    ring
  haveI : IsCyclic (twoCore t) := h.isCyclic
  have hcount := IsCyclic.card_orderOf_eq_totient (α := twoCore t) (d := 4) hdvd
  let s : Finset (twoCore t) := Finset.univ.filter (fun x => orderOf x = 4)
  have hs : s.card = 2 := by
    have htot : Nat.totient 4 = 2 := by decide
    simpa [s, htot] using hcount
  have hpos : 0 < s.card := by rw [hs]; norm_num
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  have hu_order : orderOf u = 4 := by simpa [s] using hu
  refine ⟨(u : G), u.2, ?_⟩
  have huG : orderOf (u : G) = 4 := by rw [Subgroup.orderOf_coe, hu_order]
  have h4 : (u : G) ^ 4 = 1 := by rw [← huG]; exact pow_orderOf_eq_one (u : G)
  have h2ne : (u : G) ^ 2 ≠ 1 := by
    intro hh
    have hdvd2 : orderOf (u : G) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hh
    rw [huG] at hdvd2
    omega
  have hsq : ((u : G) ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h4
  rcases h.eq_one_or_eq ((u : G) ^ 2) (Subgroup.pow_mem (twoCore t) u.2 2) hsq with h1 | h1
  · exact absurd h1 h2ne
  · simpa [pow_two] using h1

theorem exists_fourth_root_of_eight_le_card (h : Hyp G t L) (hP : 8 ≤ Nat.card (twoCore t)) :
    ∃ p ∈ twoCore t, p ^ 4 = t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := 2) (twoCore_isPGroup t)
  have hk3 : 3 ≤ k := by
    by_contra hlt
    push Not at hlt
    have hle : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hk] at hP
    norm_num at hle
    omega
  haveI : Fintype (twoCore t) := Fintype.ofFinite _
  have hdvd : 8 ∣ Fintype.card (twoCore t) := by
    rw [← Nat.card_eq_fintype_card, hk]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk3
    refine ⟨2 ^ j, ?_⟩
    rw [pow_add]
    ring
  haveI : IsCyclic (twoCore t) := h.isCyclic
  have hcount := IsCyclic.card_orderOf_eq_totient (α := twoCore t) (d := 8) hdvd
  let s : Finset (twoCore t) := Finset.univ.filter (fun x => orderOf x = 8)
  have hs : s.card = 4 := by
    have htot : Nat.totient 8 = 4 := by decide
    simpa [s, htot] using hcount
  have hpos : 0 < s.card := by rw [hs]; norm_num
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  have hu_order : orderOf u = 8 := by simpa [s] using hu
  refine ⟨(u : G), u.2, ?_⟩
  have huG : orderOf (u : G) = 8 := by rw [Subgroup.orderOf_coe, hu_order]
  have h8 : (u : G) ^ 8 = 1 := by rw [← huG]; exact pow_orderOf_eq_one (u : G)
  have h4ne : (u : G) ^ 4 ≠ 1 := by
    intro hh
    have hdvd2 : orderOf (u : G) ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hh
    rw [huG] at hdvd2
    omega
  have hsq : ((u : G) ^ 4) ^ 2 = 1 := by rw [← pow_mul]; exact h8
  rcases h.eq_one_or_eq ((u : G) ^ 4) (Subgroup.pow_mem (twoCore t) u.2 4) hsq with h1 | h1
  · exact absurd h1 h4ne
  · exact h1

theorem not_commute_tau_of_sq_eq_t (h : Ctx t L S x₁ x₂ lam rho tau) (h2 : 2 ∣ S.index)
    {c : G} (hc : c ∈ twoCore t) (hct : c * c = t) : tau * c ≠ c * tau := by
  intro hcomm
  haveI : IsCyclic (twoCore t) := h.hyp.isCyclic
  have hPS : twoCore t ≤ S := by rw [h.S_eq]; exact le_sup_left
  have hcS : c ∈ S := hPS hc
  have hP_cent : twoCore t ≤ centralizer ({c} : Set G) := by
    have hsub : ({c} : Set G) ⊆ (twoCore t : Set G) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rwa [hx]
    exact (Subgroup.le_centralizer (twoCore t)).trans (Subgroup.centralizer_le hsub)
  have hM_cent : m12Grp x₁ x₂ lam tau ≤ centralizer ({c} : Set G) := by
    rw [m12Grp]
    refine (Subgroup.closure_le (K := centralizer ({c} : Set G))).mpr ?_
    intro b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with hb1 | hb2 | hb3 | hb4
    · rw [hb1]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (twoCore_commute h.hyp c hc x₁ (generators_mem_L h.toCtx0).1).symm
    · rw [hb2]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (twoCore_commute h.hyp c hc x₂ (generators_mem_L h.toCtx0).2.1).symm
    · rw [hb3]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (twoCore_commute h.hyp c hc lam (generators_mem_L h.toCtx0).2.2).symm
    · rw [hb4]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hSc : S ≤ centralizer ({c} : Set G) := by
    rw [h.S_eq]
    exact sup_le hP_cent hM_cent
  obtain ⟨n, hn, hnt⟩ := exists_swap_of_l42 h h2
  set d : G := n * c * n⁻¹ with hd_def
  have hdS : d ∈ S := by
    rw [hd_def]
    exact (Subgroup.mem_set_normalizer_iff.mp hn c).mp hcS
  have hdcent : d ∈ centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsS : n⁻¹ * s * n ∈ S := by
      have hconj : n * (n⁻¹ * s * n) * n⁻¹ = s := by group
      exact (Subgroup.mem_set_normalizer_iff.mp hn (n⁻¹ * s * n)).mpr (by rw [hconj]; exact hs)
    have h1 : (n⁻¹ * s * n) * c = c * (n⁻¹ * s * n) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hSc hsS)
    have h2 := congrArg (fun y => n * y * n⁻¹) h1
    rw [hd_def]
    calc s * (n * c * n⁻¹) = n * ((n⁻¹ * s * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * s * n)) * n⁻¹ := h2
      _ = (n * c * n⁻¹) * s := by group
  have hdmem : d ∈ S ⊓ centralizer (S : Set G) := ⟨hdS, hdcent⟩
  have hdz : d ∈ twoCore t ⊔ zpowers ((x₁ * x₂) ^ 2) := h.center_le hdmem
  have hcommPz : ∀ a ∈ twoCore t, ∀ b ∈ zpowers ((x₁ * x₂) ^ 2), a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hc : Commute a ((x₁ * x₂) ^ 2) :=
      twoCore_commute h.hyp a ha ((x₁ * x₂) ^ 2) (y_z_mem_L h.toCtx0).2
    exact (hc.zpow_right m).eq
  obtain ⟨q, hq, w, hw, hdw⟩ := (mem_sup_iff_of_commute hcommPz).mp hdz
  have hww : w * w = 1 := mem_zpowers_sq_eq_one (z_mul_self_ne_one h.toCtx0).1 hw
  have hdd : d * d = q * q := by
    rw [hdw]
    calc (q * w) * (q * w) = q * (w * q) * w := by group
      _ = q * (q * w) * w := by rw [← hcommPz q hq w hw]
      _ = q * q * (w * w) := by group
      _ = q * q := by rw [hww, mul_one]
  have hdd_eq : d * d = t * (x₁ * x₂) ^ 2 := by
    rw [hd_def]
    calc (n * c * n⁻¹) * (n * c * n⁻¹) = n * (c * c) * n⁻¹ := by group
      _ = n * t * n⁻¹ := by rw [hct]
      _ = t * (x₁ * x₂) ^ 2 := hnt
  have htzP : t * (x₁ * x₂) ^ 2 ∈ twoCore t := by
    rw [← hdd_eq, hdd]
    exact Subgroup.mul_mem (twoCore t) hq hq
  have hzP : (x₁ * x₂) ^ 2 ∈ twoCore t := by
    have hmem : t⁻¹ * (t * (x₁ * x₂) ^ 2) ∈ twoCore t :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ h.hyp.mem_twoCore) htzP
    simpa only [inv_mul_cancel_left] using hmem
  have hzPL : (x₁ * x₂) ^ 2 ∈ twoCore t ⊓ L := ⟨hzP, (y_z_mem_L h.toCtx0).2⟩
  rw [h.hyp.twoCore_inf, Subgroup.mem_bot] at hzPL
  exact (z_mul_self_ne_one h.toCtx0).2 hzPL

theorem tau_conj_eq_inv_of_sq_eq_t (h : Ctx t L S x₁ x₂ lam rho tau) (h2 : 2 ∣ S.index)
    {c : G} (hc : c ∈ twoCore t) (hct : c * c = t) : tau * c * tau⁻¹ = c⁻¹ := by
  haveI : IsCyclic (twoCore t) := h.hyp.isCyclic
  have htauH : tau ∈ invCent t := h.toCtx0.le_invCent h.tau_mem
  have htau_comm : tau * t = t * tau := mem_invCent_iff.mp htauH
  have hdP : tau * c * tau⁻¹ ∈ twoCore t := twoCore_conj_mem t htauH hc
  set d : G := tau * c * tau⁻¹ with hd_def
  have hd_sq : d * d = t := by
    rw [hd_def]
    calc (tau * c * tau⁻¹) * (tau * c * tau⁻¹) = tau * (c * c) * tau⁻¹ := by group
      _ = tau * t * tau⁻¹ := by rw [hct]
      _ = t := by rw [htau_comm]; group
  set u : G := d * c with hu_def
  have huP : u ∈ twoCore t := Subgroup.mul_mem _ hdP hc
  have hdc : d * c = c * d := by
    have hmem : d ∈ centralizer (twoCore t : Set G) := Subgroup.le_centralizer (twoCore t) hdP
    exact (Subgroup.mem_centralizer_iff.mp hmem c hc).symm
  have hu_sq : u * u = 1 := by
    rw [hu_def]
    calc (d * c) * (d * c) = d * (c * d) * c := by group
      _ = d * (d * c) * c := by rw [← hdc]
      _ = (d * d) * (c * c) := by group
      _ = t * t := by rw [hd_sq, hct]
      _ = 1 := t_mul_self h.hyp
  have hu2 : u ^ 2 = 1 := by rw [pow_two]; exact hu_sq
  rcases h.hyp.eq_one_or_eq u huP hu2 with hu1 | hut
  · have hdc1 : d = c⁻¹ := by
      rw [hu_def] at hu1
      exact eq_inv_of_mul_eq_one_left hu1
    exact hdc1
  · have hdc_eq : d = c := by
      have hmul : d * c = c * c := by
        rw [hu_def] at hut
        rw [hut, hct]
      have := congrArg (fun y => y * c⁻¹) hmul
      simpa [mul_assoc] using this
    have hcomm : tau * c = c * tau := by
      rw [hd_def] at hdc_eq
      have := congrArg (fun y => y * tau) hdc_eq
      simpa [mul_assoc] using this
    exact absurd hcomm (not_commute_tau_of_sq_eq_t h h2 hc hct)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
