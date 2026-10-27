module

public import CFSG.GH74.GLS.Stage4.T2TSingEq

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4

theorem t5_exists_prime {a₁ a₂ : ℕ} (ha₂ : 0 < a₂) (hlt : a₂ < a₁)
    (h2 : ∀ k : ℕ, 2 ^ k ∣ a₁ ↔ 2 ^ k ∣ a₂) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ a₂.factorization r < a₁.factorization r := by
  have ha₁ : a₁ ≠ 0 := by omega
  have ha₂' : a₂ ≠ 0 := by omega
  by_contra hcon
  push Not at hcon
  have hle : a₁.factorization ≤ a₂.factorization := by
    intro r
    by_cases hr : r.Prime
    · by_cases hr2 : r = 2
      · subst hr2
        have h1 : 2 ^ (a₁.factorization 2) ∣ a₁ :=
          (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two ha₁).2 le_rfl
        have h3 := (h2 _).1 h1
        exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two ha₂').1 h3
      · exact hcon r hr hr2
    · simp [Nat.factorization_eq_zero_of_not_prime _ hr]
  have hdvd : a₁ ∣ a₂ := (Nat.factorization_le_iff_dvd ha₁ ha₂').1 hle
  have := Nat.le_of_dvd ha₂ hdvd
  omega


theorem t5_singular_gt {G : Type} [Group G] [Finite G] (N : T2N3 G) (u : G) (h : Ch6Sec5 N u)
    (hlt : N.q₂ < N.q₁) (h2 : ∀ k : ℕ, 2 ^ k ∣ N.q₁ - 1 ↔ 2 ^ k ∣ N.q₂ - 1) :
    ∃ y ∈ N.H ⊓ N.K₁, y ∉ Subgroup.zpowers N.z ∧ (orderOf y).Prime ∧ Odd (orderOf y) ∧
      orderOf y ∣ N.q₁ - 1 ∧ N.a * y * N.a⁻¹ = y := by
  have hloc := h.loc
  have hW := h.weyl
  have hq₂ge : 3 ≤ N.q₂ := hloc.q₂_ge
  obtain ⟨r, hr, hr2, hrlt⟩ := t5_exists_prime (a₁ := N.q₁ - 1) (a₂ := N.q₂ - 1) (by omega)
    (by omega) h2
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have : Fact r.Prime := ⟨hr⟩
  set b := (N.q₂ - 1).factorization r with hb
  set c := (N.q₁ - 1).factorization r with hc
  have hHc := hloc.H_comm
  have hc1 : Nat.card ↥(N.H ⊓ N.K₁) = N.q₁ - 1 := hloc.card_H_K₁
  have hc2 : Nat.card ↥(N.H ⊓ N.K₂) = N.q₂ - 1 := hloc.card_H_K₂
  have ha₁0 : N.q₁ - 1 ≠ 0 := by omega
  have ha₂0 : N.q₂ - 1 ≠ 0 := by omega
  have hrc : r ^ c ∣ N.q₁ - 1 := Nat.ordProj_dvd _ _
  have hc0 : 0 < c := by omega
  have : IsCyclic ↥(N.H ⊓ N.K₁) := hloc.H₁_cyc
  obtain ⟨h₁, hh₁, hh₁ord⟩ : ∃ h₁ ∈ N.H ⊓ N.K₁, orderOf h₁ = r ^ c := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(N.H ⊓ N.K₁))
    rw [hc1] at hg
    have hn0 : (N.q₁ - 1) / r ^ c ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd (by omega) hrc) (pow_pos hr.pos c)
      omega
    have hdvd : (N.q₁ - 1) / r ^ c ∣ orderOf g := by
      rw [hg]; exact Nat.div_dvd_of_dvd hrc
    refine ⟨(g ^ ((N.q₁ - 1) / r ^ c) : ↥(N.H ⊓ N.K₁)), (g ^ ((N.q₁ - 1) / r ^ c)).2, ?_⟩
    rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd hn0 hdvd, hg]
    exact Nat.div_div_self hrc ha₁0
  have hbc : b < c := hrlt
  set y' : G := h₁ ^ (r ^ b) with hy'
  have hy'H₁ : y' ∈ N.H ⊓ N.K₁ := Subgroup.pow_mem _ hh₁ _
  have hy'ord : orderOf y' = r ^ (c - b) := by
    have hdvd : r ^ b ∣ orderOf h₁ := by rw [hh₁ord]; exact pow_dvd_pow r hbc.le
    rw [hy', orderOf_pow_of_dvd (pow_ne_zero _ hr.ne_zero) hdvd, hh₁ord,
      Nat.pow_div hbc.le hr.pos]
  have hy'H : y' ∈ N.H := hy'H₁.1
  have key : ∀ g ∈ N.H, g ^ (r ^ c) = 1 → g ^ (r ^ b) ∈ N.H ⊓ N.K₁ := by
    intro g hg hgr
    obtain ⟨g₁, hg₁, g₂, hg₂, hgab⟩ := t5_mem_sup (H₁ := N.H ⊓ N.K₁) (H₂ := N.H ⊓ N.K₂) hHc
      inf_le_left inf_le_left hloc.H_idx (hrodd.pow (n := c)) hg hgr
    have hcomm12 : ∀ a ∈ N.H ⊓ N.K₁, ∀ b ∈ N.H ⊓ N.K₂, a * b = b * a :=
      fun a ha b hb => hHc a ha.1 b hb.1
    have hb1 : g₂ ^ (N.q₂ - 1) = 1 := by
      have h1 := pow_card_eq_one' (G := ↥(N.H ⊓ N.K₂)) (x := ⟨g₂, hg₂⟩)
      rw [hc2] at h1
      exact congrArg Subtype.val h1
    have hgm : g ^ (N.q₂ - 1) ∈ N.H ⊓ N.K₁ := by
      have hcm : Commute g₁ g₂ := hcomm12 g₁ hg₁ g₂ hg₂
      rw [hgab, hcm.mul_pow, hb1, mul_one]
      exact Subgroup.pow_mem _ hg₁ _
    obtain ⟨m, hm⟩ : r ^ b ∣ N.q₂ - 1 := Nat.ordProj_dvd _ _
    have hmcop : Nat.Coprime r m := by
      have := Nat.coprime_ordCompl hr ha₂0
      rwa [show (N.q₂ - 1) / r ^ b = m by
        rw [hm]; exact Nat.mul_div_cancel_left _ (pow_pos hr.pos b)] at this
    have hgm' : (g ^ (r ^ b)) ^ m ∈ N.H ⊓ N.K₁ := by
      rw [← pow_mul, ← hm]; exact hgm
    have hgo : (g ^ (r ^ b)) ^ (r ^ (c - b)) = 1 := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hbc.le]; exact hgr
    have hcop : Nat.Coprime m (orderOf (g ^ (r ^ b))) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hgo)
        (Nat.Coprime.pow_right _ hmcop.symm)
    obtain ⟨m', hm'⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm']
    exact Subgroup.pow_mem _ hgm' _
  have hy1 : N.a * y' * N.a⁻¹ ∈ N.H := (Subgroup.mem_normalizer_iff.1 hW.a_normH y').1 hy'H
  have hay'1 : N.a * y' * N.a⁻¹ ∈ N.H ⊓ N.K₁ := by
    have hz : N.a * h₁ * N.a⁻¹ ∈ N.H := (Subgroup.mem_normalizer_iff.1 hW.a_normH h₁).1 hh₁.1
    have hzr : (N.a * h₁ * N.a⁻¹) ^ (r ^ c) = 1 := by
      rw [conj_pow, ← hh₁ord, pow_orderOf_eq_one]; group
    have := key _ hz hzr
    rwa [conj_pow] at this
  have hw1 : N.w₁ * (N.a * y' * N.a⁻¹) * N.w₁⁻¹ = (N.a * y' * N.a⁻¹)⁻¹ := hloc.w₁_inv _ hay'1
  have hw2 : N.w₁ * y' * N.w₁⁻¹ = y'⁻¹ := hloc.w₁_inv _ hy'H₁
  obtain ⟨h₀, hh₀, hw3⟩ := hW.w₁_a
  have hh₀y : h₀ * y'⁻¹ = y'⁻¹ * h₀ := hHc h₀ hh₀ y'⁻¹ (N.H.inv_mem hy'H)
  have hcalc : N.w₁ * (N.a * y' * N.a⁻¹) * N.w₁⁻¹ = N.a⁻¹ * y'⁻¹ * N.a := by
    calc N.w₁ * (N.a * y' * N.a⁻¹) * N.w₁⁻¹
        = (N.w₁ * N.a * N.w₁⁻¹) * (N.w₁ * y' * N.w₁⁻¹) * (N.w₁ * N.a * N.w₁⁻¹)⁻¹ := by group
      _ = (N.a⁻¹ * h₀) * y'⁻¹ * (N.a⁻¹ * h₀)⁻¹ := by rw [hw3, hw2]
      _ = N.a⁻¹ * (h₀ * y'⁻¹) * h₀⁻¹ * N.a := by group
      _ = N.a⁻¹ * (y'⁻¹ * h₀) * h₀⁻¹ * N.a := by rw [hh₀y]
      _ = N.a⁻¹ * y'⁻¹ * N.a := by group
  have hrel : N.a * y'⁻¹ * N.a⁻¹ = N.a⁻¹ * y'⁻¹ * N.a := by
    rw [← hcalc, hw1]; group
  have h2' : N.a ^ 2 * y'⁻¹ * (N.a ^ 2)⁻¹ = y'⁻¹ := by
    calc N.a ^ 2 * y'⁻¹ * (N.a ^ 2)⁻¹ = N.a * (N.a * y'⁻¹ * N.a⁻¹) * N.a⁻¹ := by
          rw [pow_two]; group
      _ = N.a * (N.a⁻¹ * y'⁻¹ * N.a) * N.a⁻¹ := by rw [hrel]
      _ = y'⁻¹ := by group
  have h3 : N.a * y'⁻¹ * N.a⁻¹ = y'⁻¹ := by
    have hc' : N.a ^ 3 * y'⁻¹ * (N.a ^ 3)⁻¹ = y'⁻¹ := by
      rw [hHc (N.a ^ 3) hW.a_cube y'⁻¹ (N.H.inv_mem hy'H)]; group
    calc N.a * y'⁻¹ * N.a⁻¹ = N.a * (N.a ^ 2 * y'⁻¹ * (N.a ^ 2)⁻¹) * N.a⁻¹ := by rw [h2']
      _ = N.a ^ 3 * y'⁻¹ * (N.a ^ 3)⁻¹ := by rw [pow_two, pow_succ, pow_two]; group
      _ = y'⁻¹ := hc'
  have h4 : N.a * y' * N.a⁻¹ = y' := by
    calc N.a * y' * N.a⁻¹ = (N.a * y'⁻¹ * N.a⁻¹)⁻¹ := by group
      _ = (y'⁻¹)⁻¹ := by rw [h3]
      _ = y' := inv_inv y'
  set y : G := y' ^ (r ^ (c - b - 1)) with hy
  have hyH₁ : y ∈ N.H ⊓ N.K₁ := Subgroup.pow_mem _ hy'H₁ _
  have hyord : orderOf y = r := by
    have hdvd : r ^ (c - b - 1) ∣ orderOf y' := by
      rw [hy'ord]; exact pow_dvd_pow r (by omega)
    rw [hy, orderOf_pow_of_dvd (pow_ne_zero _ hr.ne_zero) hdvd, hy'ord,
      Nat.pow_div (by omega) hr.pos]
    have : c - b - (c - b - 1) = 1 := by omega
    rw [this, pow_one]
  have hya : N.a * y * N.a⁻¹ = y := by
    rw [hy, ← conj_pow, h4]
  have hyz : y ∉ Subgroup.zpowers N.z := by
    intro hmem
    have h5 := Subgroup.orderOf_dvd_natCard _ hmem
    rw [Nat.card_zpowers, hloc.z_ord, hyord] at h5
    have h6 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h5
    exact hr2 h6
  refine ⟨y, hyH₁, hyz, hyord ▸ hr, hyord ▸ hrodd, ?_, hya⟩
  rw [hyord]
  exact dvd_trans (dvd_pow_self r hc0.ne') hrc

end CFSG.GH74.GLS.Stage4.Rest
