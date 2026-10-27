module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightD

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem conj_eq_mul_of_inv_odd {s n : X} (hinv : s * n * s⁻¹ = n⁻¹) (hodd : Odd (orderOf n)) :
    ∃ c ∈ zpowers n, c * s * c⁻¹ = n * s := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨n ^ (k + 1), npow_mem_zpowers n (k + 1), ?_⟩
  have h1 : s * (n ^ (k + 1))⁻¹ * s⁻¹ = n ^ (k + 1) := by
    have h2 : s * n⁻¹ * s⁻¹ = n := by
      rw [show s * n⁻¹ * s⁻¹ = (s * n * s⁻¹)⁻¹ by group, hinv, inv_inv]
    rw [← inv_pow, show ∀ m : ℕ, s * n⁻¹ ^ m * s⁻¹ = (s * n⁻¹ * s⁻¹) ^ m from fun m => by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, pow_succ, ← ih]
        group, h2]
  calc n ^ (k + 1) * s * (n ^ (k + 1))⁻¹
      = n ^ (k + 1) * (s * (n ^ (k + 1))⁻¹ * s⁻¹) * s := by group
    _ = n ^ (k + 1) * n ^ (k + 1) * s := by rw [h1]
    _ = n ^ (2 * k + 1) * n * s := by rw [← pow_add, ← pow_succ]; ring_nf
    _ = n * s := by rw [← hk, pow_orderOf_eq_one, one_mul]

theorem exists_commute_of_rho_commute_kernel_two [Finite X] {M H : Subgroup X}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ)
    (hMH : M ≤ H) (hHN : H ≤ normalizer (M : Set X)) {t : X} (htH : t ∈ H) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (htK : t ∈ UnbalancedLayer.coreActionKernel M)
    (hK2 : ∀ P : Subgroup X, P ≤ H ⊓ UnbalancedLayer.coreActionKernel M → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {s : X} (hsH : s ∈ H) (hs2 : s * s = 1) (hst : s * t = t * s)
    (hsA : ρ ⟨s, hHN hsH⟩ ∈ alternatingGroup (Fin 9)) {h : X} (hhH : h ∈ H)
    (hcomm : ρ ⟨h, hHN hhH⟩ * ρ ⟨s, hHN hsH⟩ = ρ ⟨s, hHN hsH⟩ * ρ ⟨h, hHN hhH⟩) :
    ∃ (f : X) (hfH : f ∈ H), f * s = s * f ∧ f * t = t * f ∧
      ρ ⟨f, hHN hfH⟩ = ρ ⟨h, hHN hhH⟩ := by
  classical
  set K := H ⊓ UnbalancedLayer.coreActionKernel M with hKdef
  obtain ⟨N, hNK, hNodd, hNt⟩ := exists_oddPart_of_card_le_two (K := K) ⟨htH, htK⟩ ht2 ht1 hK2
  have ht2o : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have hρK : ∀ k ∈ K, ∀ hk : k ∈ normalizer (M : Set X), ρ ⟨k, hk⟩ = 1 := fun k hk _ =>
    hρ.eq_one_of_mem_coreActionKernel (by norm_num) (Subgroup.mem_inf.mp hk).2
  have hKmem : ∀ (k : X) (hk : k ∈ H), ρ ⟨k, hHN hk⟩ = 1 → k ∈ K := fun k hk h1 =>
    Subgroup.mem_inf.mpr ⟨hk, hρ.mem_coreActionKernel (hHN hk) h1⟩
  have hNconj : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    have hnK := Subgroup.mem_inf.mp (hNK hn)
    have hcK : g * n * g⁻¹ ∈ K := Subgroup.mem_inf.mpr
      ⟨H.mul_mem (H.mul_mem hg hnK.1) (H.inv_mem hg),
        hρ.conj_mem_coreActionKernel (by norm_num) (hHN hg) hnK.2⟩
    refine (hNodd _ hcK).mpr ?_
    have h1 : orderOf (g * n * g⁻¹) = orderOf n := by
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective n
      simpa using this
    rw [h1]
    exact (hNodd n (hNK hn)).mp hn
  have hNH : ∀ n ∈ N, n ∈ H := fun n hn => (Subgroup.mem_inf.mp (hNK hn)).1
  obtain ⟨q, hq⟩ := θ.surjective ⟨ρ ⟨s, hHN hsH⟩, hsA⟩
  obtain ⟨⟨m₀, hm₀⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hm₀ρ : ρ ⟨m₀, hHN (hMH hm₀)⟩ = ρ ⟨s, hHN hsH⟩ := by
    have h1 := hρ.apply_of_mem (by norm_num) ⟨m₀, hm₀⟩
    rw [hq] at h1
    exact h1
  set k₀ := m₀⁻¹ * s with hk₀def
  have hk₀H : k₀ ∈ H := H.mul_mem (H.inv_mem (hMH hm₀)) hsH
  have hk₀K : k₀ ∈ K := by
    refine hKmem k₀ hk₀H ?_
    have h1 : (⟨k₀, hHN hk₀H⟩ : ↥(normalizer (M : Set X))) =
        (⟨m₀, hHN (hMH hm₀)⟩)⁻¹ * ⟨s, hHN hsH⟩ := rfl
    rw [h1, map_mul, map_inv, hm₀ρ, inv_mul_cancel]
  have hhm : h * m₀ * h⁻¹ * m₀⁻¹ ∈ N := by
    have hM : h * m₀ * h⁻¹ * m₀⁻¹ ∈ M :=
      M.mul_mem ((mem_normalizer_iff.mp (hHN hhH) m₀).mp hm₀) (M.inv_mem hm₀)
    have hH : h * m₀ * h⁻¹ * m₀⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem hhH (hMH hm₀)) (H.inv_mem hhH)) (H.inv_mem (hMH hm₀))
    have hK : h * m₀ * h⁻¹ * m₀⁻¹ ∈ K := by
      refine hKmem _ hH ?_
      have h1 : (⟨h * m₀ * h⁻¹ * m₀⁻¹, hHN hH⟩ : ↥(normalizer (M : Set X))) =
          ⟨h, hHN hhH⟩ * ⟨m₀, hHN (hMH hm₀)⟩ * (⟨h, hHN hhH⟩)⁻¹ *
            (⟨m₀, hHN (hMH hm₀)⟩)⁻¹ := rfl
      rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hm₀ρ, hcomm]
      group
    exact (hNodd _ hK).mpr (odd_orderOf_of_rho_eq_one hρ hM (hρK _ hK _))
  have hhk : h * k₀ * h⁻¹ * k₀⁻¹ ∈ N := by
    rcases hNt k₀ hk₀K with hk | hk
    · exact N.mul_mem (hNconj h hhH k₀ hk) (N.inv_mem hk)
    ·
      set n₀ := k₀ * t with hn₀def
      have hk₀ : k₀ = n₀ * t := by rw [hn₀def, mul_assoc, ht2, mul_one]
      have htK' : h * t * h⁻¹ ∈ K := Subgroup.mem_inf.mpr
        ⟨H.mul_mem (H.mul_mem hhH htH) (H.inv_mem hhH),
          hρ.conj_mem_coreActionKernel (by norm_num) (hHN hhH) htK⟩
      have htt : h * t * h⁻¹ * t ∈ N := by
        rcases hNt _ htK' with h1 | h1
        · exfalso
          have h2 := (hNodd _ htK').mp h1
          have h3 : orderOf (h * t * h⁻¹) = 2 := by
            have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective t
            simpa [ht2o] using this
          rw [h3] at h2
          exact absurd h2 (by decide)
        · exact h1
      have h1 : h * k₀ * h⁻¹ * k₀⁻¹ =
          (h * n₀ * h⁻¹) * (h * t * h⁻¹ * t) * n₀⁻¹ := by
        rw [hk₀, mul_inv_rev, show t⁻¹ = t from inv_eq_of_mul_eq_one_right ht2]
        group
      rw [h1]
      exact N.mul_mem (N.mul_mem (hNconj h hhH n₀ hk) htt) (N.inv_mem hk)
  set n := h * s * h⁻¹ * s⁻¹ with hndef
  have hnN : n ∈ N := by
    have h1 : n = (h * m₀ * h⁻¹ * m₀⁻¹) * (m₀ * (h * k₀ * h⁻¹ * k₀⁻¹) * m₀⁻¹) := by
      rw [hndef, hk₀def]
      group
    rw [h1]
    exact N.mul_mem hhm (hNconj m₀ (hMH hm₀) _ hhk)
  have hns : h * s * h⁻¹ = n * s := by rw [hndef]; group
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hinv : s * n * s⁻¹ = n⁻¹ := by
    have h1 : n * s * (n * s) = 1 := by
      rw [← hns]
      calc h * s * h⁻¹ * (h * s * h⁻¹) = h * (s * s) * h⁻¹ := by group
        _ = 1 := by rw [hs2]; group
    rw [hsinv]
    calc s * n * s = n⁻¹ * (n * s * (n * s)) := by group
      _ = n⁻¹ := by rw [h1, mul_one]
  obtain ⟨c, hc, hcs⟩ := conj_eq_mul_of_inv_odd hinv ((hNodd n (hNK hnN)).mp hnN)
  have hcN : c ∈ N := (zpowers_le.mpr hnN) hc
  set f₀ := c⁻¹ * h with hf₀def
  have hf₀H : f₀ ∈ H := H.mul_mem (H.inv_mem (hNH c hcN)) hhH
  have hf₀s : f₀ * s * f₀⁻¹ = s := by
    rw [hf₀def, show c⁻¹ * h * s * (c⁻¹ * h)⁻¹ = c⁻¹ * (h * s * h⁻¹) * c by group, hns, ← hcs]
    group
  have htK'' : f₀ * t * f₀⁻¹ ∈ K := Subgroup.mem_inf.mpr
    ⟨H.mul_mem (H.mul_mem hf₀H htH) (H.inv_mem hf₀H),
      hρ.conj_mem_coreActionKernel (by norm_num) (hHN hf₀H) htK⟩
  set n₁ := f₀ * t * f₀⁻¹ * t with hn₁def
  have hn₁N : n₁ ∈ N := by
    rcases hNt _ htK'' with h1 | h1
    · exfalso
      have h2 := (hNodd _ htK'').mp h1
      have h3 : orderOf (f₀ * t * f₀⁻¹) = 2 := by
        have := orderOf_injective (MulAut.conj f₀).toMonoidHom (MulAut.conj f₀).injective t
        simpa [ht2o] using this
      rw [h3] at h2
      exact absurd h2 (by decide)
    · exact h1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hn₁t : n₁ * t = f₀ * t * f₀⁻¹ := by rw [hn₁def, mul_assoc, ht2, mul_one]
  have hn₁inv : t * n₁ * t⁻¹ = n₁⁻¹ := by
    have h1 : n₁ * t * (n₁ * t) = 1 := by
      rw [hn₁t]
      calc f₀ * t * f₀⁻¹ * (f₀ * t * f₀⁻¹) = f₀ * (t * t) * f₀⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    rw [htinv]
    calc t * n₁ * t = n₁⁻¹ * (n₁ * t * (n₁ * t)) := by group
      _ = n₁⁻¹ := by rw [h1, mul_one]
  have hn₁s : n₁ * s = s * n₁ := by
    have h1 : f₀ * t * f₀⁻¹ * s = s * (f₀ * t * f₀⁻¹) := by
      calc f₀ * t * f₀⁻¹ * s = f₀ * t * f₀⁻¹ * (f₀ * s * f₀⁻¹) := by rw [hf₀s]
        _ = f₀ * (t * s) * f₀⁻¹ := by group
        _ = f₀ * (s * t) * f₀⁻¹ := by rw [hst]
        _ = f₀ * s * f₀⁻¹ * (f₀ * t * f₀⁻¹) := by group
        _ = s * (f₀ * t * f₀⁻¹) := by rw [hf₀s]
    rw [hn₁def]
    calc f₀ * t * f₀⁻¹ * t * s = f₀ * t * f₀⁻¹ * (t * s) := by group
      _ = f₀ * t * f₀⁻¹ * (s * t) := by rw [hst]
      _ = f₀ * t * f₀⁻¹ * s * t := by group
      _ = s * (f₀ * t * f₀⁻¹) * t := by rw [h1]
      _ = s * (f₀ * t * f₀⁻¹ * t) := by group
  obtain ⟨c₁, hc₁, hc₁t⟩ := conj_eq_mul_of_inv_odd hn₁inv ((hNodd n₁ (hNK hn₁N)).mp hn₁N)
  have hc₁N : c₁ ∈ N := (zpowers_le.mpr hn₁N) hc₁
  have hc₁s : c₁ * s = s * c₁ := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc₁
    exact ((Commute.zpow_left hn₁s j))
  refine ⟨c₁⁻¹ * f₀, H.mul_mem (H.inv_mem (hNH c₁ hc₁N)) hf₀H, ?_, ?_, ?_⟩
  · have h1 : c₁⁻¹ * s = s * c₁⁻¹ := by
      calc c₁⁻¹ * s = c₁⁻¹ * (s * c₁) * c₁⁻¹ := by group
        _ = c₁⁻¹ * (c₁ * s) * c₁⁻¹ := by rw [hc₁s]
        _ = s * c₁⁻¹ := by group
    calc c₁⁻¹ * f₀ * s = c₁⁻¹ * (f₀ * s * f₀⁻¹) * f₀ := by group
      _ = c₁⁻¹ * s * f₀ := by rw [hf₀s]
      _ = s * c₁⁻¹ * f₀ := by rw [h1]
      _ = s * (c₁⁻¹ * f₀) := by group
  · calc c₁⁻¹ * f₀ * t = c₁⁻¹ * (f₀ * t * f₀⁻¹) * f₀ := by group
      _ = c₁⁻¹ * (n₁ * t) * f₀ := by rw [hn₁t]
      _ = c₁⁻¹ * (c₁ * t * c₁⁻¹) * f₀ := by rw [hc₁t]
      _ = t * (c₁⁻¹ * f₀) := by group
  · have h1 : (⟨c₁⁻¹ * f₀, hHN (H.mul_mem (H.inv_mem (hNH c₁ hc₁N)) hf₀H)⟩ :
        ↥(normalizer (M : Set X))) = (⟨c₁, hHN (hNH c₁ hc₁N)⟩)⁻¹ * (⟨c, hHN (hNH c hcN)⟩)⁻¹ *
          ⟨h, hHN hhH⟩ := Subtype.ext (by
            change c₁⁻¹ * (c⁻¹ * h) = c₁⁻¹ * c⁻¹ * h
            group)
    rw [h1, map_mul, map_mul, map_inv, map_inv, hρK c₁ (hNK hc₁N) _, hρK c (hNK hcN) _,
      inv_one, one_mul, one_mul]

theorem exists_commute_of_rho_involution_kernel_two [Finite X] {M H : Subgroup X}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ)
    (hMH : M ≤ H) (hHN : H ≤ normalizer (M : Set X)) {t : X} (htH : t ∈ H) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (htK : t ∈ UnbalancedLayer.coreActionKernel M)
    (hK2 : ∀ P : Subgroup X, P ≤ H ⊓ UnbalancedLayer.coreActionKernel M → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {s : X} (hsH : s ∈ H) (hs2 : s * s = 1) (hst : s * t = t * s)
    (hsA : ρ ⟨s, hHN hsH⟩ ∈ alternatingGroup (Fin 9)) {h : X} (hhH : h ∈ H)
    (hcomm : ρ ⟨h, hHN hhH⟩ * ρ ⟨s, hHN hsH⟩ = ρ ⟨s, hHN hsH⟩ * ρ ⟨h, hHN hhH⟩)
    (hh2 : ρ ⟨h, hHN hhH⟩ * ρ ⟨h, hHN hhH⟩ = 1) :
    ∃ (f : X) (hfH : f ∈ H), f * s = s * f ∧ f * t = t * f ∧
      ρ ⟨f, hHN hfH⟩ = ρ ⟨h, hHN hhH⟩ ∧ (f * f = 1 ∨ f * f = t) := by
  classical
  obtain ⟨f₀, hf₀H, hf₀s, hf₀t, hf₀ρ⟩ := exists_commute_of_rho_commute_kernel_two hρ hMH hHN htH
    ht2 ht1 htK hK2 hsH hs2 hst hsA hhH hcomm
  set K := H ⊓ UnbalancedLayer.coreActionKernel M with hKdef
  obtain ⟨N, hNK, hNodd, hNt⟩ := exists_oddPart_of_card_le_two (K := K) ⟨htH, htK⟩ ht2 ht1 hK2
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos f₀).ne'
  set f := f₀ ^ b with hfdef
  have hfH : f ∈ H := H.pow_mem hf₀H b
  have hρpow : ∀ (x : X) (hx : x ∈ H) (j : ℕ),
      ρ ⟨x ^ j, hHN (H.pow_mem hx j)⟩ = ρ ⟨x, hHN hx⟩ ^ j := fun x hx j => by
    rw [← map_pow]
    rfl
  have hfρ : ρ ⟨f, hHN hfH⟩ = ρ ⟨h, hHN hhH⟩ := by
    rw [hρpow f₀ hf₀H b, hf₀ρ]
    obtain ⟨c, rfl⟩ := hb
    rw [pow_succ, pow_mul, sq, hh2, one_pow, one_mul]
  have hf2a : f ^ 2 ^ a = 1 := by
    rw [hfdef, ← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  have h2el : ∀ x : X, x ^ 2 ^ a = 1 → Odd (orderOf x) → x = 1 := by
    intro x hx hodd
    have h1 : orderOf x ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · rw [hj, pow_succ] at hodd
      exact absurd hodd (by simp [Nat.odd_mul, Nat.not_odd_iff_even])
  have hfs : f * s = s * f := (Commute.pow_left hf₀s b)
  have hft : f * t = t * f := (Commute.pow_left hf₀t b)
  have hffK : f * f ∈ K := Subgroup.mem_inf.mpr ⟨H.mul_mem hfH hfH, hρ.mem_coreActionKernel
    (hHN (H.mul_mem hfH hfH)) (by
      have h1 : (⟨f * f, hHN (H.mul_mem hfH hfH)⟩ : ↥(normalizer (M : Set X))) =
          ⟨f, hHN hfH⟩ * ⟨f, hHN hfH⟩ := rfl
      rw [h1, map_mul, hfρ, hh2])⟩
  have hff2 : (f * f) ^ 2 ^ a = 1 := by
    rw [← sq, ← pow_mul, mul_comm, pow_mul, hf2a, one_pow]
  refine ⟨f, hfH, hfs, hft, hfρ, ?_⟩
  rcases hNt _ hffK with h1 | h1
  · exact Or.inl (h2el _ hff2 ((hNodd _ hffK).mp h1))
  · right
    have ht2a : t ^ 2 ^ a = 1 := by
      rcases a with _ | a
      ·
        exfalso
        have hf1 : f = 1 := by rw [pow_zero, pow_one] at hf2a; exact hf2a
        rw [hf1, one_mul, one_mul] at h1
        have h2 := (hNodd t (Subgroup.mem_inf.mpr ⟨htH, htK⟩)).mp h1
        rw [orderOf_eq_prime (by rw [sq]; exact ht2) ht1] at h2
        exact absurd h2 (by decide)
      · rw [pow_succ', pow_mul, show t ^ 2 = 1 by rw [sq]; exact ht2, one_pow]
    have hcomm' : Commute (f * f) t := (Commute.mul_left hft hft)
    have h3 : (f * f * t) ^ 2 ^ a = 1 := by rw [hcomm'.mul_pow, hff2, ht2a, one_mul]
    have hffK' : f * f * t ∈ K := Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hfH hfH) htH,
      (UnbalancedLayer.coreActionKernel M).mul_mem (Subgroup.mem_inf.mp hffK).2 htK⟩
    have h4 := h2el _ h3 ((hNodd _ hffK').mp h1)
    calc f * f = f * f * t * t := by rw [mul_assoc, ht2, mul_one]
      _ = t := by rw [h4, one_mul]

end CFSG.ComponentClassification.SolMax
