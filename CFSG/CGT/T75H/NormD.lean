module

public import CFSG.CGT.T75H.HStruct

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem exists_fixed_of_invol {a b : G} (hT : ∀ t ∈ T, t = 1 ∨ t = a ∨ t = b ∨ t = b * a)
    (haT : a ∈ T) (hbT : b ∈ T) (hab : a * b = b * a) (haa : a * a = 1) (hbb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) {w : G} (hww : w * w = 1)
    (hwN : ∀ t ∈ T, w * t * w⁻¹ ∈ T) : ∃ f ∈ T, f ≠ 1 ∧ w * f * w⁻¹ = f := by
  have hσσ : ∀ t : G, w * (w * t * w⁻¹) * w⁻¹ = t := fun t => by
    calc w * (w * t * w⁻¹) * w⁻¹ = (w * w) * t * (w * w)⁻¹ := by group
      _ = t := by rw [hww]; group
  have hσmul : ∀ s t : G, w * (s * t) * w⁻¹ = (w * s * w⁻¹) * (w * t * w⁻¹) := fun s t => by
    group
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hba1 : b * a ≠ 1 := fun h => hne (by
    have h1 : a = b⁻¹ := (eq_inv_of_mul_eq_one_right h)
    rw [h1, hbinv])
  rcases hT _ (hwN a haT) with h | h | h | h
  · exact absurd (by
      calc a = w⁻¹ * (w * a * w⁻¹) * w := by group
        _ = 1 := by rw [h]; group) ha1
  · exact ⟨a, haT, ha1, h⟩
  ·
    have hσb : w * b * w⁻¹ = a := by rw [← h, hσσ]
    refine ⟨b * a, T.mul_mem hbT haT, hba1, ?_⟩
    rw [hσmul, hσb, h, hab]
  ·
    have hσba : w * (b * a) * w⁻¹ = a := by rw [← h, hσσ]
    have h1 : (w * b * w⁻¹) * (b * a) = a := by
      rw [← h, ← hσmul]
      exact hσba
    have h2 : w * b * w⁻¹ = b := by
      calc w * b * w⁻¹ = ((w * b * w⁻¹) * (b * a)) * (b * a)⁻¹ := by group
        _ = a * (b * a)⁻¹ := by rw [h1]
        _ = b := by
          rw [mul_inv_rev, hainv, hbinv, ← mul_assoc, haa, one_mul]
    exact ⟨b, hbT, hb1, h2⟩

theorem exists_hSub_conj_of_invol [Finite G] (hc : Sec6Ctx T T₁ 2 1)
    (h48 : IsWC (barSub T (normIn T₁ T)))
    (h57 : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y)
    {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) {w : G} (hwH : w ∈ hSub T (normIn T₁ T))
    (hww : w * w = 1) (hwT : w ∉ T) :
    ∃ h ∈ hSub T (normIn T₁ T), w = h * ℓ * h⁻¹ := by
  classical
  obtain ⟨N, hNH, hNc, hNodd, hTN, hdec, hNnorm, -⟩ := exists_oddComplement hc h48 D
  set H := hSub T (normIn T₁ T) with hHdef
  have hHN : H ≤ Subgroup.normalizer (T : Set G) :=
    hSub_le_normalizer (fun w hw => (mem_normIn.1 hw).2)
  have hTab := hc.hy.pair.wc.1
  have hℓH : ℓ ∈ H := le_hSub D.hℓ
  have hNcomm : ∀ n ∈ N, ∀ t ∈ T, t * n = n * t := fun n hn t ht =>
    Subgroup.mem_centralizer_iff.1 (hNc hn) t ht
  have hb1 : b ≠ 1 := fun h => D.hbL (h ▸ (normIn T T₁).one_mem)
  have hne : a ≠ b := fun h => D.hbL (h ▸ D.ha)
  have hℓN : ℓ ∈ Subgroup.normalizer (T : Set G) := D.hℓN
  have hinvT : ∀ c ∈ H, (∀ t ∈ T, t * c = c * t) → c * c = 1 → c ∈ T := by
    intro c hcH hcc hc2
    obtain ⟨t, ht, n, hn, hcn⟩ := hdec c ⟨Subgroup.mem_centralizer_iff.2 hcc, hcH⟩
    have htt : t * t = 1 := elemAbelian_mul_self hTab ht
    have hnn : n * n = 1 := by
      have h1 : (t * n) * (t * n) = (t * t) * (n * n) := by
        calc (t * n) * (t * n) = t * (n * t) * n := by group
          _ = t * (t * n) * n := by rw [← hNcomm n hn t ht]
          _ = (t * t) * (n * n) := by group
      rw [← hcn, hc2, htt, one_mul] at h1
      exact h1.symm
    have hn1 : n = 1 := by
      have h5 : orderOf n ∣ Nat.card N := by
        have := orderOf_dvd_natCard (⟨n, hn⟩ : N)
        rwa [Subgroup.orderOf_mk] at this
      have hodd : Odd (orderOf n) := Odd.of_dvd_nat hNodd h5
      have hd : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hnn)
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
      · exact orderOf_eq_one_iff.1 h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    rw [hcn, hn1, mul_one]
    exact ht
  have hwN : ∀ t ∈ T, w * t * w⁻¹ ∈ T := fun t ht => conj_mem_of_mem_normalizer (hHN hwH) ht
  obtain ⟨f, hfT, hf1, hwf⟩ := exists_fixed_of_invol D.hT D.haT D.hb D.comm_ab D.aa D.bb D.ha1
    hb1 hne hww hwN
  obtain ⟨h₀, hh₀, hh₀f⟩ := h57 f hfT hf1 a D.haT D.ha1
  have hh₀N : ∀ t ∈ T, h₀ * t * h₀⁻¹ ∈ T := fun t ht => conj_mem_of_mem_normalizer (hHN hh₀) ht
  set w' : G := h₀ * w * h₀⁻¹ with hw'def
  have hw'H : w' ∈ H := H.mul_mem (H.mul_mem hh₀ hwH) (H.inv_mem hh₀)
  have hw'w' : w' * w' = 1 := by
    calc w' * w' = h₀ * (w * w) * h₀⁻¹ := by simp only [hw'def]; group
      _ = 1 := by rw [hww]; group
  have hw'inv : w'⁻¹ = w' := inv_eq_of_mul_eq_one_right hw'w'
  have hw'a : w' * a * w'⁻¹ = a := by
    have hf' : h₀⁻¹ * a * h₀ = f := by rw [← hh₀f]; group
    calc w' * a * w'⁻¹ = h₀ * (w * (h₀⁻¹ * a * h₀) * w⁻¹) * h₀⁻¹ := by simp only [hw'def]; group
      _ = a := by rw [hf', hwf]; exact hh₀f
  have hw'N : ∀ t ∈ T, w' * t * w'⁻¹ ∈ T := fun t ht =>
    conj_mem_of_mem_normalizer (hHN hw'H) ht
  have hw'a' : a * w' = w' * a := (mul_inv_eq_iff_eq_mul.1 hw'a).symm
  have hncent : ¬ (b * w' = w' * b) := by
    intro hbw
    have hcentT : ∀ t ∈ T, t * w' = w' * t := D.comm_of_ab hw'a' hbw
    apply hwT
    refine hinvT w hwH (fun t ht => ?_) hww
    have h1 : h₀ * t * h₀⁻¹ ∈ T := hh₀N t ht
    have h2 := hcentT _ h1
    calc t * w = h₀⁻¹ * ((h₀ * t * h₀⁻¹) * w') * h₀ := by simp only [hw'def]; group
      _ = h₀⁻¹ * (w' * (h₀ * t * h₀⁻¹)) * h₀ := by rw [h2]
      _ = w * t := by simp only [hw'def]; group
  have hw'b : w' * b * w'⁻¹ = b * a := by
    rcases D.hT _ (hw'N b D.hb) with h | h | h | h
    · exact absurd (by
        calc b = w'⁻¹ * (w' * b * w'⁻¹) * w' := by group
          _ = 1 := by rw [h]; group) hb1
    · exact absurd (by
        calc a = w'⁻¹ * (w' * a * w'⁻¹) * w' := by group
          _ = w'⁻¹ * (w' * b * w'⁻¹) * w' := by rw [hw'a, h]
          _ = b := by group) hne
    · exact absurd (mul_inv_eq_iff_eq_mul.1 h).symm hncent
    · exact h
  have e1 : w' * b = b * a * w' := mul_inv_eq_iff_eq_mul.1 hw'b
  have e2 : ℓ * b = b * a * ℓ := by
    have := D.conj_b_ℓ
    calc ℓ * b = (ℓ * b * ℓ) * ℓ⁻¹ := by group
      _ = b * a * ℓ := by rw [this, D.inv_ℓ]
  have e3 : ℓ * a = a * ℓ := D.comm_aℓ.symm
  have hcb : b * (ℓ * w') = (ℓ * w') * b := by
    calc b * (ℓ * w') = b * (a * a) * ℓ * w' := by rw [D.aa]; group
      _ = b * a * (a * ℓ) * w' := by group
      _ = b * a * (ℓ * a) * w' := by rw [e3]
      _ = (b * a * ℓ) * a * w' := by group
      _ = (ℓ * b) * a * w' := by rw [e2]
      _ = ℓ * (b * a * w') := by group
      _ = ℓ * (w' * b) := by rw [e1]
      _ = (ℓ * w') * b := by group
  have hca : a * (ℓ * w') = (ℓ * w') * a := by
    calc a * (ℓ * w') = (a * ℓ) * w' := by group
      _ = (ℓ * a) * w' := by rw [D.comm_aℓ]
      _ = ℓ * (a * w') := by group
      _ = ℓ * (w' * a) := by rw [hw'a']
      _ = (ℓ * w') * a := by group
  have hcT : ∀ t ∈ T, t * (ℓ * w') = (ℓ * w') * t := D.comm_of_ab hca hcb
  have hcH : ℓ * w' ∈ H := H.mul_mem hℓH hw'H
  obtain ⟨t, ht, n, hn, hcn⟩ := hdec (ℓ * w') ⟨Subgroup.mem_centralizer_iff.2 hcT, hcH⟩
  have hinv : ℓ * (t * n) * ℓ⁻¹ = (t * n)⁻¹ := by
    rw [← hcn]
    calc ℓ * (ℓ * w') * ℓ⁻¹ = (ℓ * ℓ) * w' * ℓ⁻¹ := by group
      _ = w' * ℓ := by rw [D.ℓℓ, D.inv_ℓ]; group
      _ = (ℓ * w')⁻¹ := by rw [mul_inv_rev, hw'inv, D.inv_ℓ]
  have htt : t * t = 1 := elemAbelian_mul_self hTab ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hℓtT : ℓ * t * ℓ⁻¹ ∈ T := conj_mem_of_mem_normalizer hℓN ht
  have hℓnN : ℓ * n * ℓ⁻¹ ∈ N := hNnorm ℓ hℓN n hn
  have hprod : (t * (ℓ * t * ℓ⁻¹)) * (ℓ * n * ℓ⁻¹) = n⁻¹ := by
    have h1 : (ℓ * t * ℓ⁻¹) * (ℓ * n * ℓ⁻¹) = n⁻¹ * t := by
      calc (ℓ * t * ℓ⁻¹) * (ℓ * n * ℓ⁻¹) = ℓ * (t * n) * ℓ⁻¹ := by group
        _ = (t * n)⁻¹ := hinv
        _ = n⁻¹ * t⁻¹ := mul_inv_rev t n
        _ = n⁻¹ * t := by rw [htinv]
    calc (t * (ℓ * t * ℓ⁻¹)) * (ℓ * n * ℓ⁻¹) = t * ((ℓ * t * ℓ⁻¹) * (ℓ * n * ℓ⁻¹)) := by group
      _ = t * (n⁻¹ * t) := by rw [h1]
      _ = (t * n⁻¹) * t := by group
      _ = (n⁻¹ * t) * t := by rw [hNcomm n⁻¹ (N.inv_mem hn) t ht]
      _ = n⁻¹ * (t * t) := by group
      _ = n⁻¹ := by rw [htt, mul_one]
  have hmemTN : t * (ℓ * t * ℓ⁻¹) ∈ T ⊓ N := by
    refine ⟨T.mul_mem ht hℓtT, ?_⟩
    have : t * (ℓ * t * ℓ⁻¹) = n⁻¹ * (ℓ * n * ℓ⁻¹)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact hprod
    rw [this]
    exact N.mul_mem (N.inv_mem hn) (N.inv_mem hℓnN)
  rw [hTN, Subgroup.mem_bot] at hmemTN
  have hℓt : ℓ * t * ℓ⁻¹ = t := by
    have : ℓ * t * ℓ⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right hmemTN
    rw [this, htinv]
  have hℓn : ℓ * n * ℓ⁻¹ = n⁻¹ := by
    rw [hmemTN, one_mul] at hprod
    exact hprod
  have htℓ : t * ℓ = ℓ * t := by
    have := congrArg (fun z => z * ℓ) hℓt
    simpa [mul_assoc] using this.symm
  obtain ⟨k, hk⟩ : Odd (orderOf n) := by
    have h5 : orderOf n ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨n, hn⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hNodd h5
  set u : G := n ^ (k + 1) with hudef
  have huN : u ∈ N := N.pow_mem hn _
  have huu : u * u = n := by
    calc u * u = n ^ (2 * k + 1) * n := by rw [hudef, ← pow_add, ← pow_succ]; ring_nf
      _ = n := by rw [← hk, pow_orderOf_eq_one, one_mul]
  have hℓu : ℓ * u * ℓ⁻¹ = u⁻¹ := by
    rw [hudef, ← conj_pow, hℓn, inv_pow]
  have hℓu' : ℓ * u = u⁻¹ * ℓ := mul_inv_eq_iff_eq_mul.1 hℓu
  have hℓn' : ℓ * n = n⁻¹ * ℓ := mul_inv_eq_iff_eq_mul.1 hℓn
  have hkey : u⁻¹ * ℓ * u = n⁻¹ * ℓ := by
    calc u⁻¹ * ℓ * u = u⁻¹ * (ℓ * u) := by group
      _ = u⁻¹ * (u⁻¹ * ℓ) := by rw [hℓu']
      _ = (u * u)⁻¹ * ℓ := by group
      _ = n⁻¹ * ℓ := by rw [huu]
  have hw'ℓ : w' = ℓ * (t * n) := by
    rw [← hcn]
    calc w' = (ℓ * ℓ) * w' := by rw [D.ℓℓ, one_mul]
      _ = ℓ * (ℓ * w') := by group
  have huH : u ∈ H := hNH huN
  rcases D.cent_ℓ ht htℓ with ht1 | hta
  ·
    rw [ht1] at hw'ℓ
    have hw'eq : w' = u⁻¹ * ℓ * u⁻¹⁻¹ := by
      rw [inv_inv, hkey, hw'ℓ, one_mul, hℓn']
    refine ⟨h₀⁻¹ * u⁻¹, H.mul_mem (H.inv_mem hh₀) (H.inv_mem huH), ?_⟩
    calc w = h₀⁻¹ * w' * h₀ := by simp only [hw'def]; group
      _ = (h₀⁻¹ * u⁻¹) * ℓ * (h₀⁻¹ * u⁻¹)⁻¹ := by rw [hw'eq]; group
  ·
    rw [hta] at hw'ℓ
    have hau : a * u⁻¹ = u⁻¹ * a := hNcomm u⁻¹ (N.inv_mem huN) a D.haT
    have hbℓ : b * ℓ * b⁻¹ = a * ℓ := by
      rw [D.inv_b, D.conj_ℓ_b, e3]
    have hw'eq : w' = (u⁻¹ * b) * ℓ * (u⁻¹ * b)⁻¹ := by
      calc w' = ℓ * (a * n) := hw'ℓ
        _ = (ℓ * a) * n := by group
        _ = a * (ℓ * n) := by rw [e3]; group
        _ = a * (n⁻¹ * ℓ) := by rw [hℓn']
        _ = a * (u⁻¹ * ℓ * u) := by rw [hkey]
        _ = (a * u⁻¹) * ℓ * u := by group
        _ = u⁻¹ * (a * ℓ) * u := by rw [hau]; group
        _ = u⁻¹ * (b * ℓ * b⁻¹) * u := by rw [hbℓ]
        _ = (u⁻¹ * b) * ℓ * (u⁻¹ * b)⁻¹ := by group
    refine ⟨h₀⁻¹ * (u⁻¹ * b), H.mul_mem (H.inv_mem hh₀) (H.mul_mem (H.inv_mem huH)
      (left_le_hSub D.hb)), ?_⟩
    calc w = h₀⁻¹ * w' * h₀ := by simp only [hw'def]; group
      _ = (h₀⁻¹ * (u⁻¹ * b)) * ℓ * (h₀⁻¹ * (u⁻¹ * b))⁻¹ := by rw [hw'eq]; group

end CFSG.CGT.T75H
