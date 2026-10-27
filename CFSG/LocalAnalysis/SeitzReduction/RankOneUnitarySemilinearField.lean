module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallTwoRegular

public section

namespace CFSG.SeitzReduction.RankOne

namespace SemilinearField

variable {E : Type*} [Field E] {σ : E →+* E} {q : ℕ}

theorem exists_mul_sigma_eq [Finite E] (hσ : ∀ x, σ x = x ^ q) (hE : Nat.card E = q ^ 2)
    (hq : 2 ≤ q) {c : E} (hc : σ c = c) : ∃ a : E, a * σ a = c := by
  classical
  by_cases hc0 : c = 0
  · exact ⟨0, by rw [hc0, zero_mul]⟩
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hord : orderOf ω = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hω, Nat.card_units, hE]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ω ^ n = Units.mk0 c hc0 :=
    (mem_powers_iff_mem_zpowers (y := Units.mk0 c hc0)).mpr (hω _)
  have hc1 : c ^ (q - 1) = 1 := LineCount.pow_pred_eq_one hσ (by omega) hc hc0
  have hdvd : q ^ 2 - 1 ∣ n * (q - 1) := by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, pow_mul, hn]
    ext
    simp [hc1]
  have hq2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [sq_sub_one_eq_sub_one_mul_add_one q (by omega)]
  obtain ⟨i, hi⟩ : q + 1 ∣ n := by
    rw [hq2, mul_comm n] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (show 0 < q - 1 by omega) hdvd
  refine ⟨((ω ^ i : Eˣ) : E), ?_⟩
  rw [hσ, ← pow_succ']
  have h1 : ((ω ^ n : Eˣ) : E) = c := by rw [hn]; rfl
  rw [hi, pow_mul'] at h1
  simpa using h1

theorem apply_sigma (hσ : ∀ x, σ x = x ^ q) (τ : E →+* E) (x : E) : τ (σ x) = σ (τ x) := by
  rw [hσ, hσ, map_pow]

theorem apply_eq_or_eq_sigma (hσσ : ∀ x, σ (σ x) = x) (τ : E →+* E)
    (hτ : ∀ c, σ c = c → τ c = c) (a : E) : τ a = a ∨ τ a = σ a := by
  have hp : τ (a + σ a) = a + σ a := hτ _ (by rw [map_add, hσσ, add_comm])
  have hr : τ (a * σ a) = a * σ a := hτ _ (by rw [map_mul, hσσ, mul_comm])
  have h0 : a ^ 2 - (a + σ a) * a + a * σ a = 0 := by ring
  have h1 : τ a ^ 2 - (a + σ a) * τ a + a * σ a = 0 := by
    have := congrArg τ h0
    rw [map_add, map_sub, map_mul, map_pow, hp, hr, map_zero] at this
    exact this
  have h2 : (τ a - a) * (τ a - σ a) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

theorem apply_apply_of_fixed (hσ : ∀ x, σ x = x ^ q) (hσσ : ∀ x, σ (σ x) = x) (τ : E →+* E)
    (hτ : ∀ c, σ c = c → τ c = c) (a : E) : τ (τ a) = a := by
  rcases apply_eq_or_eq_sigma hσσ τ hτ a with h | h
  · rw [h, h]
  · rw [h, apply_sigma hσ, h, hσσ]

theorem eq_sigma_of_involutive [Finite E] [CharP E 2] (hσ : ∀ x, σ x = x ^ q)
    (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q) (τ : E →+* E)
    (hτ : ∀ a, τ (τ a) = a) (hne : ∃ a, τ a ≠ a) (a : E) : τ a = σ a := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hσσ : ∀ x, σ (σ x) = x := TraceForm.sigma_sigma hσ hE
  set K : Subfield E := RingHom.eqLocusField τ (RingHom.id E) with hK
  have hmemK : ∀ x, x ∈ K ↔ τ x = x := fun x => Iff.rfl
  let Tr : E →+ E :=
    { toFun := fun x => x + τ x
      map_zero' := by simp
      map_add' := fun x y => by simp only [map_add]; ring }
  have hTr : ∀ x, Tr x = x + τ x := fun x => rfl
  have hker : ∀ x, x ∈ Tr.ker ↔ x ∈ K := by
    intro x
    rw [AddMonoidHom.mem_ker, hTr, hmemK]
    constructor
    · intro h
      have h1 : τ x = -x := by linear_combination h
      rw [h1, CharTwo.neg_eq]
    · intro h
      rw [h]
      exact CharTwo.add_self_eq_zero x
  have hkerK : Nat.card Tr.ker = Nat.card K := Nat.card_congr (Equiv.subtypeEquivRight hker)
  have hrange : Nat.card Tr.range ≤ Nat.card K := by
    refine Nat.card_le_card_of_injective (fun y => ⟨(y : E), ?_⟩) ?_
    · obtain ⟨x, hx⟩ := y.2
      rw [hmemK, ← hx, hTr, map_add, hτ, add_comm]
    · intro y y' h
      apply Subtype.ext
      have h1 := congrArg Subtype.val h
      simpa using h1
  have hcardE : Nat.card Tr.ker * Nat.card Tr.range = q ^ 2 := by
    rw [AddSubgroup.card_ker_mul_card_range Tr, hE]
  have hlow : q ≤ Nat.card K := by
    have h1 : q * q ≤ Nat.card K * Nat.card K := by
      calc q * q = q ^ 2 := (sq q).symm
        _ = Nat.card Tr.ker * Nat.card Tr.range := hcardE.symm
        _ ≤ Nat.card K * Nat.card K := by rw [hkerK]; exact Nat.mul_le_mul_left _ hrange
    exact Nat.mul_self_le_mul_self_iff.mp h1
  obtain ⟨a₀, ha₀⟩ := hne
  have ha₀K : a₀ ∉ K := fun h => ha₀ ((hmemK a₀).mp h)
  have hup : Nat.card K ≤ q := by
    have hinj : Function.Injective fun p : K × K => (p.1 : E) + (p.2 : E) * a₀ := by
      rintro ⟨k₁, k₂⟩ ⟨k₁', k₂'⟩ h
      simp only at h
      by_cases h2 : (k₂ : E) = k₂'
      · have h1 : (k₁ : E) = k₁' := by rw [h2] at h; exact add_right_cancel h
        exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
      · exfalso
        apply ha₀K
        have hd : (k₂ : E) - k₂' ≠ 0 := sub_ne_zero.mpr h2
        have e : a₀ = ((k₁' : E) - k₁) / ((k₂ : E) - k₂') := by
          field_simp
          linear_combination h
        rw [e]
        exact K.div_mem (K.sub_mem k₁'.2 k₁.2) (K.sub_mem k₂.2 k₂'.2)
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hE, sq] at h1
    exact Nat.mul_self_le_mul_self_iff.mp h1
  have hKq : Nat.card K = q := le_antisymm hup hlow
  have hKF : (K : Set E) ⊆ {x | σ x = x} := by
    intro k hk
    have : Fintype K := Fintype.ofFinite K
    have h1 : (⟨k, hk⟩ : K) ^ Fintype.card K = ⟨k, hk⟩ := FiniteField.pow_card _
    rw [← Nat.card_eq_fintype_card, hKq] at h1
    have h2 := congrArg Subtype.val h1
    rw [SubmonoidClass.coe_pow] at h2
    show σ k = k
    rw [hσ, h2]
  have hKeq : (K : Set E) = {x | σ x = x} := by
    refine Set.eq_of_subset_of_ncard_le hKF ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact (hF.trans hKq.symm).le
  have hFK : ∀ c, σ c = c → τ c = c := by
    intro c hc
    have : c ∈ (K : Set E) := by rw [hKeq]; exact hc
    exact (hmemK c).mp this
  rcases apply_eq_or_eq_sigma hσσ τ hFK a with h | h
  · have haK : a ∈ (K : Set E) := (hmemK a).mpr h
    rw [hKeq] at haK
    rw [h]
    exact haK.symm
  · exact h

theorem eq_bot_or_eq_top_of_orderOf [Finite E] {f : ℕ} (hf : 2 ≤ f)
    (hE : Nat.card E = (2 ^ f) ^ 2) {μ : E}
    (hμ : orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1)) (K : AddSubgroup E)
    (hK : ∀ k ∈ K, μ * k ∈ K) : K = ⊥ ∨ K = ⊤ := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hg : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hg0 : 0 < Nat.gcd 3 (2 ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hm0 : 0 < ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) := by
    refine Nat.div_pos ?_ hg0
    have : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
    omega
  have hprim : IsPrimitiveRoot μ (((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1)) :=
    hμ ▸ IsPrimitiveRoot.orderOf μ
  set S : Finset E := (K : Set E).toFinset with hS
  have hSμ : ∀ z ∈ S, μ * z ∈ S := by
    intro z hz
    rw [hS, Set.mem_toFinset] at hz ⊢
    exact hK z hz
  have h1 := LineCount.card_erase_zero_of_isPrimitiveRoot hprim hm0 hSμ
  have h0 : (0 : E) ∈ S := by
    rw [hS, Set.mem_toFinset]
    exact K.zero_mem
  have hcardS : S.card = Nat.card K := by
    rw [hS, ← Set.ncard_eq_toFinset_card', ← Nat.card_coe_set_eq]
    rfl
  have hN : Nat.card K = 1 + ((S.erase 0).image fun z => z ^ (((2 ^ f) ^ 2 - 1) /
      Nat.gcd 3 (2 ^ f + 1))).card * (((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1)) := by
    rw [← hcardS, ← Finset.card_erase_add_one h0, h1]
    ring
  have hdvd : Nat.card K ∣ (2 ^ f) ^ 2 := hE ▸ AddSubgroup.card_addSubgroup_dvd_card K
  rcases eq_one_or_eq_of_dvd hf hN hdvd with h | h
  · exact Or.inl (AddSubgroup.eq_bot_of_card_eq K h)
  · exact Or.inr (AddSubgroup.eq_top_of_card_eq K (h.trans hE.symm))

theorem one_lt_div_gcd {f : ℕ} (hf : 2 ≤ f) : 1 < ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) := by
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hg : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hg0 : 0 < Nat.gcd 3 (2 ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h16 : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hg0]
  generalize (2 ^ f) ^ 2 = Q at h16 ⊢
  generalize Nat.gcd 3 (2 ^ f + 1) = g at hg hg0 ⊢
  omega

theorem exists_ringHom_of_mul [Finite E] {f : ℕ} (hf : 2 ≤ f) (hE : Nat.card E = (2 ^ f) ^ 2)
    {μ : E} (hμ : orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1)) (φ : E →+ E)
    (hφ : Function.Injective φ) {s : E} (hs : ∀ a, φ (μ * a) = s * φ a) :
    ∃ τ : E →+* E, ∀ a, φ a = φ 1 * τ a := by
  let R : AddSubgroup E :=
    { carrier := {e | ∃ e' : E, ∀ a, φ (e * a) = e' * φ a}
      zero_mem' := ⟨0, fun a => by simp⟩
      add_mem' := by
        rintro e₁ e₂ ⟨e₁', h₁⟩ ⟨e₂', h₂⟩
        exact ⟨e₁' + e₂', fun a => by rw [add_mul, map_add, h₁, h₂, add_mul]⟩
      neg_mem' := by
        rintro e ⟨e', h⟩
        exact ⟨-e', fun a => by rw [neg_mul, map_neg, h, neg_mul]⟩ }
  have hR : ∀ e ∈ R, μ * e ∈ R := by
    rintro e ⟨e', h⟩
    exact ⟨s * e', fun a => by rw [mul_assoc, hs, h, mul_assoc]⟩
  have h1R : (1 : E) ∈ R := ⟨1, fun a => by rw [one_mul, one_mul]⟩
  have hall : ∀ e : E, e ∈ R := by
    rcases eq_bot_or_eq_top_of_orderOf hf hE hμ R hR with h | h
    · exfalso
      have : (1 : E) ∈ (⊥ : AddSubgroup E) := h ▸ h1R
      exact one_ne_zero (AddSubgroup.mem_bot.mp this)
    · intro e
      rw [h]
      exact AddSubgroup.mem_top e
  have hφ1 : φ 1 ≠ 0 := by
    intro h0
    exact one_ne_zero (hφ (h0.trans (map_zero φ).symm))
  have key : ∀ e a, φ (e * a) = φ e * (φ 1)⁻¹ * φ a := by
    intro e a
    obtain ⟨e', he'⟩ := hall e
    have h1 := he' 1
    rw [mul_one] at h1
    rw [he', h1, mul_inv_cancel_right₀ hφ1]
  let τ : E →+* E :=
    { toFun := fun e => φ e * (φ 1)⁻¹
      map_one' := mul_inv_cancel₀ hφ1
      map_mul' := fun e₁ e₂ => by
        show φ (e₁ * e₂) * (φ 1)⁻¹ = φ e₁ * (φ 1)⁻¹ * (φ e₂ * (φ 1)⁻¹)
        rw [key e₁ e₂]
        ring
      map_zero' := by simp
      map_add' := fun e₁ e₂ => by simp only [map_add]; ring }
  refine ⟨τ, fun a => ?_⟩
  show φ a = φ 1 * (φ a * (φ 1)⁻¹)
  rw [mul_comm (φ a), ← mul_assoc, mul_inv_cancel₀ hφ1, one_mul]

theorem exists_form_of_shift [Finite E] [CharP E 2] {f : ℕ} (hf : 2 ≤ f)
    (hσ : ∀ x, σ x = x ^ (2 ^ f)) (hE : Nat.card E = (2 ^ f) ^ 2)
    (hF : Nat.card {x : E // σ x = x} = 2 ^ f) {μ : E}
    (hμ : orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1)) (D : E →+ E)
    (hDσ : ∀ a, σ (D a) = D a) (τ : E →+* E) {m γ : E}
    (hD : ∀ a, D (μ * a) = τ μ * σ (τ μ) * D a + TraceForm.form σ γ (τ μ * (m * τ a))) :
    ∃ e : E, ∀ a, D a = TraceForm.form σ e (m * τ a) := by
  have hσσ : ∀ x, σ (σ x) = x := TraceForm.sigma_sigma hσ hE
  have hμ1 : μ ≠ 1 := by
    intro h1
    have := one_lt_div_gcd hf
    rw [← hμ, h1, orderOf_one] at this
    exact lt_irrefl 1 this
  have hν : τ μ ≠ 1 := fun h1 => hμ1 (τ.injective (h1.trans τ.map_one.symm))
  have h1ν : (1 : E) - τ μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hν)
  set e : E := γ / (1 - τ μ) with he
  have hγ : γ = e - τ μ * e := by rw [he]; field_simp
  let D₀ : E →+ E :=
    { toFun := fun a => D a - TraceForm.form σ e (m * τ a)
      map_zero' := by simp [TraceForm.form]
      map_add' := fun a b => by
        simp only [map_add, mul_add, TraceForm.form_add_right]
        ring }
  have hD₀ : ∀ a, D₀ a = D a - TraceForm.form σ e (m * τ a) := fun a => rfl
  have hD₀μ : ∀ a, D₀ (μ * a) = τ μ * σ (τ μ) * D₀ a := by
    intro a
    rw [hD₀, hD₀, hD, mul_sub, hγ]
    simp only [TraceForm.form, map_mul, map_sub]
    ring
  have hker : ∀ k ∈ D₀.ker, μ * k ∈ D₀.ker := by
    intro k hk
    rw [AddMonoidHom.mem_ker] at hk ⊢
    rw [hD₀μ, hk, mul_zero]
  refine ⟨e, fun a => ?_⟩
  rcases eq_bot_or_eq_top_of_orderOf hf hE hμ D₀.ker hker with h | h
  · exfalso
    have hinj : Function.Injective D₀ := (AddMonoidHom.ker_eq_bot_iff D₀).mp h
    have hfix : ∀ a, σ (D₀ a) = D₀ a := by
      intro a
      rw [hD₀, map_sub, hDσ]
      simp only [TraceForm.form, map_add, map_mul, hσσ]
      ring
    have hle := Nat.card_le_card_of_injective (fun a => (⟨D₀ a, hfix a⟩ : {x : E // σ x = x}))
      (fun a b hab => hinj (congrArg Subtype.val hab))
    rw [hE, hF] at hle
    have : 2 ^ f < (2 ^ f) ^ 2 := by
      have : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
      nlinarith
    omega
  · have hmem : a ∈ D₀.ker := h ▸ AddSubgroup.mem_top a
    rw [AddMonoidHom.mem_ker, hD₀] at hmem
    exact sub_eq_zero.mp hmem

end SemilinearField

end CFSG.SeitzReduction.RankOne
