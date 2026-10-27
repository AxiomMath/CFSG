module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIGOdd
public import CFSG.CGT.Timmesfeld75.Sec4CaseIGBar

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.four_le_card_normIn (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) : 4 ≤ Nat.card (normIn T T₁) := by
  have hS := h.sec3
  obtain ⟨x, hx⟩ := h.pair.conj
  have hI : Sec3Iso T T₁ := by
    have := h.iso x (hx ▸ h.pair.ne) (hx ▸ h.pair.nontriv)
    rwa [← hx] at this
  obtain ⟨hN, f, hf, he⟩ := hI
  have hcard := hS.card_eq_mul hf he
  have hle := hS.card_le_sq_card_normIn ⟨hN, f, hf, he⟩
  have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have h2f : 2 < 2 ^ f := by
    by_contra hnot
    push Not at hnot
    have h1 := Nat.mul_le_mul_left (Nat.card (normIn T T₁)) hnot
    rw [← hcard] at h1
    omega
  have h4f : 4 ≤ 2 ^ f := by
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · interval_cases f <;> simp at h2f
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hf_le : 2 ^ f ≤ Nat.card (normIn T T₁) := by
    rw [hcard, pow_two] at hle
    exact Nat.le_of_mul_le_mul_left hle hLpos
  exact h4f.trans hf_le

omit [Finite G] in
theorem Cfg.bar_comm_of_comm (c : Cfg T T₁) (N : Subgroup (NQuot T)) [N.Normal]
    (hNodd : Odd (Nat.card N)) :
    ∀ n ∈ N, ∀ u ∈ barSub T (normIn T₁ T), u ≠ 1 → u * n = n * u →
      ∀ y ∈ barSub T (normIn T₁ T), y * n = n * y := by
  intro n hn u hu hu1 hun y hy
  obtain ⟨ℓ, hℓN, hℓ, rfl⟩ := exists_eq_barElt_of_mem_barSub hu
  obtain ⟨y₀, hy₀N, hy₀, rfl⟩ := exists_eq_barElt_of_mem_barSub hy
  obtain ⟨ν, rfl⟩ := QuotientGroup.mk_surjective n
  have hñ : (ν : G) ∈ Subgroup.normalizer (T : Set G) := ν.2
  have hnν : (QuotientGroup.mk ν : NQuot T) = barElt T hñ := rfl
  rw [hnν] at hun hn ⊢
  set ñ : G := (ν : G) with hñdef
  have hℓT : ℓ ∉ T := fun h => hu1 ((barElt_eq_one_iff hℓN).2 h)
  have hcomm : ⁅ℓ, ñ⁆ ∈ T := commutator_mem_of_bar_comm hℓN hñ hun
  have hz : ñ * ℓ * ñ⁻¹ ∈ conjSubgroup ñ (normIn T₁ T) := conj_mem_conjSubgroup ñ hℓ
  have hzsup : ñ * ℓ * ñ⁻¹ ∈ normIn T₁ T ⊔ T := by
    have e : ñ * ℓ * ñ⁻¹ = (⁅ℓ, ñ⁆)⁻¹ * ℓ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (T.inv_mem hcomm))
      (Subgroup.mem_sup_left hℓ)
  have hz1 : ñ * ℓ * ñ⁻¹ ≠ 1 := by
    intro h1
    apply hℓT
    have e : ℓ = ñ⁻¹ * (ñ * ℓ * ñ⁻¹) * ñ := by group
    rw [e, h1]
    simp only [mul_one, inv_mul_cancel]
    exact T.one_mem
  have hne : conjSubgroup ñ (normIn T₁ T) ⊓ (normIn T₁ T ⊔ T) ≠ ⊥ := by
    intro h
    have hmem : ñ * ℓ * ñ⁻¹ ∈ conjSubgroup ñ (normIn T₁ T) ⊓ (normIn T₁ T ⊔ T) := ⟨hz, hzsup⟩
    rw [h] at hmem
    exact hz1 (Subgroup.mem_bot.1 hmem)
  obtain ⟨h1, -⟩ := c.commute_conj_L₁ hñ hne
  have hx : ñ * y₀ * ñ⁻¹ ∈ conjSubgroup ñ (normIn T₁ T) := conj_mem_conjSubgroup ñ hy₀
  have hxy : ñ * y₀ * ñ⁻¹ * y₀ = y₀ * (ñ * y₀ * ñ⁻¹) := h1 _ hx y₀ hy₀
  have hyy : y₀ * y₀ = 1 := elemAbelian_mul_self c.wc₁.1 (normIn_le _ _ hy₀)
  have hxx : (ñ * y₀ * ñ⁻¹) * (ñ * y₀ * ñ⁻¹) = 1 := by
    have e : (ñ * y₀ * ñ⁻¹) * (ñ * y₀ * ñ⁻¹) = ñ * (y₀ * y₀) * ñ⁻¹ := by group
    rw [e, hyy]
    group
  have hinv : y₀⁻¹ = y₀ := inv_eq_of_mul_eq_one_right hyy
  have hcg : ⁅y₀, ñ⁆ = y₀ * (ñ * y₀ * ñ⁻¹) := by
    simp only [commutatorElement_def, hinv]
    group
  have hgg : ⁅y₀, ñ⁆ * ⁅y₀, ñ⁆ = 1 := by
    rw [hcg]
    calc y₀ * (ñ * y₀ * ñ⁻¹) * (y₀ * (ñ * y₀ * ñ⁻¹))
        = y₀ * ((ñ * y₀ * ñ⁻¹) * y₀) * (ñ * y₀ * ñ⁻¹) := by group
      _ = y₀ * (y₀ * (ñ * y₀ * ñ⁻¹)) * (ñ * y₀ * ñ⁻¹) := by rw [hxy]
      _ = (y₀ * y₀) * ((ñ * y₀ * ñ⁻¹) * (ñ * y₀ * ñ⁻¹)) := by group
      _ = 1 := by rw [hyy, hxx]; group
  have hgN : ⁅y₀, ñ⁆ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem hy₀N hñ)
        ((Subgroup.normalizer (T : Set G)).inv_mem hy₀N))
      ((Subgroup.normalizer (T : Set G)).inv_mem hñ)
  have hc : barElt T hgN = ⁅barElt T hy₀N, barElt T hñ⁆ := barElt_commutator hy₀N hñ hgN
  have hc2 : ⁅barElt T hy₀N, barElt T hñ⁆ * ⁅barElt T hy₀N, barElt T hñ⁆ = 1 := by
    rw [← hc, barElt_mul]
    exact (barElt_eq_one_iff _).2 (by rw [hgg]; exact T.one_mem)
  have hcN : ⁅barElt T hy₀N, barElt T hñ⁆ ∈ N := by
    have e : ⁅barElt T hy₀N, barElt T hñ⁆ =
        (barElt T hy₀N * barElt T hñ * (barElt T hy₀N)⁻¹) * (barElt T hñ)⁻¹ := by
      simp only [commutatorElement_def]
    rw [e]
    exact N.mul_mem (‹N.Normal›.conj_mem _ hn _) (N.inv_mem hn)
  let c' : N := ⟨_, hcN⟩
  have hc'2 : c' ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hc2
  have hdvd2 : orderOf c' ∣ 2 := orderOf_dvd_of_pow_eq_one hc'2
  have hdvdN : orderOf c' ∣ Nat.card N := orderOf_dvd_natCard c'
  have hcop : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.2 hNodd
  have hone : orderOf c' ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hdvd2 hdvdN
  have hc1 : c' = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hone)
  have hc1' : ⁅barElt T hy₀N, barElt T hñ⁆ = 1 := congrArg Subtype.val hc1
  exact commutatorElement_eq_one_iff_mul_comm.1 hc1'

theorem Cfg.oddNormal_comm_barSub (c : Cfg T T₁) (hcard : 4 ≤ Nat.card (normIn T₁ T))
    (N : Subgroup (NQuot T)) [N.Normal] (hNodd : Odd (Nat.card N)) :
    ∀ n ∈ N, ∀ y ∈ barSub T (normIn T₁ T), y * n = n * y := by
  have hT₁ : IsElemAbelian 2 T₁ := c.wc₁.1
  have hL₁ : IsElemAbelian 2 (normIn T₁ T) := isElemAbelian_of_le hT₁ (normIn_le _ _)
  have hel : IsElemAbelian 2 (barSub T (normIn T₁ T)) := isElemAbelian_barSub hL₁
  have hinf : normIn T₁ T ⊓ T = ⊥ := by
    rw [eq_bot_iff, ← c.symm.inf]
    exact inf_le_inf (normIn_le _ _) le_rfl
  have hcb : 4 ≤ Nat.card (barSub T (normIn T₁ T)) := by
    rw [card_barSub (fun x hx => (mem_normIn.1 hx).2) hinf]
    exact hcard
  exact oddNormal_comm_of_dichotomy hel hcb N hNodd (c.bar_comm_of_comm N hNodd)

theorem Sec4Hyp.oddNormal_comm_sec4A (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T)
    (N : Subgroup (NQuot T)) [N.Normal] (hNodd : Odd (Nat.card N)) :
    ∀ n ∈ N, ∀ z ∈ sec4A T T₁ T₂, z * n = n * z := by
  have h4 := h.four_le_card_normIn hq
  have hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G) := h.mem_normalizer_normIn
  have hc₁ := h.sec3.cfg.oddNormal_comm_barSub (by rw [h.card_normIn₁]; exact h4) N hNodd
  have hc₂ := h.cfg₂.oddNormal_comm_barSub
    (by rw [h.card_normIn₂_eq hB]; exact h4) N hNodd
  intro n hn z hz
  obtain ⟨a', b', ha', hb', rfl⟩ := exists_eq_barElt_mul_of_mem_sec4A h hz
  have hA' : barElt T (mem_normIn.1 ha').2 ∈ barSub T (normIn T₁ T) :=
    barElt_mem_barSub (mem_normIn.1 ha').2 ha'
  have hB' : barElt T (mem_normIn.1 hb').2 ∈ barSub T (normIn T₂ T) :=
    barElt_mem_barSub (mem_normIn.1 hb').2 hb'
  calc barElt T (mem_normIn.1 ha').2 * barElt T (mem_normIn.1 hb').2 * n
      = barElt T (mem_normIn.1 ha').2 * (barElt T (mem_normIn.1 hb').2 * n) := by rw [mul_assoc]
    _ = barElt T (mem_normIn.1 ha').2 * (n * barElt T (mem_normIn.1 hb').2) := by
      rw [hc₂ n hn _ hB']
    _ = (barElt T (mem_normIn.1 ha').2 * n) * barElt T (mem_normIn.1 hb').2 := by rw [mul_assoc]
    _ = (n * barElt T (mem_normIn.1 ha').2) * barElt T (mem_normIn.1 hb').2 := by
      rw [hc₁ n hn _ hA']
    _ = n * (barElt T (mem_normIn.1 ha').2 * barElt T (mem_normIn.1 hb').2) := by rw [mul_assoc]

theorem Sec4Hyp.oddNormal_comm_normalClosure (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T)
    (N : Subgroup (NQuot T)) [N.Normal] (hNodd : Odd (Nat.card N)) :
    ∀ n ∈ N, ∀ z ∈ Subgroup.normalClosure (sec4A T T₁ T₂ : Set (NQuot T)), z * n = n * z := by
  have hC : Subgroup.normalClosure (sec4A T T₁ T₂ : Set (NQuot T)) ≤
      Subgroup.centralizer (N : Set (NQuot T)) := by
    apply Subgroup.normalClosure_le_normal
    intro z hz n hn
    exact (h.oddNormal_comm_sec4A hq N hNodd n hn z hz).symm
  intro n hn z hz
  exact ((Subgroup.mem_centralizer_iff.1 (hC hz)) n hn).symm

end CFSG.CGT.Timmesfeld75
