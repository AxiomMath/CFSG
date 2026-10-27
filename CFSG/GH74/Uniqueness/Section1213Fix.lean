module

public import CFSG.GH74.Uniqueness.Section4Lift
public import CFSG.GH74.Uniqueness.Lemma31gh

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem A5.subset_pair_of_pRank_le_one {H : Subgroup X} (hrank : Open.pRank 2 H ≤ 1)
    {A : Set (Subgroup X)} (hA : ∀ h ∈ H, ∀ δ ∈ A, conjugate δ h ∈ A)
    (hfree : ∀ s ∈ H, orderOf s = 2 → ∀ δ ∈ A, conjugate δ s ≠ δ)
    (hswap : ∀ δ ∈ A, ∀ ζ ∈ A, δ ≠ ζ → ∃ s ∈ H, orderOf s = 2 ∧ conjugate δ s = ζ)
    {s₀ : X} (hs₀ : s₀ ∈ H) (hs₀2 : orderOf s₀ = 2) {δ : Subgroup X} (hδ : δ ∈ A) :
    A ⊆ {δ, conjugate δ s₀} := by
  classical
  have : Fintype ↥H := Fintype.ofFinite _
  have hrk : Open.twoRank ↥H ≤ 1 := by
    rw [Open.twoRank, ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2
      (by norm_num) H]
    exact hrank
  have hs₀s₀ : s₀ * s₀ = 1 := by
    have := pow_orderOf_eq_one s₀
    rwa [hs₀2, pow_two] at this
  have hs₀1 : s₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs₀2
    exact absurd hs₀2 (by norm_num)
  have ht₀o : orderOf (⟨s₀, hs₀⟩ : ↥H) = 2 := by rw [Subgroup.orderOf_mk]; exact hs₀2
  have hiso : ∀ g : ↥H, (g * ⟨s₀, hs₀⟩ * g⁻¹) * ⟨s₀, hs₀⟩ = ⟨s₀, hs₀⟩ * (g * ⟨s₀, hs₀⟩ * g⁻¹) →
      g * ⟨s₀, hs₀⟩ * g⁻¹ = ⟨s₀, hs₀⟩ := by
    intro g hg
    by_contra hne
    have hgo : orderOf (g * ⟨s₀, hs₀⟩ * g⁻¹) = 2 := by
      rw [← ht₀o]
      simpa using orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
        (⟨s₀, hs₀⟩ : ↥H)
    have h2 := two_le_pRank_of_commute_involutions (H := (⊤ : Subgroup ↥H)) (mem_top _)
      (mem_top _) hgo ht₀o hne hg
    unfold Open.twoRank at hrk
    omega
  obtain ⟨O, hOn, hOodd, hO⟩ := CFSG.ZStar.glauberman_zStar ↥H ⟨s₀, hs₀⟩
    (fun h => hs₀1 (congrArg Subtype.val h)) (Subtype.ext hs₀s₀) hiso
  set O' : Subgroup X := O.map H.subtype with hO'
  have hO'H : O' ≤ H := map_subtype_le O
  have hO'odd : Odd (Nat.card O') := by
    rw [hO', card_map_of_injective H.subtype_injective]
    exact hOodd
  have hO'norm : ∀ h ∈ H, ∀ o ∈ O', h * o * h⁻¹ ∈ O' := by
    intro h hh o ho
    obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
    exact ⟨⟨h, hh⟩ * o' * ⟨h, hh⟩⁻¹, hOn.conj_mem o' ho' ⟨h, hh⟩, rfl⟩
  have hO'conj : ∀ h ∈ H, h * s₀ * h⁻¹ * s₀⁻¹ ∈ O' := fun h hh => ⟨_, hO ⟨h, hh⟩, rfl⟩
  have hcoset : ∀ s ∈ H, orderOf s = 2 → s * s₀⁻¹ ∈ O' := by
    intro s hs hso
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_involutions_of_twoRank_le_one hrk ht₀o
      (show orderOf (⟨s, hs⟩ : ↥H) = 2 by rw [Subgroup.orderOf_mk]; exact hso))
    have hc' : (c : X) * s₀ * (c : X)⁻¹ = s := congrArg Subtype.val hc
    rw [← hc']
    exact hO'conj c c.2
  have hs₀O : s₀ ∉ O' := by
    intro h
    have h1 : orderOf s₀ ∣ Nat.card O' := by
      have := orderOf_dvd_natCard (⟨s₀, h⟩ : ↥O')
      rwa [Subgroup.orderOf_mk] at this
    rw [hs₀2] at h1
    exact (Nat.not_even_iff_odd.mpr hO'odd) (even_iff_two_dvd.mpr h1)
  have hnofix : ∀ w ∈ H, w * s₀⁻¹ ∈ O' → ∀ δ' ∈ A, conjugate δ' w ≠ δ' := by
    intro w hwH hwO δ' hδ' hfix
    have hw2 : w * w ∈ O' := by
      have e : w * w = (w * s₀⁻¹) * (s₀ * (w * s₀⁻¹) * s₀⁻¹) * (s₀ * s₀) := by group
      rw [e, hs₀s₀, mul_one]
      exact O'.mul_mem hwO (hO'norm s₀ hs₀ _ hwO)
    have hwO' : w ∉ O' := by
      intro h
      apply hs₀O
      have e : s₀ = (w * s₀⁻¹)⁻¹ * w := by group
      rw [e]
      exact O'.mul_mem (O'.inv_mem hwO) h
    have hmeven : Even (orderOf w) := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      obtain ⟨k, hk⟩ := hodd
      apply hwO'
      have e : (w * w) ^ (k + 1) = w := by
        rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf w + 1 by omega, pow_succ,
          pow_orderOf_eq_one, one_mul]
      rw [← e]
      exact O'.pow_mem hw2 _
    obtain ⟨k, hk⟩ := hmeven
    have hk0 : k ≠ 0 := by
      have := orderOf_pos w
      omega
    have hvo : orderOf (w ^ k) = 2 := by
      rw [orderOf_pow_of_dvd hk0 ⟨2, by omega⟩, hk, ← two_mul,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
    have hN : w ∈ normalizer (δ' : Set X) := conjugate_eq_iff_mem_normalizer.mp hfix
    exact hfree _ (H.pow_mem hwH k) hvo δ' hδ'
      (conjugate_eq_iff_mem_normalizer.mpr (pow_mem hN k))
  have hOfix : ∀ o ∈ O', ∀ δ' ∈ A, conjugate δ' o = δ' := by
    intro o ho δ' hδ'
    by_contra hne
    obtain ⟨s, hsH, hso, hsδ⟩ :=
      hswap δ' hδ' (conjugate δ' o) (hA o (hO'H ho) δ' hδ') (Ne.symm hne)
    have hsO := hcoset s hsH hso
    have hmO : s * o⁻¹ * s₀⁻¹ ∈ O' := by
      have e : s * o⁻¹ * s₀⁻¹ = (s * s₀⁻¹) * (s₀ * o⁻¹ * s₀⁻¹) := by group
      rw [e]
      exact O'.mul_mem hsO (hO'norm s₀ hs₀ _ (O'.inv_mem ho))
    have hfix : conjugate δ' (s * o⁻¹) = δ' := by
      rw [← conjugate_conjugate, hsδ, conjugate_conjugate, mul_inv_cancel, conjugate_one]
    exact hnofix (s * o⁻¹) (H.mul_mem hsH (H.inv_mem (hO'H ho))) hmO δ' hδ' hfix
  intro ζ hζ
  by_cases hζδ : ζ = δ
  · exact Or.inl hζδ
  · right
    show ζ = conjugate δ s₀
    obtain ⟨s, hsH, hso, hsδ⟩ := hswap δ hδ ζ hζ (Ne.symm hζδ)
    have hsO := hcoset s hsH hso
    rw [← hsδ, show s = (s * s₀⁻¹) * s₀ by group, ← conjugate_conjugate, hOfix _ hsO δ hδ]

end CFSG.GH74.Uniqueness
