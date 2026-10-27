module

public import CFSG.CGT.T75JM.L2GBasic

public section

namespace CFSG.CGT.M24R

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75JM

variable {G : Type*} [Group G]

theorem card_normIn_conj (T : Subgroup G) (s : G) :
    Nat.card (normIn T (conjSubgroup s⁻¹ T)) = Nat.card (normIn (conjSubgroup s T) T) := by
  have hmem : ∀ x : G,
      x ∈ normIn T (conjSubgroup s⁻¹ T) ↔ s * x * s⁻¹ ∈ normIn (conjSubgroup s T) T := by
    intro x
    rw [mem_normIn, mem_normIn, mem_conjSubgroup, mem_normalizer_conj, inv_inv]
    constructor
    · rintro ⟨hx, hxN⟩
      exact ⟨by simpa [mul_assoc] using hx, hxN⟩
    · rintro ⟨hx, hxN⟩
      exact ⟨by simpa [mul_assoc] using hx, hxN⟩
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : normIn T (conjSubgroup s⁻¹ T) => (⟨s * x * s⁻¹, (hmem x).1 x.2⟩ :
      normIn (conjSubgroup s T) T)) ⟨?_, ?_⟩)
  · intro x y hxy
    have h1 : s * (x : G) * s⁻¹ = s * y * s⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using h1)
  · rintro ⟨y, hy⟩
    refine ⟨⟨s⁻¹ * y * s, (hmem _).2 (by simpa [mul_assoc] using hy)⟩, Subtype.ext ?_⟩
    show s * (s⁻¹ * y * s) * s⁻¹ = y
    group

theorem exists_swapper8 {T T₁ : Subgroup G} (h : TCtx T T₁)
    (hcl : ∀ x ∈ Subgroup.normalizer (T : Set G), ∀ y ∈ Subgroup.normalizer (T : Set G),
      x * x = 1 → y * y = 1 → x ∉ T → y ∉ T →
      (∃ A₁ : Subgroup G, Nat.card A₁ ≤ 4 ∧ ∀ t ∈ T, t * x = x * t → t ∈ A₁) →
      (∃ A₂ : Subgroup G, Nat.card A₂ ≤ 4 ∧ ∀ t ∈ T, t * y = y * t → t ∈ A₂) →
        ∃ n ∈ Subgroup.normalizer (T : Set G), n * x * n⁻¹ = y) :
    ∃ g : G, conjSubgroup g T = T₁ ∧ conjSubgroup g T₁ = T := by
  obtain ⟨s, hs⟩ := h.conj
  obtain ⟨b, hb, hb1⟩ := exists_ne_one_of_one_lt_card (K := normIn T₁ T)
    (by rw [h.norm2]; norm_num)
  have hbT₁ : b ∈ T₁ := (mem_normIn.1 hb).1
  have hbN : b ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hb).2
  have hb2 : b * b = 1 := elemAbelian_mul_self h.elemAbelian₁ hbT₁
  have hbT : b ∉ T := fun hbT => hb1 (by
    have : b ∈ T ⊓ T₁ := ⟨hbT, hbT₁⟩
    rw [h.inf_bot, Subgroup.mem_bot] at this
    exact this)
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_of_one_lt_card (K := normIn T T₁)
    (by rw [h.norm1]; norm_num)
  have haT : a ∈ T := (mem_normIn.1 ha).1
  have haN₁ : a ∈ Subgroup.normalizer (T₁ : Set G) := (mem_normIn.1 ha).2
  set y : G := s⁻¹ * a * s with hy
  have hyc : y ∈ conjSubgroup s⁻¹ T := by
    rw [mem_conjSubgroup]
    have : (s⁻¹)⁻¹ * y * s⁻¹ = a := by rw [hy]; group
    rw [this]
    exact haT
  have hyN : y ∈ Subgroup.normalizer (T : Set G) := by
    rw [hs] at haN₁
    exact mem_normalizer_conj.1 haN₁
  have hy2 : y * y = 1 :=
    elemAbelian_mul_self (isElemAbelian_conjSubgroup h.wc.1 s⁻¹) hyc
  have hyT : y ∉ T := fun hyT => ha1 (by
    have hyT₁ : s * y * s⁻¹ ∈ T₁ := by
      rw [hs, mem_conjSubgroup]
      have : s⁻¹ * (s * y * s⁻¹) * s = y := by group
      rw [this]
      exact hyT
    have hsy : s * y * s⁻¹ = a := by rw [hy]; group
    rw [hsy] at hyT₁
    have : a ∈ T ⊓ T₁ := ⟨haT, hyT₁⟩
    rw [h.inf_bot, Subgroup.mem_bot] at this
    exact this)
  have hy1 : y ≠ 1 := fun h1 => hyT (h1 ▸ T.one_mem)
  have hAb : ∃ A₁ : Subgroup G, Nat.card A₁ ≤ 4 ∧ ∀ t ∈ T, t * b = b * t → t ∈ A₁ := by
    refine ⟨normIn T T₁, h.norm1.le, fun t ht htb => mem_normIn.2 ⟨ht, ?_⟩⟩
    exact h.wc₁.centralizer_le_normalizer hbT₁ hb1 (Subgroup.mem_centralizer_singleton_iff.2 htb)
  have hAy : ∃ A₂ : Subgroup G, Nat.card A₂ ≤ 4 ∧ ∀ t ∈ T, t * y = y * t → t ∈ A₂ := by
    refine ⟨normIn T (conjSubgroup s⁻¹ T), ?_, fun t ht hty => mem_normIn.2 ⟨ht, ?_⟩⟩
    · rw [card_normIn_conj, ← hs, h.norm2]
    · exact (h.wc.conj s⁻¹).centralizer_le_normalizer hyc hy1
        (Subgroup.mem_centralizer_singleton_iff.2 hty)
  obtain ⟨n, hn, hnby⟩ := hcl b hbN y hyN hb2 hy2 hbT hyT hAb hAy
  have hmem1 : y ∈ conjSubgroup s⁻¹ T := hyc
  have hmem2 : y ∈ conjSubgroup (n * s) T := by
    rw [← conjSubgroup_conjSubgroup, ← hs, mem_conjSubgroup, ← hnby]
    simpa [mul_assoc] using hbT₁
  have heq := inter_unique h.wc hmem1 hmem2 hy1
  have hnT : conjSubgroup n T = T := mem_normalizer_iff_conjSubgroup_eq.1 hn
  have hsns : conjSubgroup (s * (n * s)) T = T := by
    have h3 : conjSubgroup s (conjSubgroup s⁻¹ T) = conjSubgroup s (conjSubgroup (n * s) T) := by
      rw [heq]
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup] at h3
    simpa [conjSubgroup_one] using h3.symm
  refine ⟨s * n, ?_, ?_⟩
  · rw [← conjSubgroup_conjSubgroup, hnT, hs]
  · have e : conjSubgroup (s * n) T₁ = conjSubgroup (s * (n * s)) T := by
      rw [hs, conjSubgroup_conjSubgroup, mul_assoc]
    rw [e, hsns]

end CFSG.CGT.M24R
