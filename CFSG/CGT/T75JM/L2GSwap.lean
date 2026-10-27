module

public import CFSG.CGT.T75JM.L2GBasic

public section

namespace CFSG.CGT.T75JM

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G]

namespace TCtx

variable {T T₁ : Subgroup G} (h : TCtx T T₁)
include h

theorem exists_swapper
    (hcl : ∀ x ∈ Subgroup.normalizer (T : Set G), ∀ y ∈ Subgroup.normalizer (T : Set G),
      x * x = 1 → y * y = 1 → x ∉ T → y ∉ T →
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
  obtain ⟨n, hn, hnby⟩ := hcl b hbN y hyN hb2 hy2 hbT hyT
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

end TCtx

section Swap

variable {T T₁ : Subgroup G} {g : G}

theorem mem_normalizer_T₁_iff (hg1 : conjSubgroup g T = T₁) {x : G} :
    g * x * g⁻¹ ∈ Subgroup.normalizer (T₁ : Set G) ↔ x ∈ Subgroup.normalizer (T : Set G) := by
  rw [← hg1, mem_normalizer_conj]
  simp [mul_assoc]

theorem mem_normalizer_T_iff (hg2 : conjSubgroup g T₁ = T) {x : G} :
    g * x * g⁻¹ ∈ Subgroup.normalizer (T : Set G) ↔ x ∈ Subgroup.normalizer (T₁ : Set G) := by
  rw [← hg2, mem_normalizer_conj]
  simp [mul_assoc]

theorem swap_mem_D (hg1 : conjSubgroup g T = T₁) (hg2 : conjSubgroup g T₁ = T) {x : G}
    (hx : x ∈ Subgroup.normalizer (T : Set G)) (hx₁ : x ∈ Subgroup.normalizer (T₁ : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.normalizer (T : Set G) ∧
      g * x * g⁻¹ ∈ Subgroup.normalizer (T₁ : Set G) :=
  ⟨(mem_normalizer_T_iff hg2).2 hx₁, (mem_normalizer_T₁_iff hg1).2 hx⟩

theorem swap_mem_B (hg1 : conjSubgroup g T = T₁) (hg2 : conjSubgroup g T₁ = T) {a : G}
    (ha : a ∈ normIn T T₁) : g * a * g⁻¹ ∈ normIn T₁ T := by
  obtain ⟨haT, haN₁⟩ := mem_normIn.1 ha
  refine mem_normIn.2 ⟨?_, (mem_normalizer_T_iff hg2).2 haN₁⟩
  rw [← hg1, mem_conjSubgroup]
  simpa [mul_assoc] using haT

theorem swap_mem_A (hg1 : conjSubgroup g T = T₁) (hg2 : conjSubgroup g T₁ = T) {b : G}
    (hb : b ∈ normIn T₁ T) : g * b * g⁻¹ ∈ normIn T T₁ := by
  obtain ⟨hbT₁, hbN⟩ := mem_normIn.1 hb
  refine mem_normIn.2 ⟨?_, (mem_normalizer_T₁_iff hg1).2 hbN⟩
  rw [← hg2, mem_conjSubgroup]
  simpa [mul_assoc] using hbT₁

end Swap

end CFSG.CGT.T75JM
