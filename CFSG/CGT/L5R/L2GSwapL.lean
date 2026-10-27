module

public import CFSG.CGT.L5R.L2GAdjustL
public import CFSG.CGT.M24R.L2GModel8
public import CFSG.CGT.M24R.L2GSwap8

public section

namespace CFSG.CGT.L5R

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75JM CFSG.CGT.M24R

variable {G H : Type*} [Group G] [Group H]

theorem tCtxL_conj {T T₁ : Subgroup G} (h : TCtxL T T₁) {s : G} (hs : T₁ = conjSubgroup s T) :
    TCtxL T (conjSubgroup s⁻¹ T) where
  wc := h.wc
  inf_bot := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxT, hx'⟩ := Subgroup.mem_inf.1 hx
    rw [mem_conjSubgroup, inv_inv] at hx'
    have h1 : s * x * s⁻¹ ∈ T₁ := by
      rw [hs, mem_conjSubgroup]
      simpa [mul_assoc] using hxT
    have h2 : s * x * s⁻¹ ∈ T ⊓ T₁ := ⟨hx', h1⟩
    rw [h.inf_bot, Subgroup.mem_bot] at h2
    have : x = s⁻¹ * (s * x * s⁻¹) * s := by group
    rw [this, h2]
    group
  conj := ⟨s⁻¹, rfl⟩
  norm1 := by rw [card_normIn_conj, ← hs, h.norm2]
  norm2 := by
    have := card_normIn_conj T s⁻¹
    rw [inv_inv] at this
    rw [← this, ← hs, h.norm1]

theorem exists_swapperL {T T₁ : Subgroup G} (h : TCtxL T T₁) (M : T1ModelL H)
    {E : OntoEmb H (Subgroup.normalizer (T : Set G))} (hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T) :
    ∃ g : G, conjSubgroup g T = T₁ ∧ conjSubgroup g T₁ = T := by
  obtain ⟨s, hs⟩ := h.conj
  obtain ⟨n₁, hn₁⟩ := exists_conjB h M hE
  obtain ⟨n₂, hn₂⟩ := exists_conjB (tCtxL_conj h hs) M hE
  set b : G := E.Φ (n₁ * M.b0 * n₁⁻¹) with hb
  set y : G := E.Φ (n₂ * M.b0 * n₂⁻¹) with hy
  have hbT₁ : b ∈ T₁ := (hn₁ M.b0).1 M.b0_mem
  have hyc : y ∈ conjSubgroup s⁻¹ T := (hn₂ M.b0).1 M.b0_mem
  have hy1 : y ≠ 1 := by
    intro h1
    apply M.b0_ne
    have h2 : n₂ * M.b0 * n₂⁻¹ = 1 := E.inj (h1.trans (map_one E.Φ).symm)
    have : M.b0 = n₂⁻¹ * (n₂ * M.b0 * n₂⁻¹) * n₂ := by group
    rw [this, h2]
    group
  set m : G := E.Φ (n₂ * n₁⁻¹) with hm
  have hmN : m ∈ Subgroup.normalizer (T : Set G) := E.mem _
  have hmby : m * b * m⁻¹ = y := by
    rw [hm, hb, hy, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have hmem2 : y ∈ conjSubgroup (m * s) T := by
    rw [← conjSubgroup_conjSubgroup, ← hs, mem_conjSubgroup, ← hmby]
    simpa [mul_assoc] using hbT₁
  have heq := inter_unique h.wc hyc hmem2 hy1
  have hmT : conjSubgroup m T = T := mem_normalizer_iff_conjSubgroup_eq.1 hmN
  have hsms : conjSubgroup (s * (m * s)) T = T := by
    have h3 : conjSubgroup s (conjSubgroup s⁻¹ T) = conjSubgroup s (conjSubgroup (m * s) T) := by
      rw [heq]
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup] at h3
    simpa [conjSubgroup_one] using h3.symm
  refine ⟨s * m, ?_, ?_⟩
  · rw [← conjSubgroup_conjSubgroup, hmT, hs]
  · have e : conjSubgroup (s * m) T₁ = conjSubgroup (s * (m * s)) T := by
      rw [hs, conjSubgroup_conjSubgroup, mul_assoc]
    rw [e, hsms]

end CFSG.CGT.L5R
