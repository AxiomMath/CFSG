module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIConj
public import CFSG.CGT.Timmesfeld75.Sec3Fpf
public import CFSG.CGT.Timmesfeld75.Sec3Ten
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIINorm

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.sec4N_le_normalizer_right (h : Sec4Hyp T T₁ a T₂) :
    sec4N T T₁ T₂ ≤ Subgroup.normalizer (T₂ : Set G) := by
  have hB := h.mem_normalizer_normIn
  refine sup_le (sup_le ?_ ?_) ((normIn_le _ _).trans Subgroup.le_normalizer)
  · rw [← h.normIn_eq hB]
    exact inf_le_right
  · rw [← h.normIn_right_eq hB]
    exact inf_le_right

theorem Sec4Hyp.fixed_eq_one (h : Sec4Hyp T T₁ a T₂) {t t₁ t₂ f : G} (ht : t ∈ T)
    (ht₁ : t₁ ∈ T₁) (ht₁L : t₁ ∉ normIn T₁ T) (ht₂ : t₂ ∈ T₂) (ht₂L : t₂ ∉ normIn T₂ T)
    (hf : f ∈ normIn T₂ T) (hz : (t₂ * t * t₁ * t) * f * (t₂ * t * t₁ * t)⁻¹ = f) : f = 1 := by
  have hB := h.mem_normalizer_normIn
  have htN : t ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer ht
  have htY : t ∈ sec4Y T T₁ T₂ := left_le_sec4Y ht
  have hNN := h.sec4Y_le_normalizer
  have hNconj : ∀ n ∈ sec4N T T₁ T₂, ∀ y ∈ sec4Y T T₁ T₂, y * n * y⁻¹ ∈ sec4N T T₁ T₂ :=
    fun n hn y hy => conj_mem_of_mem_normalizer (hNN hy) hn
  have htt : t * t = 1 := elemAbelian_mul_self h.pair.wc.1 ht
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set V : Subgroup G := conjSubgroup t T₁ with hV
  obtain ⟨x, hx⟩ := h.pair.conj
  obtain ⟨y₂, hy₂⟩ := h.conj
  have hVconj : ∃ v : G, V = conjSubgroup v T := ⟨t * x, by rw [hV, hx, conjSubgroup_conjSubgroup]⟩
  have hT₂conj : ∃ v : G, T₂ = conjSubgroup v T := ⟨y₂, hy₂⟩
  have hL₂V : normIn T₂ T ≤ normIn T₂ V := by
    intro n hn
    obtain ⟨hnT₂, -⟩ := mem_normIn.1 hn
    refine mem_normIn.2 ⟨hnT₂, ?_⟩
    rw [hV, mem_normalizer_conjSubgroup_iff]
    have : t⁻¹ * n * t⁻¹⁻¹ ∈ sec4N T T₁ T₂ :=
      hNconj n (normIn_le_sec4N_right hn) t⁻¹ ((sec4Y T T₁ T₂).inv_mem htY)
    exact h.sec4N_le_normalizer_mid (by simpa using this)
  have hne : V ≠ T₂ := by
    intro hVT₂
    have ha1 : a ∈ normIn T₂ T := h.mem_normIn₂
    rw [← hVT₂, hV, normIn_conj_right_of_mem_normalizer htN T₁] at ha1
    obtain ⟨e, he, hae⟩ := mem_conjSubgroup_iff_exists.1 ha1
    have heM : e ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_right T T₁ he
    have : a ∈ cfgM T T₁ := by
      rw [hae]
      exact h.sec3.cfg.conj_mem_cfgM (Subgroup.mem_sup_left ht) heM
    have hM : cfgM T T₁ ≤ T ⊔ normIn T₁ T := sup_le_sup_right (normIn_le T T₁) _
    exact h.haL (hM this)
  have hS'' : Sec3 T₂ V := sec3_of_conj_conj h.glob hT₂conj hVconj hne (by
    intro h0
    apply h.normIn₂_ne_bot
    exact eq_bot_iff.2 fun x hx => by
      have := hL₂V hx
      rw [h0] at this
      exact this)
  have hcardL₂ : Nat.card (normIn T₂ T) = Nat.card (normIn T T₁) := h.card_normIn₂_eq hB
  have hcard1 : Nat.card (normIn T₂ V) ≤ Nat.card (normIn T T₁) :=
    h.pair.card_normIn_le hT₂conj hVconj hne
  have hnormL₂ : normIn T₂ V = normIn T₂ T :=
    (Subgroup.eq_of_le_of_card_ge hL₂V (by rw [hcardL₂]; exact hcard1)).symm
  have ht₂M : t₂ ∉ cfgM T₂ V := fun hM => ht₂L (by
    have : t₂ ∈ normIn T₂ V := by
      rw [← hS''.cfg.inf_cfgM]
      exact ⟨ht₂, hM⟩
    rwa [hnormL₂] at this)
  have hL₁V : conjSubgroup t (normIn T₁ T) ≤ normIn V T₂ := by
    intro n hn
    obtain ⟨e, he, rfl⟩ := mem_conjSubgroup_iff_exists.1 hn
    refine mem_normIn.2 ⟨conj_mem_conjSubgroup t (normIn_le T₁ T he), ?_⟩
    exact h.sec4N_le_normalizer_right (hNconj e (normIn_le_sec4N_mid he) t htY)
  have hcard2 : Nat.card (normIn V T₂) ≤ Nat.card (normIn T T₁) :=
    h.pair.card_normIn_le hVconj hT₂conj hne.symm
  have hnormV : normIn V T₂ = conjSubgroup t (normIn T₁ T) :=
    (Subgroup.eq_of_le_of_card_ge hL₁V (by
      rw [card_conjSubgroup, h.card_normIn₁]; exact hcard2)).symm
  have hsV : t * t₁ * t⁻¹ ∈ V := conj_mem_conjSubgroup t ht₁
  have hst : t * t₁ * t = t * t₁ * t⁻¹ := by rw [hti]
  have hsM : t * t₁ * t ∉ cfgM T₂ V := fun hM => ht₁L (by
    have h1 : t * t₁ * t⁻¹ ∈ normIn V T₂ := by
      rw [← hS''.cfg.inf_cfgM_right]
      exact ⟨hsV, by rw [← hst]; exact hM⟩
    rw [hnormV] at h1
    obtain ⟨e, he, hee⟩ := mem_conjSubgroup_iff_exists.1 h1
    have : t₁ = e := by
      have h2 : t * t₁ * t⁻¹ = t * e * t⁻¹ := hee
      calc t₁ = t⁻¹ * (t * t₁ * t⁻¹) * t := by group
        _ = t⁻¹ * (t * e * t⁻¹) * t := by rw [h2]
        _ = e := by group
    rw [this]
    exact he)
  obtain ⟨y₀, hy₀X, hy₀⟩ := hS''.conj
  have hsy : t * t₁ * t ∈ conjSubgroup y₀ T₂ := by
    rw [← hy₀, hst]
    exact hsV
  have hxy : conjSubgroup 1 T₂ ≠ conjSubgroup y₀ T₂ := by
    rw [conjSubgroup_one, ← hy₀]
    exact hne.symm
  have hC := hS''.cfgM_inf_centralizer_inf_centralizer (x := 1) (y := y₀)
    (T₂ ⊔ V).one_mem hy₀X hxy (by rw [conjSubgroup_one]; exact ht₂) ht₂M hsy hsM
  have ht₂t₂ : t₂ * t₂ = 1 := elemAbelian_mul_self h.isWC₂.1 ht₂
  have ht₁t₁ : t₁ * t₁ = 1 := elemAbelian_mul_self h.isWC₁.1 ht₁
  have hss : (t * t₁ * t) * (t * t₁ * t) = 1 := by
    have : t * t₁ * t * (t * t₁ * t) = t * (t₁ * (t * t) * t₁) * t := by group
    rw [this, htt, mul_one, ht₁t₁, mul_one, htt]
  have hfM : f ∈ cfgM T₂ V := Cfg.normIn_le_cfgM_left T₂ V (hL₂V hf)
  have e : t₂ * t * t₁ * t = t₂ * (t * t₁ * t) := by group
  rw [e] at hz
  exact eq_one_of_conj_mul_eq_of_inf_centralizer hS''.cfg.isElemAbelian_cfgM ht₂t₂ hss
    (fun m hm => hS''.cfg.conj_mem_cfgM (Subgroup.mem_sup_left ht₂) hm) hC hfM hz

end CFSG.CGT.Timmesfeld75
