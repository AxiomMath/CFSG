module

public import CFSG.CGT.T75H.QuotZ
public import CFSG.CGT.Timmesfeld75.Sec6Four

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] def sStar (T T₁ : Subgroup G) : Subgroup G := T ⊔ normIn T₁ T

theorem le_sStar_left : T ≤ sStar T T₁ := le_sup_left

theorem normIn_le_sStar : normIn T₁ T ≤ sStar T T₁ := le_sup_right

theorem normIn_inf_left_eq_bot [Finite G] (hS3 : Sec3 T T₁) : normIn T₁ T ⊓ T = ⊥ := by
  refine le_antisymm ?_ bot_le
  calc normIn T₁ T ⊓ T ≤ T ⊓ T₁ := le_inf inf_le_right (inf_le_left.trans (normIn_le T₁ T))
    _ = ⊥ := hS3.cfg.inf

theorem card_mul_le_card_sStar [Finite G] (hL₁T : normIn T₁ T ⊓ T = ⊥) :
    Nat.card (normIn T₁ T) * Nat.card T ≤ Nat.card (sStar T T₁) := by
  let f : ↥(normIn T₁ T) × ↥T → ↥(sStar T T₁) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), (sStar T T₁).mul_mem (normIn_le_sStar p.1.2) (le_sStar_left p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨u, hu⟩, ⟨t, ht⟩⟩ ⟨⟨u', hu'⟩, ⟨t', ht'⟩⟩ h
    have h' : u * t = u' * t' := congrArg Subtype.val h
    have h2 : u'⁻¹ * u = t' * t⁻¹ := by
      calc u'⁻¹ * u = u'⁻¹ * (u * t) * t⁻¹ := by group
        _ = u'⁻¹ * (u' * t') * t⁻¹ := by rw [h']
        _ = t' * t⁻¹ := by group
    have h3 : u'⁻¹ * u ∈ normIn T₁ T ⊓ T :=
      ⟨(normIn T₁ T).mul_mem ((normIn T₁ T).inv_mem hu') hu, by
        rw [h2]; exact T.mul_mem ht' (T.inv_mem ht)⟩
    rw [hL₁T, Subgroup.mem_bot] at h3
    have hu2 : u = u' := (inv_mul_eq_one.1 h3).symm
    subst hu2
    have : t = t' := mul_left_cancel h'
    subst this
    rfl
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at this

theorem isPGroup_sStar [Finite G] (hS3 : Sec3 T T₁) : IsPGroup 2 (sStar T T₁) := by
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  have hT2 : IsPGroup 2 T := isPGroup_two_of_isElemAbelian hS3.cfg.wc.1
  have hL₁2 : IsPGroup 2 (normIn T₁ T) :=
    (isPGroup_two_of_isElemAbelian hS3.cfg.wc₁.1).to_le (normIn_le T₁ T)
  exact IsPGroup.to_sup_of_normal_left' hT2 hL₁2 hL₁N

theorem exists_sylow_sStar [Finite G] (h1 : Sec4NoA) (h63 : Sec63) (hc : Sec6Ctx T T₁ 2 1)
    (h48 : IsWC (barSub T (normIn T₁ T))) :
    ∃ S : Sylow 2 G, sStar T T₁ ≤ S ∧ (∀ s ∈ S, s ∈ Subgroup.normalizer (T : Set G)) ∧
      (S : Subgroup G) ⊓ hSub T (normIn T₁ T) = sStar T T₁ ∧
      (∀ y ∈ (S : Subgroup G), y ∈ classD T → y ∈ sStar T T₁) := by
  have hS3 := hc.sec3
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  have hL₁T := normIn_inf_left_eq_bot hS3
  obtain ⟨S, hS⟩ := (isPGroup_sStar hS3).exists_le_sylow
  have hTS : T ≤ (S : Subgroup G) := le_sStar_left.trans hS
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (T : Set G) := by
    intro s hs
    refine mem_normalizer_of_conjSubgroup_eq (eq_of_conj_le_pGroup hc.hy.pair.wc S.isPGroup' hTS ?_)
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs (hTS ht))
      ((S : Subgroup G).inv_mem hs)
  have hcard8 : 8 ≤ Nat.card (sStar T T₁) := by
    have := card_mul_le_card_sStar hL₁T
    rwa [card_normIn_swap_two hc, show Nat.card T = 4 by simpa using hc.hT] at this
  have hSH : (S : Subgroup G) ⊓ hSub T (normIn T₁ T) = sStar T T₁ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (le_inf hS (sup_le left_le_hSub le_hSub)) ?_
    exact (card_le_eight_of_pGroup_le hc h48 (S.isPGroup'.to_inf_left) inf_le_right).trans hcard8
  refine ⟨S, hS, hSN, hSH, fun y hyS hyD => ?_⟩
  have hyN := hSN y hyS
  have hyH : y ∈ hSub T (normIn T₁ T) :=
    hc.normD_le_hSub_of_not_a8 h1 h63 (by omega) ⟨hyD, hyN⟩
  rw [← hSH]
  exact ⟨hyS, hyH⟩

end CFSG.CGT.T75H
