module

public import CFSG.CGT.T75O.Fusion

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

namespace Cfg56

variable (c : Cfg56 T T₁)
include c

theorem exists_mem_secA_ne_one : ∃ a ∈ secA T T₁, a ≠ 1 := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.secA_ne_bot
  exact ⟨a, ha, fun h => ha1 (Subtype.ext h)⟩

theorem setup {t : G} (ht : t ∈ secA T T₁) (ht1 : t ≠ 1) : CorB.Setup t where
  orderOf_eq :=
    orderOf_eq_prime (by simpa [pow_two] using c.mul_self_T (secA_le_left ht)) ht1
  isPGroup := c.isPGroup_sup.to_le ((Subgroup.closure_le _).2 (c.conjCent_subset ht ht1))
  class_two := c.class_two_of_le_sup ((Subgroup.closure_le _).2 (c.conjCent_subset ht ht1))
  fusion := c.fusion ht ht1

theorem false_of_listGroup (hL : ListWCIdentification) (hLG : ListGroup G) : False := by
  have := c.hy.finite
  have := c.hy.simple
  have hstd := hL G hLG T c.hy.pair.wc c.hy.card
  obtain ⟨a, ha, ha1⟩ := c.exists_mem_secA_ne_one
  obtain ⟨g, hg⟩ := c.exists_isUIdx
  obtain ⟨f, hf, -, hcard⟩ := c.card_secA_eq hg
  have hTA : T ≤ secA T T₁ := by
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]
      exact one_mem _
    · obtain ⟨n, hn, hnat⟩ := hstd.transitive a (secA_le_left ha) ha1 t ht ht1
      have h1 := conj_mem_conjSubgroup n ha
      rw [conjSubgroup_secA hn] at h1
      rw [← hnat]
      exact h1
  have hTL : T ≤ normIn T T₁ := hTA.trans secA_le_normIn
  have hle : Nat.card T ≤ Nat.card (normIn T T₁) := Subgroup.card_le_of_le hTL
  have hpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have h2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hf)
  rw [hcard] at hle
  nlinarith

end Cfg56

@[expose] def Sec56ExclAt (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), Cfg56 T T₁ →
    ∀ (Y : Type) [Group Y], Nonempty (G ≃* Y) → ¬ P Y

end CFSG.CGT.T75O
