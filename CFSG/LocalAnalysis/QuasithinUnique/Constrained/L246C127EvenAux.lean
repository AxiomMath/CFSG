module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace L246C127

variable {G : Type} [Group G]

section CharTwo

variable [Finite G]

theorem charTwo_subgroupOf_of_le {A H : Subgroup G} (hHA : H ≤ A) (h : CharTwo H) :
    CharTwo (H.subgroupOf A) := by
  have hQH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hQN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  set Q' : Subgroup ↥A := (pCoreOf 2 H).subgroupOf A with hQ'
  set H' : Subgroup ↥A := H.subgroupOf A with hH'
  have hQ'H' : Q' ≤ H' := fun x hx => hQH hx
  have hQ'2 : IsPGroup 2 ↥Q' :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe (hQH.trans hHA)).symm
  have hH'N : H' ≤ Subgroup.normalizer (Q' : Set ↥A) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxH : (x : G) ∈ H := hx
    have := Subgroup.mem_normalizer_iff.1 (hQN hxH) (y : G)
    simpa [hQ', Subgroup.mem_subgroupOf] using this
  have hQ'P : Q' ≤ pCoreOf 2 H' := C1.le_pCoreOf_of_normalized hQ'H' hH'N hQ'2
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxH, hxC⟩ := hx
  have hxQ : (x : G) ∈ pCoreOf 2 H := by
    refine h (Subgroup.mem_inf.2 ⟨hxH, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩)
    have hq' : (⟨q, hQH.trans hHA hq⟩ : ↥A) ∈ pCoreOf 2 H' := hQ'P hq
    have := Subgroup.mem_centralizer_iff.1 hxC _ hq'
    exact congrArg Subtype.val this
  exact hQ'P hxQ

end CharTwo

section Good

variable {A B : Type} [Group A] [Group B]

@[expose] def Good2 (A : Type) [Group A] : Prop :=
  Nat.card A = 3 ∨ (IsSimpleGroup A ∧ ¬ IsPGroup 2 A)

theorem Good2.of_mulEquiv (e : A ≃* B) (h : Good2 A) : Good2 B := by
  rcases h with h | ⟨hs, hp⟩
  · exact Or.inl (by rw [← Nat.card_congr e.toEquiv]; exact h)
  · exact Or.inr ⟨(MulEquiv.isSimpleGroup_congr e).1 hs, fun hB => hp (hB.of_equiv e.symm)⟩

theorem Good2.nontrivial (h : Good2 A) : Nontrivial A := by
  rcases h with h | ⟨hs, -⟩
  · have : Finite A := Nat.finite_of_card_ne_zero (by omega)
    exact Finite.one_lt_card_iff_nontrivial.1 (by omega)
  · exact hs.toNontrivial

theorem Good2.noTwoNormal [Finite A] (h : Good2 A) :
    ∀ N : Subgroup A, N.Normal → IsPGroup 2 ↥N → N = ⊥ := by
  intro N hN hN2
  rcases h with h | ⟨hs, hp⟩
  · refine eq_bot_iff.2 fun x hx => ?_
    have h1 : orderOf x ∣ 3 := h ▸ orderOf_dvd_natCard x
    obtain ⟨k, hk⟩ := hN2 ⟨x, hx⟩
    have h2 : orderOf x ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hk
    have h3 : orderOf x ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
    have : Nat.gcd 3 (2 ^ k) = 1 := (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
    rw [this, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact Subgroup.mem_bot.2 h3
  · rcases hs.eq_bot_or_eq_top_of_normal N with h' | h'
    · exact h'
    · exfalso
      apply hp
      subst h'
      exact hN2.of_equiv (Subgroup.topEquiv : ↥(⊤ : Subgroup A) ≃* A)

theorem Good2.noTwoQuot [Finite A] (h : Good2 A) :
    ∀ (N : Subgroup A) [N.Normal], IsPGroup 2 (A ⧸ N) → N = ⊤ := by
  intro N hN hq
  rcases h with h | ⟨hs, hp⟩
  · have hdvd : Nat.card N ∣ 3 := h ▸ Subgroup.card_subgroup_dvd_card N
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exfalso
      have hbot : N = ⊥ := Subgroup.eq_bot_of_card_eq N h1
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h3 : 3 ∣ Nat.card A := by rw [h]
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 h3
      obtain ⟨k, hk⟩ := hq (QuotientGroup.mk x)
      have h4 : x ^ 2 ^ k ∈ N := by
        have : (QuotientGroup.mk (x ^ 2 ^ k) : A ⧸ N) = 1 := by
          rw [QuotientGroup.mk_pow]; exact hk
        exact (QuotientGroup.eq_one_iff _).1 this
      rw [hbot, Subgroup.mem_bot] at h4
      have : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h4
      rw [hx] at this
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this) (by norm_num)
    · exact Subgroup.eq_top_of_card_eq N (by rw [h1, h])
  · rcases hs.eq_bot_or_eq_top_of_normal N with h' | h'
    · exfalso
      apply hp
      subst h'
      exact hq.of_equiv QuotientGroup.quotientBot
    · exact h'

theorem good2_alt {n : ℕ} (hn : n = 3 ∨ n = 5) : Good2 (alternatingGroup (Fin n)) := by
  rcases hn with rfl | rfl
  · left
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  · right
    refine ⟨Bridge.alt_isSimple (by norm_num), fun hp => ?_⟩
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have h3 : 3 ∣ 2 ^ k := by rw [← hk, h60]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

end Good

end L246C127

end CFSG.QuasithinUnique
