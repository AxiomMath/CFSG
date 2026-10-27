module

public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.CGT.Timmesfeld75.Sec5Basic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ S : Subgroup G} {a : G}

structure SecB6 (T T₁ S : Subgroup G) (a : G) : Prop where
  sec : Sec3 T T₁
  two : IsPGroup 2 S
  hL₁S : normIn T₁ T ≤ S
  haS : a ∈ S
  haa : a * a = 1
  haN : a ∈ Subgroup.normalizer (T : Set G)
  haNL : a ∈ Subgroup.normalizer (normIn T T₁ : Set G)
  hne : conjSubgroup a T₁ ≠ T₁
  hcomm : ∀ e ∈ normIn T₁ T, ∀ f ∈ conjSubgroup a (normIn T₁ T), e * f = f * e
  hcard : Nat.card T = Nat.card (normIn T T₁) * 2

namespace SecB6

variable (h : SecB6 T T₁ S a)

include h

theorem normIn_le_normalizer_conj [Finite G] : normIn T₁ T ≤ normIn T₁ (conjSubgroup a T₁) := by
  have hbot : conjSubgroup a (normIn T₁ T) ≠ ⊥ := fun h0 =>
    h.sec.cfg.ne₁ (conjSubgroup_eq_bot_iff.1 h0)
  obtain ⟨f', hf'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
  have hf : (f' : G) ∈ conjSubgroup a (normIn T₁ T) := f'.2
  have hf1 : (f' : G) ≠ 1 := fun h1 => hf' (Subtype.ext h1)
  have hfP : (f' : G) ∈ conjSubgroup a T₁ := conjSubgroup_mono (normIn_le T₁ T) hf
  intro e he
  refine mem_normIn.2 ⟨normIn_le T₁ T he, ?_⟩
  exact (h.sec.cfg.wc₁.conj a).centralizer_le_normalizer hfP hf1
    (Subgroup.mem_centralizer_singleton_iff.2 (h.hcomm e he f' hf))

theorem sec₂ [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) :
    Sec3 T₁ (conjSubgroup a T₁) :=
  Sec3.of_inputs h214 hInv h.sec.cfg.wc₁ h.hne (fun h0 => h.sec.cfg.ne₁ (eq_bot_iff.2
    (fun e he => by
      have := h.normIn_le_normalizer_conj he
      rw [h0, Subgroup.mem_bot] at this
      exact this)))

theorem conj_conj_eq (K : Subgroup G) : conjSubgroup a (conjSubgroup a K) = K := by
  rw [conjSubgroup_conjSubgroup, h.haa, conjSubgroup_one]

theorem mem_normalizer_cfgM :
    a ∈ Subgroup.normalizer (cfgM T₁ (conjSubgroup a T₁) : Set G) := by
  apply mem_normalizer_of_conjSubgroup_eq
  rw [← cfgM_conj, h.conj_conj_eq, cfgM_symm]

theorem mem_normalizer_sup :
    a ∈ Subgroup.normalizer ((T₁ ⊔ conjSubgroup a T₁ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_sup_eq_sup, h.conj_conj_eq, sup_comm]

theorem card_T₁ [Finite G] : Nat.card T₁ = Nat.card (normIn T₁ T) * 2 := by
  obtain ⟨x₀, -, hx₀⟩ := h.sec.conj
  have h1 : Nat.card T₁ = Nat.card T := by rw [hx₀, card_conjSubgroup]
  have h2 : Nat.card (normIn T₁ T) = Nat.card (normIn T T₁) := h.sec.card_normIn_swap
  rw [h1, h2, h.hcard]

theorem normIn_conj_eq [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) :
    normIn T₁ (conjSubgroup a T₁) = normIn T₁ T := by
  have hS2 := h.sec₂ h214 hInv
  have hle := h.normIn_le_normalizer_conj
  have hlt : normIn T₁ (conjSubgroup a T₁) < T₁ := by
    rw [lt_iff_le_and_ne]
    refine ⟨normIn_le _ _, fun h0 => hS2.not_le_cfgM ?_⟩
    have h1 := Cfg.normIn_le_cfgM_left T₁ (conjSubgroup a T₁)
    rwa [h0] at h1
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hLpos : 0 < Nat.card (normIn T₁ T) := Nat.card_pos
  have h2 : Nat.card (normIn T₁ (conjSubgroup a T₁)) ∣ Nat.card T₁ :=
    Subgroup.card_dvd_of_le (normIn_le _ _)
  rw [hk, h.card_T₁] at h2
  have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hLpos h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with h1 | h1
  · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hk, h1, mul_one])).symm
  · exfalso
    rw [h1] at hk
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge (normIn_le _ _) (by rw [h.card_T₁, hk]))

theorem cfgM_eq_sup [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) :
    cfgM T₁ (conjSubgroup a T₁) = normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T) := by
  have e1 : normIn (conjSubgroup a T₁) T₁ =
      conjSubgroup a (normIn T₁ (conjSubgroup a T₁)) := by
    have := normIn_conj a T₁ (conjSubgroup a T₁)
    rwa [h.conj_conj_eq T₁] at this
  show normIn T₁ (conjSubgroup a T₁) ⊔ normIn (conjSubgroup a T₁) T₁ = _
  rw [e1, h.normIn_conj_eq h214 hInv]

end SecB6

end CFSG.CGT.Timmesfeld75
