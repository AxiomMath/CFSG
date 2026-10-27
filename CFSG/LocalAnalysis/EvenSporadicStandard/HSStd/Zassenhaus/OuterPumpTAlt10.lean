module

public import CFSG.Foundations.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.OddStandard.GlueAlt

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Equiv Equiv.Perm

theorem sign_eq_neg_one_of_orderOf_fourteen (σ : Perm (Fin 10)) (h : orderOf σ = 14) :
    sign σ = -1 := by
  have hl := Equiv.Perm.lcm_cycleType σ
  have hs := Equiv.Perm.sum_cycleType σ
  have hle : σ.support.card ≤ 10 := by simpa using Finset.card_le_univ σ.support
  have h2 : ∀ n ∈ σ.cycleType, 2 ≤ n := fun n hn => Equiv.Perm.two_le_of_mem_cycleType hn
  have hdvd : ∀ n ∈ σ.cycleType, n ∣ 14 := fun n hn => h ▸ hl ▸ Multiset.dvd_lcm hn
  have hle10 : ∀ n ∈ σ.cycleType, n ≤ 10 := fun n hn =>
    (Multiset.le_sum_of_mem hn).trans (hs ▸ hle)
  have hmem : ∀ n ∈ σ.cycleType, n = 2 ∨ n = 7 := by
    intro n hn
    have h1 := hdvd n hn
    have h2' := h2 n hn
    have h3 := hle10 n hn
    interval_cases n <;> omega
  have ha : 7 ∈ σ.cycleType := by
    by_contra hno
    have : σ.cycleType.lcm ∣ 2 := Multiset.lcm_dvd.2 fun n hn => by
      rcases hmem n hn with rfl | rfl
      · exact dvd_rfl
      · exact absurd hn hno
    rw [hl, h] at this
    omega
  have hb : 2 ∈ σ.cycleType := by
    by_contra hno
    have : σ.cycleType.lcm ∣ 7 := Multiset.lcm_dvd.2 fun n hn => by
      rcases hmem n hn with rfl | rfl
      · exact absurd hn hno
      · exact dvd_rfl
    rw [hl, h] at this
    omega
  obtain ⟨c, hc⟩ : ∃ c, σ.cycleType = 7 ::ₘ 2 ::ₘ c := by
    obtain ⟨c1, hc1⟩ := Multiset.exists_cons_of_mem ha
    have hb1 : 2 ∈ c1 := by
      have : 2 ∈ (7 ::ₘ c1) := hc1 ▸ hb
      simpa using this
    obtain ⟨c2, hc2⟩ := Multiset.exists_cons_of_mem hb1
    exact ⟨c2, by rw [hc1, hc2]⟩
  have hcs : c = 0 := by
    rw [hc] at hs
    simp at hs
    have hc2 : ∀ n ∈ c, 2 ≤ n := fun n hn => h2 n (by rw [hc]; simp [hn])
    by_contra hne
    obtain ⟨n, hn⟩ := Multiset.exists_mem_of_ne_zero hne
    have := Multiset.le_sum_of_mem hn
    have := hc2 n hn
    omega
  rw [Equiv.Perm.sign_of_cycleType, hc, hcs]
  simp
  decide

theorem card_alternatingGroup_eight_T : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem center_eq_bot_of_alt8_le_alt10 {G : Type} [Group G] [Finite G] {M K : Subgroup G}
    (eM : Nonempty (↥M ≃* alternatingGroup (Fin 10))) (hKM : K ≤ M)
    (hq : CFSG.IsQuasisimple ↥K)
    (e : Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 8))) : center ↥K = ⊥ := by
  obtain ⟨φ⟩ := eM
  obtain ⟨e⟩ := e
  have hperf : Group.IsPerfect ↥K := hq.1
  have hle := CFSG.OddStandard.GlueAlt.card_center_le_two_of_alt (n := 8) le_rfl e
  by_contra hne
  have hpos : 0 < Nat.card (center ↥K) := Nat.card_pos
  have h2 : Nat.card (center ↥K) = 2 := by
    have : Nat.card (center ↥K) ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
    omega
  have hK : Nat.card ↥K = 20160 * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥K), h2, Nat.card_congr e.toEquiv,
      card_alternatingGroup_eight_T]
  have hf2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hf7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center ↥K) 2 (h2 ▸ dvd_rfl)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 7 (by rw [hK]; norm_num)
  have hz2 : orderOf (z : ↥K) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hcomm : Commute x (z : ↥K) := Subgroup.mem_center_iff.1 z.2 x
  have hy : orderOf (x * (z : ↥K)) = 14 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx, hz2]; norm_num), hx, hz2]
  let ψ : ↥K →* Perm (Fin 10) :=
    (alternatingGroup (Fin 10)).subtype.comp (φ.toMonoidHom.comp (Subgroup.inclusion hKM))
  have hψ : Function.Injective ψ := by
    refine Subtype.val_injective.comp (φ.injective.comp (Subgroup.inclusion_injective hKM))
  have ho : orderOf (ψ (x * (z : ↥K))) = 14 := by rw [orderOf_injective ψ hψ, hy]
  have hsgn : sign (ψ (x * (z : ↥K))) = 1 :=
    mem_alternatingGroup.1 (φ (Subgroup.inclusion hKM (x * (z : ↥K)))).2
  rw [sign_eq_neg_one_of_orderOf_fourteen _ ho] at hsgn
  exact absurd hsgn (by decide)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
