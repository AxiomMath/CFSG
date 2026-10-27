module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Blocks

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit
open CFSG.RankThree.PartOne (IsShortGroup)
open scoped commutatorElement

namespace QBlock

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem oddCore_eq_bot (h : QBlock K) : CFSG.oddCore ↥K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CFSG.IsCharacteristicP 2 ↥K :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥K 2).mpr h.short.fitting_eq
  unfold CFSG.oddCore
  refine sSup_eq_bot.2 ?_
  rintro N ⟨hNn, hNodd⟩
  have hP : IsPGroup 2 (pCore 2 ↥K) := pCore_isPGroup
  have hNP : N ⊓ pCore 2 ↥K = ⊥ := by
    have h2 : IsPGroup 2 ↥(N ⊓ pCore 2 ↥K) := hP.to_inf_right
    have hodd : Odd (Nat.card ↥(N ⊓ pCore 2 ↥K)) :=
      hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    rcases h2.card_eq_or_dvd with h1 | h1
    · exact (Subgroup.eq_bot_iff_card _).2 h1
    · exact absurd (even_iff_two_dvd.2 h1) (Nat.not_even_iff_odd.2 hodd)
  have hcent : N ≤ Subgroup.centralizer (pCore 2 ↥K : Set ↥K) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h1 : p * n * p⁻¹ * n⁻¹ ∈ N ⊓ pCore 2 ↥K := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact N.mul_mem (hNn.conj_mem n hn p) (N.inv_mem hn)
      · have : p * (n * p⁻¹ * n⁻¹) ∈ pCore 2 ↥K :=
          (pCore 2 ↥K).mul_mem hp ((inferInstance : (pCore 2 ↥K).Normal).conj_mem _
            ((pCore 2 ↥K).inv_mem hp) n)
        simpa [mul_assoc] using this
    rw [hNP, Subgroup.mem_bot] at h1
    calc p * n = (p * n * p⁻¹ * n⁻¹) * n * p := by group
      _ = n * p := by rw [h1]; group
  have hNle : N ≤ pCore 2 ↥K := hcent.trans hchar
  exact le_bot_iff.1 (hNP ▸ le_inf le_rfl hNle)

omit [Finite G] in
theorem le_of_isPGroup_normal' {M T N : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) [Finite G] (hNM : N ≤ M)
    (hn : M ≤ Subgroup.normalizer (N : Set G)) (hN : IsPGroup 2 N) : N ≤ T := by
  have h1 : IsPGroup 2 (N ⊔ T : Subgroup G) :=
    hN.to_sup_of_normal_left' hT.isPGroup (hT.le.trans hn)
  have h2 := hT.eq_of_le le_sup_right (sup_le hNM hT.le) h1
  exact le_sup_left.trans h2.le

theorem four_mul_card_le_sylow (h : QBlock K) {B : Subgroup G}
    (hB : CFSG.ABGLocalTools.IsSylowOf 2 B K) :
    4 * Nat.card ↥(oTwoIn K) ≤ Nat.card ↥B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQnt : Nontrivial (↥K ⧸ pCore 2 ↥K) := by
    have : Nontrivial ((↥K ⧸ pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ pCore 2 ↥K)) :=
      h.quasisimple.2.1.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center (↥K ⧸ pCore 2 ↥K))).nontrivial
  have hQperf : Group.IsPerfect (↥K ⧸ pCore 2 ↥K) := h.quasisimple.1
  have h4 : 4 ∣ Nat.card (↥K ⧸ pCore 2 ↥K) := four_dvd_card_of_perfect
  have hKcard : Nat.card ↥K = Nat.card (↥K ⧸ pCore 2 ↥K) * Nat.card (pCore 2 ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hOcard : Nat.card ↥(oTwoIn K) = Nat.card (pCore 2 ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  obtain ⟨e, he⟩ := (pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
  have hK0 : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
  have h4' : 2 ^ 2 ∣ Nat.card (↥K ⧸ pCore 2 ↥K) := (by norm_num : (4 : ℕ) = 2 ^ 2) ▸ h4
  have hdvd : 2 ^ (e + 2) ∣ Nat.card ↥K := by
    rw [hKcard, he, pow_add, mul_comm (2 ^ e)]
    exact Nat.mul_dvd_mul h4' (dvd_refl _)
  have hle : e + 2 ≤ (Nat.card ↥K).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hK0).1 hdvd
  rw [hB.card_eq, hOcard, he, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, add_comm]
  exact Nat.pow_le_pow_right (by norm_num) hle

end QBlock

end CFSG.CGT.PushingUpLit.LIT.Foote
