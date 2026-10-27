module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalance
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.Sporadic.He.Simple
public import Certificates.Certificate3168
public import CFSG.ClassicalInvolution.Balance.LocalBalance
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

theorem exists_mul_ne_held : ∃ a b : Blueprint.NativeSporadic.He, a * b ≠ b * a := by
  have : IsSimpleGroup Blueprint.NativeSporadic.He := Sporadic.He.isSimpleGroup_He
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h
  push Not at h
  have hcard := Sporadic.He.card_He
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Blueprint.NativeSporadic.He) 2
    (by rw [hcard]; norm_num)
  have hn : (zpowers g).Normal := by
    constructor
    intro x hx y
    rw [h y x, mul_inv_cancel_right]
    exact hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers g) with hb | ht
  · rw [zpowers_eq_bot] at hb
    rw [hb, orderOf_one] at hg
    exact absurd hg (by norm_num)
  · have h1 := Nat.card_zpowers g
    rw [ht, card_top, hcard, hg] at h1
    exact absurd h1 (by norm_num)

theorem nonempty_fusionZStar_equiv_held {J : Type*} [Group J]
    (e : J ⧸ pPrimeCore 2 J ≃* Blueprint.NativeSporadic.He) :
    Nonempty (J ⧸ Open.fusionZStar J ≃* Blueprint.NativeSporadic.He) := by
  have : IsSimpleGroup Blueprint.NativeSporadic.He := Sporadic.He.isSimpleGroup_He
  have hZ : center Blueprint.NativeSporadic.He = ⊥ := center_eq_bot_of_simple exists_mul_ne_held
  have heq : Open.fusionZStar J = pPrimeCore 2 J := by
    ext l
    rw [GSThmB.OddQuot.mem_fusionZStar_iff]
    constructor
    · intro h
      have hc : QuotientGroup.mk' (pPrimeCore 2 J) l ∈ center (J ⧸ pPrimeCore 2 J) := by
        rw [mem_center_iff]
        intro q
        obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 J) q
        have h1 := (QuotientGroup.eq_one_iff _).mpr (h m)
        rw [← QuotientGroup.mk'_apply, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1.symm
      have hc' : e (QuotientGroup.mk' (pPrimeCore 2 J) l) ∈ center Blueprint.NativeSporadic.He := by
        rw [mem_center_iff]
        intro y
        obtain ⟨q, rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul, mem_center_iff.mp hc q]
      rw [hZ, mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hc'
      exact hc'
    · intro hl m
      have hn : (pPrimeCore 2 J).Normal := inferInstance
      rw [commutatorElement_def]
      have h1 : m * l⁻¹ * m⁻¹ ∈ pPrimeCore 2 J := hn.conj_mem _ (inv_mem hl) m
      have h2 := mul_mem hl h1
      rwa [show l * (m * l⁻¹ * m⁻¹) = l * m * l⁻¹ * m⁻¹ by group] at h2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans e⟩

end CFSG.ComponentClassification.GrSLit
