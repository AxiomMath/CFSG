module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace L34R

variable {Q : Type} [Group Q] [Finite Q]

theorem pPrimeCore_eq_bot (hQ : IsQuasisimple Q) (hZ : IsPGroup 2 (center Q))
    (h2 : 2 ∣ Nat.card Q) : pPrimeCore 2 Q = ⊥ := by
  have hodd : Odd (Nat.card (pPrimeCore 2 Q)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rcases LocalCores.quasisimple_normal_subgroups hQ
      (inferInstance : (pPrimeCore 2 Q).Normal) with h | h
  · exfalso
    rw [h, card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    obtain ⟨k, hk⟩ := hZ ⟨x, h hx⟩
    have h1 : orderOf x ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    have h2' : orderOf x ∣ Nat.card (pPrimeCore 2 Q) := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : pPrimeCore 2 Q)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 Q)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2')

theorem exists_properFixedComponent (hQ : IsQuasisimple Q)
    (hZ : IsPGroup 2 (center Q))
    {σ : MulAut Q} (hσ : ∀ y, σ (σ y) = y) {P : Subgroup Q} (hPF : P ≤ fixedSubgroup σ)
    (hP : IsPComponent 2 (P.subgroupOf (fixedSubgroup σ))) (hPne : P ≠ ⊤)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) :
    ∃ (σ' : MulAut (Q ⧸ center Q)) (P' : Subgroup (Q ⧸ center Q)),
      CatLeaf.ProperFixedComponent σ' P' ∧ IsL34Type (P' ⧸ Open.fusionZStar P') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card Q := by
    have hc : Nat.card (P ⧸ Open.fusionZStar P) = 20160 := CatLeaf.card_of_isL34Type htype
    have hd := (Subgroup.card_quotient_dvd_card (Open.fusionZStar P)).trans
      (Subgroup.card_subgroup_dvd_card P)
    rw [hc] at hd
    exact (show 2 ∣ 20160 by norm_num).trans hd
  have hO := pPrimeCore_eq_bot hQ hZ h2
  let eO : Q ⧸ pPrimeCore 2 Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hA : IsQuasisimple (Q ⧸ pPrimeCore 2 Q) :=
    LocalCores.isQuasisimple_of_mulEquiv eO.symm hQ
  have hlt : (pPrimeCore 2 P).index < (pPrimeCore 2 Q).index := by
    rw [hO, index_bot]
    have h1 : (pPrimeCore 2 P).index ≤ Nat.card P := by
      rw [index_eq_card]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have h3 : P.index ≠ 1 := fun h => hPne (index_eq_one.mp h)
    have h4 : P.index ≠ 0 := index_ne_zero_of_finite
    have h5 := P.card_mul_index
    have h6 : Nat.card P < Nat.card Q := by
      have : 2 ≤ P.index := by omega
      have hpos : 0 < Nat.card P := Nat.card_pos
      calc Nat.card P < Nat.card P * 2 := by omega
        _ ≤ Nat.card P * P.index := Nat.mul_le_mul_left _ this
        _ = Nat.card Q := h5
    omega
  obtain ⟨σ₁, P₁, hσ₁, hP₁F, hP₁, hP₁ne, ⟨e₁⟩⟩ :=
    exists_simple_fixed_component hA σ hσ hPF hP hlt
  let eS : (Q ⧸ pPrimeCore 2 Q) ⧸ center (Q ⧸ pPrimeCore 2 Q) ≃* Q ⧸ center Q :=
    Sol78.centerQuotCongr eO
  obtain ⟨hmap, ⟨e₂⟩⟩ := CatLeaf.ProperFixedComponent.map eS
    (show CatLeaf.ProperFixedComponent σ₁ P₁ from ⟨hσ₁, hP₁F, hP₁, hP₁ne⟩)
  exact ⟨_, _, hmap, LieType.CurtisTits.lieModel_of_mulEquiv (e₁.trans e₂) htype⟩

end L34R

end CFSG.ComponentClassification.GrSLit
