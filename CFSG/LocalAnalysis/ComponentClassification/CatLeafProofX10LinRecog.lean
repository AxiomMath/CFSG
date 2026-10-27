module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpCard

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Lin

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof.X10Sp

@[expose] def IsClassicalTag (t : StatedLieTag) : Prop :=
  t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus

theorem lieOrder_of_lieModel_classical {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : IsClassicalTag t) (hp2 : p ≠ 2) (hn : n ≠ 0) (h : LieModel X t n p f) :
    Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) ∧
      (Nat.card X).factorization p = lieSylowExponent t n * f := by
  rcases ht with rfl | rfl | rfl | ht
  · exact lieOrder_of_lieModel (Or.inl rfl) hp2 hn h
  · exact lieOrder_of_lieModel (Or.inr (Or.inl rfl)) hp2 hn h
  · exact lieOrder_of_lieModel (Or.inr (Or.inr rfl)) hp2 hn h
  have hsc := GH74.statedClassicalModel_of_lieModel hn h
  have hadm := hsc.1
  have hp : p.Prime := hadm.1
  have hc : Nat.card X = lieOrderNumerator t n (p ^ f) / lieOrderDivisor t n (p ^ f) := by
    rcases ht with rfl | rfl | rfl
    · have hc := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hsc).2.2.2.1 rfl
      have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
      rw [hc, ordBC, ClassicalInvolution.gcd_two_sub_one_of_odd hodd, ← sq]
      rfl
    · rw [(ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hsc).2.2.2.2.1 rfl, ordD]
      rfl
    · rw [(ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hsc).2.2.2.2.2 rfl,
        ordTwistedD]
      rfl
  have hmul : Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) := by
    rw [hc, Nat.div_mul_cancel (lieOrderDivisor_dvd_numerator hadm)]
  have hnum : lieOrderNumerator t n (p ^ f) ≠ 0 := by
    rw [lieOrderNumerator_eq hadm]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hp.ne_zero)) (lieOrderCofactor_ne_zero hadm)
  have hX : Nat.card X ≠ 0 := fun h0 => hnum (by rw [← hmul, h0, zero_mul])
  refine ⟨hmul, ?_⟩
  have hfac := congrArg (fun m => m.factorization p) hmul
  rwa [Nat.factorization_mul hX (lieOrderDivisor_ne_zero hadm), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_lieOrderDivisor hadm), add_zero,
    factorization_lieOrderNumerator hadm] at hfac

theorem eq_psp4_of_two_lieModels {Y : Type} [Group Y] {t : StatedLieTag} {m p e f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (ht : IsClassicalTag t)
    (hadm : StatedLieAdmissible t m p e) (h : LieModel Y t m p e)
    (hX : LieModel Y .PSp 2 p f) : t = .PSp ∧ m = 2 ∧ e = f := by
  have he : 1 ≤ e := hadm.2.1
  have hm0 : m ≠ 0 := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fun h0 => by have := hadm.2.2.1; omega
    · exact fun h0 => by have := hadm.2.2.1; omega
    · exact fun h0 => by have := hadm.2.2.1; omega
    · exact fun h0 => by have := hadm.2.2.1; omega
    · exact fun h0 => by have : 4 ≤ m := hadm.2.2; omega
    · exact fun h0 => by have : 4 ≤ m := hadm.2.2; omega
  obtain ⟨h1, h1p⟩ := lieOrder_of_lieModel_classical ht hp2 hm0 h
  obtain ⟨h2, h2p⟩ := lieOrder_of_lieModel_classical (Or.inr (Or.inr (Or.inl rfl))) hp2
    (by norm_num) hX
  have hv := h1p.symm.trans h2p
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    have hm : 2 ≤ m := hadm.2.2.1
    rcases (show m = 2 ∨ m = 4 ∨ (3 ≤ m ∧ m ≠ 4) by omega) with rfl | rfl | ⟨hm3, hm4⟩
    · exact false_of_card_psl2_psp4 hp hp2 hf he h1 h2 hv
    · exact false_of_card_psl4_psp4 hp hp2 hf h1 h2 hv
    · exact false_of_card_psl_psp4 hp hp2 hf he hm3 hm4 h1 h2 hv
  · exfalso
    have hm : 3 ≤ m := hadm.2.2.1
    rcases (show m = 4 ∨ m ≠ 4 by omega) with rfl | hm4
    · exact false_of_card_psu4_psp4 hp hp2 hf h1 h2 hv
    · exact false_of_card_psu_psp4 hp hp2 hf he hm hm4 h1 h2 hv
  · have hm : 2 ≤ m := hadm.2.2.1
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · have hv' : 2 ^ 2 * e = 2 ^ 2 * f := hv
      exact ⟨rfl, rfl, by omega⟩
    · exact (false_of_card_psp_psp4 hp hp2 hf he hm3 h1 h2 hv).elim
  · exact (false_of_card_pomegaOdd_psp4 hp hp2 hf he hadm.2.2.1 h1 h2 hv).elim
  · exact (false_of_card_pomegaPlus_psp4 hp hp2 hf he hadm.2.2 h1 h2 hv).elim
  · exact (false_of_card_pomegaMinus_psp4 hp hp2 hf he hadm.2.2 h1 h2 hv).elim

theorem false_of_two_lieModels_l2 {Y : Type} [Group Y] {t : StatedLieTag} {m p e f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (ht : (t = .PSL ∧ 3 ≤ m) ∨ t = .PSU ∨ t = .PSp) (hadm : StatedLieAdmissible t m p e)
    (h : LieModel Y t m p e) (hX : LieModel Y .PSL 2 p (2 * f)) : False := by
  have he : 1 ≤ e := hadm.2.1
  rcases ht with ⟨rfl, hm⟩ | rfl | rfl
  · obtain ⟨h1, h2, hv⟩ := lieOrder_of_two_lieModels (Or.inl rfl) (Or.inl rfl) hp2 (by omega)
      (by norm_num) h hX
    exact false_of_card_psl_l2 hp hp2 hf he hm h1 h2 hv
  · have hm : 3 ≤ m := hadm.2.2.1
    obtain ⟨h1, h2, hv⟩ := lieOrder_of_two_lieModels (Or.inr (Or.inl rfl)) (Or.inl rfl) hp2
      (by omega) (by norm_num) h hX
    exact false_of_card_psu_l2 hp hp2 hf he hm h1 h2 hv
  · have hm : 2 ≤ m := hadm.2.2.1
    obtain ⟨h1, h2, hv⟩ := lieOrder_of_two_lieModels (Or.inr (Or.inr rfl)) (Or.inl rfl) hp2
      (by omega) (by norm_num) h hX
    exact false_of_card_psp_l2 hp hp2 hf he hm h1 h2 hv

end CFSG.ComponentClassification.CatLeafProof.X10Lin
