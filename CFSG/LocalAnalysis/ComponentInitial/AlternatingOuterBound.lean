module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms

theorem outer_isomorphism {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    (∃ e : Outer G ≃* Outer H,
      ∀ α : MulAut G, e (α : Outer G) = (((f.symm.trans α).trans f : MulAut H) : Outer H)) ∧
      (Group.IsSolvable (Outer G) ↔ Group.IsSolvable (Outer H)) := by
  refine ⟨⟨OuterAutomorphisms.equivalence f, fun α => ?_⟩, ⟨fun _ => ?_, fun _ => ?_⟩⟩
  · rfl
  · exact Group.isSolvable_of_surjective (OuterAutomorphisms.equivalence f).surjective
  · exact Group.isSolvable_of_surjective (OuterAutomorphisms.equivalence f).symm.surjective

theorem pow_le_ordProj_two {n k : ℕ} (hn : n ≠ 0) (h : 2 ^ k ∣ n) : 2 ^ k ≤ ordProj[2] n :=
  Nat.pow_le_pow_right two_pos ((Nat.prime_two.pow_dvd_iff_le_factorization hn).1 h)

theorem ordProj_two_le {n b : ℕ} (hnb : n ≤ b) (hb : 1 ≤ b) : ordProj[2] n ≤ b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hb
  · exact (Nat.ordProj_le 2 hn.ne').trans hnb

theorem alternating_simple_outer_two_part_bound {T : Type*} [Group T] {m : ℕ} (hm : 5 ≤ m)
    (e : T ≃* alternatingGroup (Fin m)) :
    ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T) ∧ 4 ≤ ordProj[2] (Nat.card T) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hcardT : Nat.card T = m.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
  have h24 : 24 ∣ m.factorial := by
    have h := Nat.factorial_dvd_factorial (show 4 ≤ m by omega)
    rwa [show (4 : ℕ).factorial = 24 from rfl] at h
  have hpos : 0 < m.factorial / 2 := Nat.div_pos (by
    have := Nat.le_of_dvd (Nat.factorial_pos m) h24; omega) two_pos
  have hT4 : 4 ≤ ordProj[2] (Nat.card T) := by
    rw [hcardT]
    refine pow_le_ordProj_two (k := 2) hpos.ne' ?_
    obtain ⟨c, hc⟩ := h24
    exact ⟨3 * c, by rw [hc]; omega⟩
  refine ⟨?_, hT4⟩
  rcases (show m = 6 ∨ (m = 5 ∨ 7 ≤ m) by omega) with rfl | hm'
  · have hout := CatalogueSchreierAlternating.DegreeSix.outer_card_le_four_of_equiv e
    have hT8 : 8 ≤ ordProj[2] (Nat.card T) := by
      rw [hcardT]
      exact pow_le_ordProj_two (k := 3) (by decide) (by decide)
    exact lt_of_le_of_lt (ordProj_two_le hout (by norm_num)) (by omega)
  · have hout := CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six hm' e
    exact lt_of_le_of_lt (ordProj_two_le (Nat.le_of_dvd two_pos hout) (by norm_num)) (by omega)

end CFSG.LocalAnalysis.ComponentInitial
