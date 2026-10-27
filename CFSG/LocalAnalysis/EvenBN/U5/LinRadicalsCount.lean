module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinCase

theorem linrc_not_top_le {Q : Type*} [Group Q] [Finite Q] {q : ℕ} (hq : 2 ≤ q)
    {W : Subgroup Q} (hW : Nat.card W = q ^ 2) (hQ : Nat.card Q = q ^ 3)
    (htop : (⊤ : Subgroup Q) ≤ W) : False := by
  have h := Subgroup.card_le_of_le htop
  rw [Subgroup.card_top, hQ, hW] at h
  nlinarith [Nat.zero_le (q ^ 2), hq]

theorem radicals_card_of_product {Q : Type*} [Group Q] [Finite Q] {q : ℕ} (hq : 2 ≤ q)
    {Q₁ Q₂ : Subgroup Q}
    (hR : CFSG.LocalAnalysis.EvenBN.LinearThree.Radicals (⊤ : Subgroup Q) Q₁ Q₂ q)
    {B B' Z : Subgroup Q} (hB : CFSG.Open.IsElemAbelian 2 B)
    (hB' : CFSG.Open.IsElemAbelian 2 B') (hBn : B.Normal) (hB'n : B'.Normal)
    (hsup : B ⊔ B' = ⊤) (hcard : Nat.card B = Nat.card B') (hZ : Z ≤ B ⊓ B')
    (hZc : Nat.card Z = q) : Nat.card B = q ^ 2 := by
  have hQ : Nat.card Q = q ^ 3 := (Subgroup.card_top (G := Q)).symm.trans hR.card
  have hBcase : B ≤ Q₁ ∨ B ≤ Q₂ := hR.le_of_elem B le_top hB
  have hB'case : B' ≤ Q₁ ∨ B' ≤ Q₂ := hR.le_of_elem B' le_top hB'
  have hsame : ∀ W : Subgroup Q, Nat.card W = q ^ 2 → ¬ (B ≤ W ∧ B' ≤ W) := by
    rintro W hW ⟨h1, h2⟩
    exact linrc_not_top_le hq hW hQ (by rw [← hsup]; exact sup_le h1 h2)
  have hinf_le : B ⊓ B' ≤ Q₁ ⊓ Q₂ := by
    rcases hBcase with h1 | h1 <;> rcases hB'case with h2 | h2
    · exact (hsame Q₁ hR.card₁ ⟨h1, h2⟩).elim
    · exact le_inf (inf_le_left.trans h1) (inf_le_right.trans h2)
    · exact le_inf (inf_le_right.trans h2) (inf_le_left.trans h1)
    · exact (hsame Q₂ hR.card₂ ⟨h1, h2⟩).elim
  have hC : Nat.card (Q₁ ⊓ Q₂ : Subgroup Q) = q := by
    rw [hR.inf_eq]
    exact hR.card_center
  have hinf : Nat.card (B ⊓ B' : Subgroup Q) = q := by
    have h1 := Subgroup.card_le_of_le hZ
    have h2 := Subgroup.card_le_of_le hinf_le
    omega
  have hnorm : B' ≤ Subgroup.normalizer (B : Set Q) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hBn]
    exact le_top
  have hprod := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq hnorm
  rw [hsup, hR.card, hinf, ← hcard] at hprod
  have key : Nat.card B * Nat.card B = q ^ 2 * q ^ 2 := by
    rw [← hprod]
    ring
  exact (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).1 key

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
