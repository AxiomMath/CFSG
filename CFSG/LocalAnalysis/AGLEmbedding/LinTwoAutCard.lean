module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.AGLEmbedding

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem card_mulAut_psl2GF (p n : ℕ) [Fact p.Prime] (hn : 1 ≤ n) :
    Nat.card (MulAut (PSL2GF p n)) = p ^ n * ((p ^ n) ^ 2 - 1) * n := by
  have hq := GaloisField.card p n (by omega)
  rw [← Nat.card_congr (semilinearEquivAut (GaloisField p n)).toEquiv, SemidirectProduct.card,
    pgl2_card_formula, hq,
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Fact.out _ hq).1]

theorem kFactL2AutPCard : KFactL2AutPCard := by
  intro p n _ _ hn A hA
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hcop : Nat.Coprime (p ^ k) ((p ^ n) ^ 2 - 1) := by
    have h : Nat.Coprime ((p ^ n) ^ 2) ((p ^ n) ^ 2 - 1) :=
      (Nat.coprime_self_sub_right (Nat.one_le_pow _ _ (pow_pos hp.pos n))).mpr
        (Nat.coprime_one_right _)
    exact (h.coprime_dvd_left (dvd_pow (dvd_pow_self p (by omega)) two_ne_zero)).pow_left k
  have hdvd : p ^ k ∣ ((p ^ n) ^ 2 - 1) * (p ^ n * n) := by
    rw [← hk, show ((p ^ n) ^ 2 - 1) * (p ^ n * n) = p ^ n * ((p ^ n) ^ 2 - 1) * n by ring,
      ← card_mulAut_psl2GF p n hn]
    exact Subgroup.card_subgroup_dvd_card A
  rw [hk]
  exact hcop.dvd_of_dvd_mul_left hdvd

end CFSG.AGLEmbedding
