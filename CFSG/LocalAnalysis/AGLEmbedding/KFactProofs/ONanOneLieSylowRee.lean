module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel

public section

namespace CFSG.AGLEmbedding.KFactProofs.OneLieSylow

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem factorization_three_ree (a : ℕ) :
    ((3 ^ (2 * a + 1)) ^ 3 * (3 ^ (2 * a + 1) - 1) * ((3 ^ (2 * a + 1)) ^ 3 + 1)).factorization 3 =
      3 * (2 * a + 1) := by
  set q : ℕ := 3 ^ (2 * a + 1) with hq
  have hq3 : 3 ∣ q := dvd_pow_self 3 (by omega)
  have hq1 : 3 ≤ q := Nat.le_self_pow (by omega) 3
  have h1 : ¬ 3 ∣ q - 1 := by omega
  have h2 : ¬ 3 ∣ q ^ 3 + 1 := by
    have : 3 ∣ q ^ 3 := dvd_pow hq3 (by norm_num)
    omega
  have hq0 : q ≠ 0 := by omega
  rw [Nat.factorization_mul (mul_ne_zero (pow_ne_zero 3 hq0) (by omega)) (by positivity),
    Nat.factorization_mul (pow_ne_zero 3 hq0) (by omega), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h1, Nat.factorization_eq_zero_of_not_dvd h2, add_zero,
    add_zero, Nat.factorization_pow, Finsupp.smul_apply, hq,
    Nat.Prime.factorization_pow Nat.prime_three]
  simp

theorem card_sylow_ree {L : Type} [Group L] [Finite L]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex 3 d) (h : Nonempty (L ≃* CatGroup d))
    (U : Sylow 3 L) :
    Nat.card (U : Subgroup L) = (3 ^ d.1.fieldExponent) ^ 3 ∧
      Nat.card (Sylow 3 L) = (3 ^ d.1.fieldExponent) ^ 3 + 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  obtain ⟨hn, hηξ, hfaith, htrans, -, -, hreg, hcardΩ, -, hcardΓ, hP, hstab, hUn, hNU, hNUV⟩ :=
    small_Ree_Borel_coset_Sylow_action a (GaloisField 3 (2 * a + 1)) hK w₀ hw₀
  obtain ⟨P, hPU⟩ := hP
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq e U P
  have hU : (U : Subgroup L).map e'.toMonoidHom =
      (ReeTag.G2.reeFixedPosUnipotent (GaloisField 3 (2 * a + 1)) a).subgroupOf
        (ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a) := he'.trans hPU
  rw [hfe]
  refine ⟨?_, ?_⟩
  · rw [card_eq_of_map_eq e' he', P.card_eq_multiplicity, hcardΓ,
      factorization_three_ree a, ← pow_mul, mul_comm]
  · rw [card_sylow_eq_index e' U hU, hNU]
    exact hcardΩ

end CFSG.AGLEmbedding.KFactProofs.OneLieSylow
