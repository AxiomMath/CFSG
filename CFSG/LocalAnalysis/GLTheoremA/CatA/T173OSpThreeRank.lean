module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperShared
public import CFSG.RankThree.PartOne.KF.ClsSpUpper
public import CFSG.RankThree.PartOne.KF.ClsSpWit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG CFSG.Open CFSG.SectionRank CFSG.RankThree.PartOne.KFU CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ}

private theorem card_le_three_pow_of_le_normalizer [CharP F 2] (hF : Nat.card F = 2)
    {R E : Subgroup ↥(StatedSp ℓ F)} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hE : E ≤ Subgroup.normalizer (R : Set ↥(StatedSp ℓ F)))
    (hEel : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ (ℓ - 1) := by
  have hdiv : ∀ i : ℕ, 0 < i → i < 2 → ¬ 3 ∣ Nat.card F ^ i - 1 := by
    intro i _ hi2
    obtain rfl : i = 1 := by omega
    rw [pow_one, hF]
    norm_num
  have hpK : (3 : F) ≠ 0 := natCast_ne_zero_of_ne_two Nat.prime_three (by norm_num)
  obtain ⟨a, ha1, ha2, hcard⟩ :=
    card_le_of_normalizes (spForm ℓ F) (natRep (StatedSp ℓ F))
      (isIsometric_natRep_statedSp (n := ℓ) (K := F)) (natRep_injective (StatedSp ℓ F))
      Nat.prime_three (by norm_num) hpK (d := 2) (by norm_num) hdiv hR hR1 hE
      (fun g hg h hh => congrArg Subtype.val (hEel.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩))
      (fun g hg => hEel.2 g hg)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin,
    show ℓ + ℓ = 2 * ℓ by omega] at ha2 hcard
  calc Nat.card E ≤ 3 ^ (a / 2) * 3 ^ ((2 * ℓ - 2 * a) / 2) := hcard
    _ = 3 ^ (a / 2 + (ℓ - a)) := by
        rw [← pow_add]
        congr 1
        omega
    _ ≤ 3 ^ (ℓ - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)

theorem twoLocalRank_three_statedSp (hF : Nat.card F = 2) (hℓ : 2 ≤ ℓ) :
    GLATwoLocalRank 3 ↥(StatedSp ℓ F) = ℓ - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num)
  refine le_antisymm ?_ ?_
  · exact CFSG.LocalAnalysis.GLTheoremA.glaTwoLocalRank_le_of_card_le Nat.prime_three
      (fun R E hR1 hR hE hEel => card_le_three_pow_of_le_normalizer hF hR hR1 hE hEel)
  · have hlow : ℓ - 1 ≤ CFSG.Assembly.RankThreeEven.localRank 3
        (StatedProj (StatedSp ℓ F)) := by
      have h := le_localRank_three_statedSp_blocks (K := F) (m := ℓ - 1) (by omega)
      rwa [show ℓ - 1 + 1 = ℓ by omega] at h
    have hlow' : ℓ - 1 ≤ CFSG.Assembly.RankThreeEven.localRank 3 ↥(StatedSp ℓ F) := by
      rwa [localRank_statedProj_eq (K := F) (n := ℓ) (by omega) (p := 3) Nat.prime_three]
        at hlow
    simpa only [CFSG.Open.GLATwoLocalRank, CFSG.Assembly.RankThreeEven.localRank] using hlow'

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
