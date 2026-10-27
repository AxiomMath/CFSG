module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTransfer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ComponentClassification.RankTwoBender

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ABGLocalTools

variable {H Q : Type*} [Group H] [Group Q] [Finite H] (f : H →* Q)

omit [Finite H] in
theorem isElemAbelian_map {T : Subgroup H} (hT : IsElemAbelian 2 T) : IsElemAbelian 2 (T.map f) :=
  CFSG.SectionRank.isElemAbelian_map hT _

theorem isSylowOf_map_of_odd_ker [Finite Q] (hk : Odd (Nat.card f.ker)) {T X : Subgroup H}
    (hTX : IsSylowOf 2 T X) : IsSylowOf 2 (T.map f) (X.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Asc76X.isSylowOf_iff_card] at hTX ⊢
  obtain ⟨hle, hcard⟩ := hTX
  refine ⟨map_mono hle, ?_⟩
  have hTp : IsPGroup 2 T := IsPGroup.of_card hcard
  rw [card_map_of_isPGroup f hk hTp, hcard]
  congr 1
  have h := Asc76X.card_map_mul_card_inf_ker f X
  have hodd : Odd (Nat.card (f.ker ⊓ X : Subgroup H)) := hk.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hne : Nat.card (f.ker ⊓ X : Subgroup H) ≠ 0 := Nat.card_pos.ne'
  have hne' : Nat.card (X.map f) ≠ 0 := Nat.card_pos.ne'
  rw [← h, Nat.factorization_mul hne' hne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr h2)), add_zero]

end CFSG.ComponentClassification.RankTwoBender
