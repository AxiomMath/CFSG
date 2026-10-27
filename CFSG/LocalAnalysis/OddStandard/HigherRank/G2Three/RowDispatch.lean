module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.RowCores
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.ComponentClassification.HarrisLit CFSG.ComponentClassification.HarrisLit.T1

theorem Case3RowCores.lieChar_three (hRows : Case3RowCores)
    (hM11 : Nat.card ↥CFSG.Blueprint.NativeSporadic.M11 = 7920)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hcat : CFSG.Blueprint.Catalog S) {t : S} (ht : orderOf t = 2) {J : Subgroup S}
    (hJC : J ≤ centralizer ({t} : Set S))
    (hJs : (J.subgroupOf (centralizer ({t} : Set S))).IsSubnormal) (htJ : t ∈ J)
    (hJq : IsTwoQuasisimple ↥J) {L : Type} [Group L] [Finite L] (hM : IsMTypeSchur 3 L)
    (hI : InductionTypeField 3 L)
    (e : Nonempty (L ⧸ CFSG.Open.fusionZStar L ≃* ↥J ⧸ CFSG.Open.fusionZStar ↥J))
    (hJU : CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSU 4 3 1) : LieChar 3 S := by
  by_cases h3 : LieChar 3 S
  · exact h3
  · exfalso
    obtain ⟨hAlt, hLieRow, hSpor⟩ := hRows
    rcases hcat with ⟨q, -, ⟨eC⟩⟩ | ⟨n, hn, ⟨eA⟩⟩ | ⟨τ, n, r, f, hm⟩ | hex | hsp
    ·
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      apply eC.injective
      rw [map_mul, map_mul, mul_comm]
    ·
      exact hAlt S hna 3 Nat.prime_three (by norm_num) ⟨⟨n, hn, ⟨eA⟩⟩, h3⟩
        t ht J hJC hJs htJ hJq L hM hI e
    ·
      have hLie : LieChar r S :=
        ⟨τ, n, f, .inl ⟨by
          rcases CFSG.Milestones.statedClassicalModel_tag_mem S τ n r f hm with
            h | h | h | h | h | h <;> subst h <;> decide, hm⟩⟩
      exact hLieRow S hna 3 Nat.prime_three (by norm_num)
        ⟨⟨r, fun h => h3 (h ▸ hLie), hLie⟩, h3⟩ t ht J hJC hJs htJ hJq L hM hI e
    ·
      have hLie : ∃ r : ℕ, LieChar r S := by
        rcases hex with ⟨τ, r, f, hτ, hm⟩ | ⟨τ, r, f, hτ, hm⟩ | ⟨r, f, hm⟩
        · exact ⟨r, τ, 0, f, .inr (.inl ⟨rfl, hτ, hm⟩)⟩
        · exact ⟨r, τ, 0, f, .inr (.inr (.inl ⟨rfl, hτ, hm⟩))⟩
        · exact ⟨r, .twistedB2, 0, f, .inr (.inr (.inr ⟨rfl, rfl, hm⟩))⟩
      obtain ⟨r, hLie⟩ := hLie
      exact hLieRow S hna 3 Nat.prime_three (by norm_num)
        ⟨⟨r, fun h => h3 (h ▸ hLie), hLie⟩, h3⟩ t ht J hJC hJs htJ hJq L hM hI e
    ·
      by_cases hm11 : Nonempty (S ≃* ↥CFSG.Blueprint.NativeSporadic.M11)
      · obtain ⟨e1⟩ := hm11
        have hS_card : Nat.card S = 7920 := by
          rw [Nat.card_congr e1.toEquiv, hM11]
        have hJq_card : Nat.card (↥J ⧸ center ↥J) = 3265920 :=
          CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_three
            (hJU.statedClassicalModel (by decide))
        haveI : Nonempty ↥J := ⟨⟨t, htJ⟩⟩
        have hle1 : Nat.card (↥J ⧸ center ↥J) ≤ Nat.card ↥J :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (center ↥J))
        have hle2 : Nat.card ↥J ≤ Nat.card S := Subgroup.card_le_card_group (H := J)
        omega
      · exact hSpor S hna 3 Nat.prime_three (by norm_num) ⟨hsp, hm11⟩
          t ht J hJC hJs htJ hJq L hM hI e

end CFSG.OddStandard.HigherRank.G2Three
