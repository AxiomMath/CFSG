module

public import CFSG.LargeExtraspecial.DWW4Rank
public import CFSG.Yardstones.M3aba7dc4b8a8.Definitions

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup CFSG.LargeExtraspecial CFSG.Yardstones.M3aba7dc4b8a8

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_bmax_of_sectional (hset : GF2RankFourSetting G z) (S : Setting G) (hSz : S.z = z)
    (hw : S.width = 4) (hS4 : CFSG.GH74.SectionalTwoRankLE S.Mbar 4) :
    ∃ B : Subgroup G, B ≤ S.M ∧ CFSG.Open.IsElemAbelian 3 B ∧ ∃ r : ℕ, 4 ≤ r ∧
      Nat.card B = 3 ^ r := by
  obtain ⟨-, -, hchar, he, -, hmax, hsym, B, hB, hBM⟩ := hset
  subst hSz
  have h4 := DW.W4Rank.four_le_rank_of_eleven_generated hchar he
    (DW.W4Rank.exists_generators_le_eleven_of_witness S hw hS4 hchar hmax hsym hB hBM)
  exact ⟨B, hBM, hB.1, _, h4, hB.2.1⟩

theorem exists_elemAbelian_three_of_sectional (hset : GF2RankFourSetting G z) (S : Setting G)
    (hSz : S.z = z) (hw : S.width = 4) (hS4 : CFSG.GH74.SectionalTwoRankLE S.Mbar 4) :
    ∃ E : Subgroup S.O, E ≤ S.Mbar ∧ CFSG.Open.IsElemAbelian 3 E ∧
      ∃ r : ℕ, 4 ≤ r ∧ Nat.card E = 3 ^ r := by
  obtain ⟨B, hBM, hEl, r, hr, hB⟩ := exists_bmax_of_sectional hset S hSz hw hS4
  let f : B →* S.O := S.ρ.comp (Subgroup.inclusion hBM)
  have hodd : Odd (Nat.card B) := by
    rw [hB]
    exact Odd.pow (by decide)
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr fun b hb => ?_
    have hq : (⟨b, hBM b.2⟩ : S.M) ∈ S.Q := S.mem_Q_of_ρ_eq_one hb
    obtain ⟨k, hk⟩ := S.extraspecial.1 ⟨_, hq⟩
    have h2 : (b : G) ^ 2 ^ k = 1 := by
      have := congrArg (fun x : S.Q => ((x : S.M) : G)) hk
      simpa using this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card B) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    have h3 := pow_gcd_eq_one.mpr ⟨(Subtype.ext h2 : b ^ 2 ^ k = 1), pow_card_eq_one' (G := B)⟩
    rwa [hcop.gcd_eq_one, pow_one] at h3
  refine ⟨f.range, ?_, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, r, hr, ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBM b.2⟩, rfl⟩
  · obtain ⟨_, b, rfl⟩ := x
    obtain ⟨_, c, rfl⟩ := y
    refine Subtype.ext ?_
    change f b * f c = f c * f b
    rw [← map_mul, ← map_mul, hEl.1.is_comm.comm b c]
  · rintro _ ⟨b, rfl⟩
    rw [← map_pow, show b ^ 3 = 1 from Subtype.ext (hEl.2 b b.2), map_one]
  · exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hB

end CFSG.GF2Type.Smith1979
