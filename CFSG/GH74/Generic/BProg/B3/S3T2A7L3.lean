module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7WS
public import CFSG.GH74.Generic.BProg.B2.L3Cover
public import CFSG.GH74.Generic.BProg.B2.FamilyL3
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Five
public import CFSG.GH74.Generic.BProg.B2.GenLocU3Final
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Three
public import CFSG.GH74.Generic.S3.NbrBase

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def U33 (T : Type) [Group T] : Prop :=
  LieModel T .PSU 3 3 1


theorem weakSig_qShape3 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → QShape3 J →
    B2.WeakSig2NormG4 J :=
  fun _ _ _ hq h => B2.weakSig2NormG4_qShape3 (fun _ _ _ _ h5 hJ => B2.genLoc_psl3_five h5 hJ)
    (fun _ _ _ _ _ hq hJ => by
      rcases hq with h5 | h7 | h9
      · exact B2.GenLocU3Small.genProp_psu3_five_nine (Or.inl h5) hJ
      · exact B2.genProp_psu3_seven h7 hJ
      · exact B2.GenLocU3Small.genProp_psu3_five_nine (Or.inr h9) hJ) hq h

theorem cell125_oddL3 (hU : Cell125 U33) : Cell125 OddL3 := by
  intro Y _ _ L B X₀ z hs hP hsig hcut
  obtain ⟨p, f, hp, hp2, hf, hrow⟩ := hP
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · exfalso
      exact hp2 (by omega)
    · exact h
  have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hoddc : ∀ ζ : ↥L, ζ ≠ 1 → (∀ g : ↥L, g * ζ = ζ * g) → Odd (orderOf ζ) → False :=
    fun ζ hζ1 hζc hζo => hζ1 (Subtype.ext (B2.FamilyOddCentre.odd_central_eq_one hs.core hs.comp
      ζ.2 (fun g hg => congrArg Subtype.val (hζc ⟨g, hg⟩)) (by rwa [Subgroup.orderOf_coe])))
  have hcert : RankCertified (↥L ⧸ center ↥L) 1 := by
    rcases hrow with hL | hU'
    · exact S3.rankCertified_one_of_model (Or.inl rfl) hp2 hL
    · exact S3.rankCertified_one_of_model (Or.inr rfl) hp2 hU'
  rcases Nat.lt_or_ge 3 (p ^ f) with hgt | hle
  · have hQ : QShape3 (↥L ⧸ center ↥L) := ⟨p, f, hp, hp2, hgt, hrow⟩
    rcases B2.l3_cover_cases hs.comp.1 hQ with ⟨ζ, hζ1, hζc, hζo⟩ | ⟨hZ, -⟩
    · exact hoddc ζ hζ1 hζc hζo
    · exact false_of_weakSig2NormG4 hs hsig (fun b _ => normal_of_rankCertified_one hs hZ hcert b)
        (B2.weakSig2NormG4_of_qShape3Cover weakSig_qShape3 hs.comp.1 hQ)
  · have hp3' : p = 3 := by omega
    subst hp3'
    have hf1 : f = 1 := by
      have h3 : 3 ^ f = 3 ^ 1 := by omega
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
    subst hf1
    rcases hrow with hL | hU'
    · obtain ⟨hZ, -⟩ := B2.l3_three_cover_center hs.comp.1 hL
      exact false_of_weakSig2NormG4 hs hsig (fun b _ => normal_of_rankCertified_one hs hZ hcert b)
        (B2.weakSig2NormG4_of_l3Three (fun _ _ _ hJ => B2.genLoc4_l3_three hJ) hs.comp.1 hL)
    · exact hU Y L B X₀ z hs hU' hsig hcut

end CFSG.GH74.Generic.BProg.B3.S3T2A7
