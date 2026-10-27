module

public import CFSG.GF2Type.Smith1980Orth.S3ThmA
public import CFSG.GF2Type.Smith1980Orth.S2W4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

theorem false_of_badData_four {k : G} (H : D.BadData k) (hw : S.width = 4) : False := by
  have hxM := H.bad.mem_M
  have hxQ := H.bad.not_mem_QG
  have hPP := D.orthogonal_commSpace_eq (rho_conj_mul_self S hxM) H.half
  have hm : finrank (ZMod 2) (commSpace (D.resC ⟨_, H.hxC⟩)) = 2 := by
    have := H.half
    omega
  have hL := D.card_le_of_fix hPP H.lfix
  rw [hm] at hL
  have h4 : Nat.card (S.Lbar k) ≤ 4 := by
    have e : 2 ^ (Nat.choose 2 2 + min 2 1) = 4 := by decide
    rwa [e] at hL
  have hmul := S.card_Lbar_mul k
  rcases H.dl with h | ⟨hxz, p, -, -, hΔ⟩
  · have hL0 := SMK.card_L0_ge S hxM hxQ
    rw [hw] at hL0
    rw [h, Subgroup.card_bot, mul_one] at hmul
    have : (2 : ℕ) ^ 4 = 16 := by norm_num
    omega
  · have hL0 := SMK.card_L0_ge_succ S hxM hxQ hxz
    rw [hw] at hL0
    have hΔ4 := D.card_Dl_le_four_of_R1 hxQ hΔ
    have : Nat.card (S.L0 k) ≤ 16 := by
      rw [← hmul]
      calc Nat.card (S.Lbar k) * Nat.card (S.QG ⊓ S.Qa k : Subgroup G) ≤ 4 * 4 :=
            Nat.mul_le_mul h4 hΔ4
        _ = 16 := by norm_num
    have : (2 : ℕ) ^ (4 + 1) = 32 := by norm_num
    omega

end S2Data

theorem OrthData.not_bad_of_width_eq_four [IsSimpleGroup G] (I : TimInputs)
    (hAS4 : S14.AschbacherSmithW4Input) (hThmA : DW.W4Rank.TheoremAWidthFour)
    (hres : W4.PGL25W4Free) (O : OrthData S) (hw : S.width = 4) (k : G) : ¬ Bad S k := by
  intro hbad
  obtain ⟨D⟩ := exists_s2Data_of_width_eq_four I hAS4 hThmA hres O hw
  obtain ⟨D'⟩ := exists_s2Data_of_width_eq_four I hAS4 hThmA hres (O.conjBy k)
    (by rw [Setting.width_conjBy]; exact hw)
  exact D.false_of_badData_four (D.half_of_bad D' hbad) hw

theorem OrthData.oe34a_of_width_eq_four [IsSimpleGroup G] (I : TimInputs)
    (hAS4 : S14.AschbacherSmithW4Input) (hThmA : DW.W4Rank.TheoremAWidthFour)
    (hres : W4.PGL25W4Free) (O : OrthData S) (hw : S.width = 4) : OE34a S := by
  obtain ⟨D⟩ := exists_s2Data_of_width_eq_four I hAS4 hThmA hres O hw
  exact D.oe34a_of_forall_not_bad (O.not_bad_of_width_eq_four I hAS4 hThmA hres hw)

theorem OrthData.oDelta_of_width_eq_four [IsSimpleGroup G] (I : TimInputs)
    (hAS4 : S14.AschbacherSmithW4Input) (hThmA : DW.W4Rank.TheoremAWidthFour)
    (hres : W4.PGL25W4Free) (O : OrthData S) (hw : S.width = 4) : ODelta S := by
  intro k hxM hxQ hbot
  obtain ⟨a, ha, haΔ⟩ :=
    exists_of_not_bad (O.not_bad_of_width_eq_four I hAS4 hThmA hres hw k) hxM hxQ
  rw [hbot, Subgroup.mem_bot] at haΔ
  subst haΔ
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  apply S.z_ne_one
  calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
    _ = 1 := by rw [hg]; group

end CFSG.GF2Type.Smith1980Orth
