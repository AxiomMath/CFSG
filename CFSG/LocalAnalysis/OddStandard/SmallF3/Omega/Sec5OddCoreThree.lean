module

public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LieType.Multipliers.U43
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem isPGroup_three_oddCoreIn
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsOm6Z2 L) : IsPGroup 3 (oddCoreIn L) := by
  classical
  obtain ⟨hq, hZcard, hmodel⟩ := hL
  haveI hperf : Group.IsPerfect ↥L := hq.1
  let O : Subgroup ↥L := CFSG.oddCore ↥L
  let Z : Subgroup ↥L := Subgroup.center ↥L
  have hne : O ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (↥L ⧸ O) := (QuotientGroup.subsingleton_iff).mpr htop
    have h1 : Nat.card (Subgroup.center (↥L ⧸ O)) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    have h2 : Nat.card (Subgroup.center (↥L ⧸ O)) = 2 := by
      simpa only [O] using hZcard
    omega
  have hOpen : CFSG.Open.IsQuasisimple ↥L := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hOZ : O ≤ Z :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hOpen O hne
  let π : ↥L →* ↥L ⧸ O := QuotientGroup.mk' O
  have hcenter : Z.map π = Subgroup.center (↥L ⧸ O) := by
    refine CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel π
      (QuotientGroup.mk'_surjective O) ?_
    rw [show π.ker = O from QuotientGroup.ker_mk' O]
    exact hOZ
  let e : ↥L ⧸ Z ≃* (↥L ⧸ O) ⧸ Subgroup.center (↥L ⧸ O) :=
    (QuotientGroup.quotientQuotientEquivQuotient (N := O) (M := Z) hOZ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hcenter)
  have hmodelL : CFSG.Blueprint.LieModel (↥L ⧸ Z) .PSU 4 3 1 :=
    hmodel.of_mulEquiv e.symm
  obtain ⟨hperfS, ⟨eM⟩⟩ :=
    CFSG.LieType.Multipliers.U43.multiplier_PSU_four_three (↥L ⧸ Z) hmodelL
  haveI : Group.IsPerfect (↥L ⧸ Z) := ⟨hperfS⟩
  have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier (↥L ⧸ Z)) = 36 := by
    rw [Nat.card_congr eM.toEquiv]
    simp [Nat.card_prod, Nat.card_zmod]
  have hcardHopf :
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (↥L ⧸ Z)) = 36 := by
    rw [← Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (↥L ⧸ Z)).toEquiv]
    exact hcardM
  let p : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z
  obtain ⟨⟨-, -⟩, h, -, -, -, hmap, ⟨eK⟩⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier
      (S := ↥L ⧸ Z) (E := ↥L) (p := p)
      (QuotientGroup.mk'_surjective Z) (by
        rw [show p.ker = Z from QuotientGroup.ker_mk' Z])
  have hZ_dvd_hopf : Nat.card Z ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (↥L ⧸ Z)) := by
    calc
      Nat.card Z = Nat.card p.ker := by
        rw [show p.ker = Z from QuotientGroup.ker_mk' Z]
      _ = Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (↥L ⧸ Z) ⧸
            (h.comp (CFSG.RankThree.PerfectCover.hopfMultiplier (↥L ⧸ Z)).subtype).ker) :=
          (Nat.card_congr eK.toEquiv).symm
      _ ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (↥L ⧸ Z)) :=
          Subgroup.card_quotient_dvd_card _
  have hZ_dvd36 : Nat.card Z ∣ 36 := by
    simpa only [hcardHopf] using hZ_dvd_hopf
  have hOddO : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card ↥L
  have hO_dvd36 : Nat.card O ∣ 36 := (Subgroup.card_dvd_of_le hOZ).trans hZ_dvd36
  have hO_dvd9 : Nat.card O ∣ 9 := by
    have hcop : Nat.Coprime (Nat.card O) 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.coprime_pow_right_iff (by norm_num) _ 2).mpr hOddO.coprime_two_right
    have h36 : Nat.card O ∣ 4 * 9 := by simpa using hO_dvd36
    exact hcop.dvd_of_dvd_mul_left h36
  have hcardOin : Nat.card ↥(oddCoreIn L) = Nat.card O := by
    change Nat.card ↥(O.map L.subtype) = Nat.card O
    rw [Subgroup.card_map_of_injective L.subtype_injective]
  exact IsPGroup.of_card_dvd_pow (p := 3) (n := 2) (by
    rw [hcardOin]
    simpa using hO_dvd9)

end CFSG.OddStandard.SmallF3.Omega
