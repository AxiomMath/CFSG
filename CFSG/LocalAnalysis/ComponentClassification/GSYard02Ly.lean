module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverGH
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup
open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier

theorem leafLy_of_coverAlt
    (hA : CoverLeafAlt) : LeafSporadic .Ly := by
  intro X _ _ _ hgen hsp
  obtain ⟨e⟩ := hsp
  have eJ : X ≃* ↥J := e.trans lyEquivJ
  haveI : Finite ↥J := Finite.of_equiv X eJ.toEquiv
  have hJgen : GH74.Gen4 ↥J := GH74.Gen4.of_mulEquiv eJ hgen
  have hz : Nat.card (Subgroup.center lyC) = 2 := card_center_lyC
  have hzne : Subgroup.center lyC ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hz
    omega
  have hzp : IsPGroup 2 (Subgroup.center lyC) :=
    IsPGroup.of_card (n := 1) (hz.trans (by norm_num))
  have hzc : IsCyclic (Subgroup.center lyC) := isCyclic_of_prime_card hz
  have hr : 3 ≤ CFSG.pRank 2 lyC := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank 2 lyC]
    obtain ⟨hEA, hcardE⟩ := (ea16_iff lyE1).2 (Or.inl rfl)
    have hEJ : CFSG.IsElementaryAbelian 2 ↥(lyE1.map lyS.subtype) :=
      CFSG.IsElementaryAbelian.map_subtype
    have hcard4 : Nat.card ↥(lyE1.map lyS.subtype) = 2 ^ 4 := by
      rw [Subgroup.card_map_of_injective lyS.subtype_injective, hcardE] <;> norm_num
    have hle : lyE1.map lyS.subtype ≤ lyC := by
      rintro _ ⟨x, -, rfl⟩
      exact lyS_le_lyC x.2
    have h4 := CFSG.SectionRank.le_pRank (by norm_num : (1 : ℕ) < 2) hle
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).1 hEJ) hcard4
    omega
  have hgenC : GH74.Gen4 ↥lyC := GH74.Gen4.subgroup lyC hJgen
  have hCover : CoverHyp lyC := ⟨isQuasisimple_lyC, hzne, hzp, hzc, hr, hgenC⟩
  have hC : SylowFourJoined ↥lyC :=
    hA lyC hCover 11 (by norm_num) (by norm_num) ⟨lyCenterEquiv⟩
  have hfac : (Nat.card ↥lyC).factorization 2 = 8 := by
    rw [CFSG.Sporadic.Recognition.LyonsSims.card_lyC,
      show (39916800 : ℕ) = 2 ^ 8 * 155925 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hcardP : Nat.card ↥(lyS.subgroupOf lyC) = 2 ^ (Nat.card ↥lyC).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe lyS_le_lyC).toEquiv, card_lyS, hfac] <;>
      norm_num
  have hPS : (Sylow.ofCard (lyS.subgroupOf lyC) hcardP : Subgroup ↥lyC).map lyC.subtype =
      (lySylow : Subgroup ↥J) := by
    rw [lySylow_coe]
    show (lyS.subgroupOf lyC).map lyC.subtype = lyS
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left lyS_le_lyC]
  have hSJ : SylowFourJoined ↥J :=
    sylowFourJoined_of_le lyC (Sylow.ofCard (lyS.subgroupOf lyC) hcardP) lySylow hPS hC
  exact @SylowFourJoined.of_mulEquiv ↥J (Subgroup.toGroup J) X _ _ eJ.symm hSJ

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
