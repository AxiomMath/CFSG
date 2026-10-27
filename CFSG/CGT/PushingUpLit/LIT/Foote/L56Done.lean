module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Case
public import CFSG.CGT.PushingUpLit.LIT.Foote.L56PartD
public import CFSG.CGT.PushingUpLit.LIT.Foote.TheoremA

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (Theorem3Statement Frame SylowFrame)

theorem lemma_5_6_holds (h3 : Theorem3Statement) : Lemma56 := by
  intro G _ _ M J z₀ c hz hTwo hFour
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : FooteTheoremA := footeTheoremA
  have hJ := c.block
  obtain ⟨g, hgood, hmax⟩ := exists_max56 hFour.exists_good
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (eSub J g)
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hT.le.trans inf_le_right
  have hfr : Frame J T :=
    { le_normalizer := hTN
      inf_eq_bot := c.inf_eq_bot_of_le hgood.1 (hT.le.trans inf_le_left) hT.isPGroup
      isPGroup := hT.isPGroup }
  obtain ⟨S, hS⟩ := hfr.exists_sylowFrame
  have hB := c.not_centralizes_blockU hA hz hgood hT hmax
  obtain ⟨x₁, hx₁J, hx₁M, hx₁B⟩ := c.exists_swap h3 hA hz hgood hT hmax hS hB
  obtain ⟨x, hxJ, hxM, hxB, hxW⟩ := c.exists_swap_le hA hz hgood hT hS hx₁J hx₁M hx₁B
  obtain ⟨hTc, hTs, hQV, hQT⟩ := c.partC hA hz hgood hT hmax hS hB
  have hVS : blockU J ≤ S := blockU_le_of_sylowFrame hJ hS
  obtain ⟨y₀, hy₀J, hy₀S, hy₀ne⟩ := c.exists_not_weakly_closed hS hB hQV
  obtain ⟨y, hyJ, hyN, hyne⟩ := exists_y_le_normalizer hS ⟨y₀, hy₀J, hy₀S, hy₀ne⟩
  have hnT := not_conj_le_of_ne hS (blockU_le J)
    (fun y hy v hv => conj_mem_blockU (Subgroup.le_normalizer hy) hv) hVS hJ.blockU_comm hQV hyJ
    hyne
  exact c.false_of_swap hA hz hTwo hgood hT hmax hS hB hxJ hxM hxB hxW hyJ hyN hnT

end CFSG.CGT.PushingUpLit.LIT.Foote
