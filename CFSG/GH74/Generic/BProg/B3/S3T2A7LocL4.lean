module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7Rows
public import CFSG.GH74.Generic.BProg.B2.Thm2Classes
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ThreeFinal
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Ext
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q2s
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutAsm
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenExt
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutDa

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7Loc

open CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.Generic CFSG.Assembly.LowTwoRank Subgroup

theorem su4ExtStmt (K : Type) [Field K] [Finite K] (p f : ℕ) :
    B2.GenLocU4Inner.Su4ExtStmt K p f :=
  fun hp hp2 hK hq {_} _ _ α hA ρ hU hρ hab a₀ c hc hsq =>
    B2.GenLocU4Ext.gammaAct_su4_ext hp hp2 hK hq α hA ρ hU hρ hab a₀ c hc hsq

theorem su4QuatStmt
    (K : Type) [Field K] [Finite K] (p f : ℕ) :
    B2.GenLocU4Inner.Su4QuatStmt K p f :=
  B2.GenLocU4Q.su4QuatStmt B2.GenLocU4Q2.su4Q2Stmt_holds B2.GenLocU4Q2s.su4Q2SplitStmt_holds

theorem su4OuterStmt
    (K : Type) [Field K] [Finite K] (p f : ℕ) :
    B2.GenLocU4Fam.Su4OuterStmt K p f :=
  fun hp hp2 hK hq {_} _ _ α hA hout hsect =>
    B2.GenLocU4OutAsm.gammaAct_su4_outer_of_classes (B2.GenLocU4Out.outSplitGen K p f)
      (B2.GenLocU4Out.outDbGen K p f) (B2.GenLocU4Out.outExtGen K p f)
      B2.GenLocU4OutDa.outDaGen_holds hp hp2 hK hq α hA hout hsect

theorem weakSig2NormG4_isSL4Model
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (h : L5U5.IsSL4Model J) : B2.WeakSig2NormG4 J :=
  B2.weakSig2NormG4_qShape1 (fun _ _ _ hF4 => B2.genLoc4_sl4_lin_all hF4) su4ExtStmt
    su4QuatStmt su4OuterStmt hq h

section Component

variable {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}

omit [Finite Y] in
theorem center_ne_bot_of_mem (hs : S3T2A7.Setting125 Y L B X₀ z) (hzL : z ∈ L) :
    center ↥L ≠ ⊥ := by
  intro hbot
  have hzc : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp hs.z_cent g)
  rw [hbot, mem_bot] at hzc
  exact hs.z_ne (congrArg Subtype.val hzc)

theorem isSL4Model_of_setting (hF : GenericKnownFacts) (hs : S3T2A7.Setting125 Y L B X₀ z)
    (hL : S3T2A7.OddL4m (↥L ⧸ center ↥L)) :
    RankCertified (↥L ⧸ center ↥L) 3 ∧ L5U5.IsSL4Model ↥L := by
  have hP2 : IsPGroup 2 ↥(center ↥L) := GLS.isPGroup_two_center_of_subnormal hs.core hs.comp.2
  obtain ⟨p, f, hp, hp2, -, ⟨h4, hm⟩ | ⟨h4, hm⟩⟩ := hL
  · obtain ⟨-, -, F, _, _, hFc, ⟨e⟩⟩ := lieModel_psl_data hm
    have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_card_eq hp hp2 hFc
    have hc3 : RankCertified (↥L ⧸ center ↥L) 3 := (rankCertified_PSL4 hF2).of_mulEquiv e.symm
    have hZ := center_ne_bot_of_mem hs (S3T2A7.mem_of_rankCertified_three hs hc3)
    have hodd : Odd (Nat.card F) := by rw [hFc]; exact (hp.odd_of_ne_two hp2).pow
    obtain ⟨π, hπ, hcompat⟩ := hF.psl4_cover ↥L hs.comp.1 hP2 F hodd e
    refine ⟨hc3, ?_⟩
    rcases cover_branch_SL4 hF2 e π hπ hcompat hZ with ⟨hmod, ⟨e'⟩⟩ | ⟨h1, -⟩
    · exact Or.inl ⟨F, inferInstance, inferInstance, hmod, ⟨e'⟩⟩
    · rw [hFc] at h1
      omega
  · obtain ⟨-, -, F, _, _, hFc, ⟨e⟩⟩ := lieModel_psu_data hm
    have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hc3 : RankCertified (↥L ⧸ center ↥L) 3 :=
      (rankCertified_PSU4 hFc (Nat.odd_iff.1 hqodd)).of_mulEquiv e.symm
    have hZ := center_ne_bot_of_mem hs (S3T2A7.mem_of_rankCertified_three hs hc3)
    obtain ⟨π, hπ, hcompat⟩ := hF.psu4_cover ↥L hs.comp.1 hP2 F (p ^ f) hFc hqodd e
    refine ⟨hc3, ?_⟩
    rcases cover_branch_SU4 hFc (Nat.odd_iff.1 hqodd) e π hπ hcompat hZ with
      ⟨hmod, ⟨e'⟩⟩ | ⟨h3, -⟩
    · exact Or.inr ⟨p ^ f, F, inferInstance, inferInstance, hFc, hmod, ⟨e'⟩⟩
    · omega

end Component

theorem cell125_oddL4m
    (hF : GenericKnownFacts) : S3T2A7.Cell125 S3T2A7.OddL4m := by
  intro Y _ _ L B X₀ z hs hL hsig _
  obtain ⟨hc3, hSL⟩ := isSL4Model_of_setting hF hs hL
  exact S3T2A7.false_of_weakSig2NormG4 hs hsig
    (fun b _ => S3T2A7.normal_of_rankCertified hs.sec4 hs.comp (hc3.mono (by norm_num)) b)
    (weakSig2NormG4_isSL4Model hs.comp.1 hSL)

end CFSG.GH74.Generic.BProg.B3.S3T2A7Loc
