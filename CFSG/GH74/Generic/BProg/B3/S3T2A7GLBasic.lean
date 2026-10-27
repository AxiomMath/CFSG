module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7WS

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem cell125_of_imp {P R : ∀ (T : Type) [Group T], Prop}
    (h : ∀ (T : Type) [Group T], R T → P T) (hP : Cell125 P) : Cell125 R :=
  fun Y _ _ L B X₀ z hs hR hsig hcut => hP Y L B X₀ z hs (h _ hR) hsig hcut

namespace GLR

variable {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}

omit [Finite Y] in
theorem center_ne_bot_of_mem (hs : Setting125 Y L B X₀ z) (hzL : z ∈ L) :
    center ↥L ≠ ⊥ := by
  intro hbot
  have hzc : (⟨z, hzL⟩ : ↥L) ∈ center ↥L :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp hs.z_cent g)
  rw [hbot, mem_bot] at hzc
  exact hs.z_ne (congrArg Subtype.val hzc)

theorem isPGroup_center (hs : Setting125 Y L B X₀ z) : IsPGroup 2 ↥(center ↥L) :=
  GLS.isPGroup_two_center_of_subnormal hs.core hs.comp.2

theorem false_of_noTwoCover (hs : Setting125 Y L B X₀ z) (hc : RankCertified (↥L ⧸ center ↥L) 3)
    (hn : NoTwoCover (↥L ⧸ center ↥L)) : False :=
  center_ne_bot_of_mem hs (mem_of_rankCertified_three hs hc)
    (hn ↥L hs.comp.1 (isPGroup_center hs) ⟨MulEquiv.refl _⟩)

omit [Finite Y] in
theorem false_of_rankCertified_four (hs : Setting125 Y L B X₀ z) (hc : RankCertified ↥L 4) :
    False :=
  (hc.of_injective L.subtype L.subtype_injective).not_sectionalTwoRankLE hs.sec4

end GLR

end CFSG.GH74.Generic.BProg.B3.S3T2A7
