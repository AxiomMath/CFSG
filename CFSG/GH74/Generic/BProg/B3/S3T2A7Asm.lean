module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7Defs
public import CFSG.GH74.Generic.BProg.B3.ObsPump
public import CFSG.GH74.Generic.BProg.B3.LocBalRee

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance Subgroup

theorem cell125_of_locBal1For {P : ∀ (T : Type) [Group T], Prop} (h : LocBal1For P) :
    Cell125 P := by
  intro Y _ _ L B X₀ z hs hP _ hcut
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hfB, hfL, hfc, n, hn, hnL, hnc⟩ := hcut
  obtain ⟨-, hsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hs.B_el
  have hf2 : f * f = 1 := hsq f hfB
  set M : Subgroup Y := normalizer (L : Set Y) with hM
  have hInn := CFSG.LocalAnalysis.ComponentInitial.inner_le_range_centerQuotient_comp L
  let φ : M →* (rhoL L).range := (rhoL L).rangeRestrict
  have hcore : φ ⟨n, hnL⟩ ∈ CFSG.Assembly.Dichotomy.involutionOddCore (φ ⟨f, hfL⟩) := by
    have h1 : (⟨n, hnL⟩ : M) ∈ CFSG.Assembly.Dichotomy.involutionOddCore (⟨f, hfL⟩ : M) :=
      LocalBalance.subgroupOf_involutionOddCore_le ⟨f, hfL⟩ (Subgroup.mem_subgroupOf.mpr hn)
    exact map_involutionOddCore_le φ (MonoidHom.rangeRestrict_surjective _)
      (isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext hf2 : (⟨f, hfL⟩ : M) * ⟨f, hfL⟩ = 1))
      (Subgroup.mem_map_of_mem φ h1)
  have ht1 : φ ⟨f, hfL⟩ ≠ 1 := by
    intro h1
    apply hfc
    have h2 : rhoL L ⟨f, hfL⟩ = 1 := congrArg Subtype.val h1
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((ObsPump.rhoL_eq_one_iff hs.comp ⟨f, hfL⟩).mp h2 l hl).symm
  have ht2 : orderOf (φ ⟨f, hfL⟩) = 2 := by
    refine orderOf_eq_prime ?_ ht1
    rw [← map_pow, sq, show (⟨f, hfL⟩ : M) * ⟨f, hfL⟩ = 1 from Subtype.ext hf2, map_one]
  rw [h (↥L ⧸ center ↥L) hP (rhoL L).range hInn (φ ⟨f, hfL⟩) ht2, Subgroup.mem_bot] at hcore
  apply hnc
  have h1 : rhoL L ⟨n, hnL⟩ = 1 := congrArg Subtype.val hcore
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact ((ObsPump.rhoL_eq_one_iff hs.comp ⟨n, hnL⟩).mp h1 l hl).symm

theorem ghList_quot {Y : Type} [Group Y] {L B X₀ : Subgroup Y} {z : Y}
    (hs : Setting125 Y L B X₀ z) : GHList (↥L ⧸ center ↥L) :=
  hs.secGH L (center ↥L) inferInstance hs.comp.1.2.1 hs.comp.1.2.2

section Ree


theorem locBal1For_ree : LocBal1For Ree2G2 := by
  intro T _ _ hT H hH t ht
  obtain ⟨f, -, hf⟩ := hT
  exact LocBalRee.involutionOddCore_eq_bot_ree ⟨f, hf⟩ hH ht

theorem cell125_ree : Cell125 Ree2G2 :=
  cell125_of_locBal1For locBal1For_ree

end Ree

theorem lem125p2_of_cells (hS : Cell125 SporGH) (hE : Cell125 Even2GH) (hL34 : Cell125 L34)
    (hA : Cell125 Alt810) (hA9 : Cell125 Alt9) (h2 : Cell125 OddL2) (h3 : Cell125 OddL3)
    (hSp : Cell125 OddSp4) (hG2 : Cell125 OddG2) (hD4 : Cell125 Odd3D4) (h4 : Cell125 OddL4)
    (h5 : Cell125 OddL5) (hR : Cell125 Ree2G2) : Lem125p2 := by
  intro Y _ _ L B X₀ z hs hsig hcut
  have key : ∀ {P : ∀ (T : Type) [Group T], Prop}, Cell125 P → P (↥L ⧸ center ↥L) → False :=
    fun hP hp => hP Y L B X₀ z hs hp hsig hcut
  rcases ghList_quot hs with ⟨n, h7, h11, hn⟩ | hspor | ⟨p, f, hp, hf, hrow⟩
  · interval_cases n
    · exact Or.inl hn
    · exact (key hA (Or.inl hn)).elim
    · exact (key hA9 hn).elim
    · exact (key hA (Or.inr hn)).elim
    · exact Or.inr hn
  · exact (key hS hspor).elim
  · exfalso
    rcases hrow with ⟨hp2, hl2 | hl3 | hu3 | hsp | hg2 | hd4⟩ | ⟨hp2, h8, hl4⟩ | ⟨hp2, h8, hu4⟩ |
      ⟨h4m, hl5⟩ | ⟨h4m, hu5⟩ | hree | ⟨-, hl28 | hl216 | hl34 | hu34 | hsz⟩
    · exact key h2 ⟨p, f, hp, hp2, hf, hl2⟩
    · exact key h3 ⟨p, f, hp, hp2, hf, Or.inl hl3⟩
    · exact key h3 ⟨p, f, hp, hp2, hf, Or.inr hu3⟩
    · exact key hSp ⟨p, f, hp, hp2, hf, hsp⟩
    · exact key hG2 ⟨p, f, hp, hp2, hf, hg2⟩
    · exact key hD4 ⟨p, f, hp, hp2, hf, hd4⟩
    · exact key h4 ⟨p, f, hp, hp2, hf, Or.inl ⟨h8, hl4⟩⟩
    · exact key h4 ⟨p, f, hp, hp2, hf, Or.inr ⟨h8, hu4⟩⟩
    · exact key h5 ⟨p, f, hp, hf, Or.inl ⟨h4m, hl5⟩⟩
    · exact key h5 ⟨p, f, hp, hf, Or.inr ⟨h4m, hu5⟩⟩
    · exact key hR ⟨f, hf, hree⟩
    · exact key hE (Or.inl hl28)
    · exact key hE (Or.inr (Or.inl hl216))
    · exact key hL34 hl34
    · exact key hE (Or.inr (Or.inr (Or.inl hu34)))
    · exact key hE (Or.inr (Or.inr (Or.inr hsz)))

end CFSG.GH74.Generic.BProg.B3.S3T2A7
