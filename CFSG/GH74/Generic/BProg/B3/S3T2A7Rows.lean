module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7WS
public import CFSG.GH74.Generic.BProg.B2.L3Cover
public import CFSG.GH74.Generic.ClassicalCerts
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.CompletedOddCoreElimination
public import CFSG.GH74.E2.ComponentsShape
public import CFSG.GH74.GLS.Bg.Iii2.L41Comp
public import CFSG.GH74.GLS.C3.Layer1.Th2V2Core
public import CFSG.GH74.Generic.BProg.B3.ObsPump
public import CFSG.GroupTheory.ElementaryAbelianBasis
public import Certificates.Certificate5007

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.RankThree.PerfectCover
open scoped MatrixGroups

@[expose] def OddL4m (T : Type) [Group T] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    ((p ^ f % 4 = 3 ∧ LieModel T .PSL 4 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel T .PSU 4 p f))

@[expose] def OddL4p (T : Type) [Group T] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    ((p ^ f % 8 = 5 ∧ LieModel T .PSL 4 p f) ∨ (p ^ f % 8 = 3 ∧ LieModel T .PSU 4 p f))

theorem cell125_oddL4_of (hm : Cell125 OddL4m) (hp : Cell125 OddL4p) : Cell125 OddL4 := by
  intro Y _ _ L B X₀ z hs hP hsig hcut
  obtain ⟨p, f, hpr, hp2, hf, hrow⟩ := hP
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp ((hpr.odd_of_ne_two hp2).pow)
  rcases hrow with ⟨h8, hL⟩ | ⟨h8, hU⟩
  · by_cases h4 : p ^ f % 4 = 3
    · exact hm Y L B X₀ z hs ⟨p, f, hpr, hp2, hf, Or.inl ⟨h4, hL⟩⟩ hsig hcut
    · exact hp Y L B X₀ z hs ⟨p, f, hpr, hp2, hf, Or.inl ⟨by omega, hL⟩⟩ hsig hcut
  · by_cases h4 : p ^ f % 4 = 1
    · exact hm Y L B X₀ z hs ⟨p, f, hpr, hp2, hf, Or.inr ⟨h4, hU⟩⟩ hsig hcut
    · exact hp Y L B X₀ z hs ⟨p, f, hpr, hp2, hf, Or.inr ⟨by omega, hU⟩⟩ hsig hcut

theorem false_of_cert3_odd_multiplier {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y}
    {z : Y} (hs : Setting125 Y L B X₀ z) {X : Type} [Group X] (e : (↥L ⧸ center ↥L) ≃* X)
    (hc : RankCertified X 3) (hodd : Odd (Nat.card (hopfMultiplier X))) : False := by
  have hzL := mem_of_rankCertified_three hs (hc.of_mulEquiv e.symm)
  rcases B2.L3Cover.center_eq_bot_or_odd_of hs.comp.1 e hodd with ⟨ζ, hζ1, hζc, hζo⟩ | hc0
  · apply hζ1
    refine Subtype.ext (B2.FamilyOddCentre.odd_central_eq_one hs.core hs.comp ζ.2
      (fun g hg => congrArg Subtype.val (hζc ⟨g, hg⟩)) ?_)
    rwa [Subgroup.orderOf_coe]
  · have hmem : (⟨z, hzL⟩ : ↥L) ∈ center ↥L :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hs.z_cent g)
    rw [hc0, Subgroup.mem_bot] at hmem
    exact hs.z_ne (congrArg Subtype.val hmem)

section L5


theorem cell125_oddL5 : Cell125 OddL5 := by
  intro Y _ _ L B X₀ z hs hP _ _
  obtain ⟨p, f, hp, hf, hrow⟩ := hP
  rcases hrow with ⟨h4, hL⟩ | ⟨h4, hU⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel hL (by decide)
    have : Fintype K := Fintype.ofFinite K
    have hKc : Fintype.card K = p ^ f := Fintype.card_eq_nat_card.trans hK
    have hKodd : Fintype.card K % 2 = 1 := by omega
    have hch : ringChar K ≠ 2 := fun h => by
      have := (FiniteField.even_card_iff_char_two (F := K)).mp h
      omega
    let e' := e.trans (projectiveSpecialLinearGroupEquivStatedProj 5 K).symm
    refine false_of_cert3_odd_multiplier hs e'
      ((rankCertified_PSL5 hch).of_mulEquiv (projectiveSpecialLinearGroupEquivStatedProj 5 K).symm)
      ?_
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_five_le (k := K) (n := 5)
        le_rfl
    rw [← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv, Nat.card_congr eM.toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 5 _)
  · obtain ⟨⟨-, hf', -, hne⟩, K, _, _, hK, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel hU (by decide)
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow hp hK
    have hq : p ^ f % 2 = 1 := by omega
    refine false_of_cert3_odd_multiplier hs e (rankCertified_PSU5 hK hq) ?_
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier hK hf' (n := 5) (by norm_num)
        (by decide) (by simp)
    rw [← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv, Nat.card_congr eM.toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 5 _)

end L5

end CFSG.GH74.Generic.BProg.B3.S3T2A7
