module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLBasic
public import CFSG.GH74.Generic.BProg.B3.S3T2A7Rows

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def OddL4Eq (T : Type) [Group T] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    ((p ^ f % 4 = 1 ∧ LieModel T .PSL 4 p f) ∨ (p ^ f % 4 = 3 ∧ LieModel T .PSU 4 p f))

theorem cell125_l4eq (hF : GenericKnownFacts) : Cell125 OddL4Eq := by
  intro Y _ _ L B X₀ z hs hL _ _
  have hP2 := GLR.isPGroup_center hs
  obtain ⟨p, f, hp, hp2, -, ⟨h4, hm⟩ | ⟨h4, hm⟩⟩ := hL
  · obtain ⟨-, -, F, _, _, hFc, ⟨e⟩⟩ := lieModel_psl_data hm
    have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_card_eq hp hp2 hFc
    have hc3 : RankCertified (↥L ⧸ center ↥L) 3 := (rankCertified_PSL4 hF2).of_mulEquiv e.symm
    have hZ := GLR.center_ne_bot_of_mem hs (mem_of_rankCertified_three hs hc3)
    have hodd : Odd (Nat.card F) := by rw [hFc]; exact (hp.odd_of_ne_two hp2).pow
    obtain ⟨π, hπ, hcompat⟩ := hF.psl4_cover ↥L hs.comp.1 hP2 F hodd e
    rcases cover_branch_SL4 hF2 e π hπ hcompat hZ with ⟨hmod, -⟩ | ⟨-, hc4⟩
    · rw [hFc] at hmod
      omega
    · exact GLR.false_of_rankCertified_four hs hc4
  · obtain ⟨-, -, F, _, _, hFc, ⟨e⟩⟩ := lieModel_psu_data hm
    have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hc3 : RankCertified (↥L ⧸ center ↥L) 3 :=
      (rankCertified_PSU4 hFc (Nat.odd_iff.1 hqodd)).of_mulEquiv e.symm
    have hZ := GLR.center_ne_bot_of_mem hs (mem_of_rankCertified_three hs hc3)
    obtain ⟨π, hπ, hcompat⟩ := hF.psu4_cover ↥L hs.comp.1 hP2 F (p ^ f) hFc hqodd e
    rcases cover_branch_SU4 hFc (Nat.odd_iff.1 hqodd) e π hπ hcompat hZ with
      ⟨hmod, -⟩ | ⟨-, hc4⟩
    · omega
    · exact GLR.false_of_rankCertified_four hs hc4

theorem cell125_l4p (hF : GenericKnownFacts) : Cell125 OddL4p :=
  cell125_of_imp (fun _ _ ⟨p, f, hp, hp2, hf, hrow⟩ => ⟨p, f, hp, hp2, hf,
    hrow.imp (fun ⟨h8, hm⟩ => ⟨by omega, hm⟩) (fun ⟨h8, hm⟩ => ⟨by omega, hm⟩)⟩)
    (cell125_l4eq hF)

end CFSG.GH74.Generic.BProg.B3.S3T2A7
