module

public import CFSG.LocalAnalysis.GLTheoremA.Lemma56
public import CFSG.LocalAnalysis.GLTheoremA.P55.U43

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem prop55 {p : ℕ} (hc : Sec5Ctx G p) (hBex : ∃ B : Subgroup G, GLAIsBmax p B)
    (hrank : 4 ≤ GLATwoLocalRank p G) (h51 : Prop51At G p) (h113 : I113UsedAt G p)
    (h336 : I336UsedAt) (hdih : DihedralUsed) (h71 : I71UsedAt G p) (h2611 : I2611UsedAt G p)
    (h64 : I64UsedAt G p) : Prop55At G p := by
  by_contra hno
  have hp := hc.prime
  have hp2 := hc.odd
  obtain ⟨B, x, L, hBxL⟩ := exists_isS0Max hc.stage3 hc.stage4Order hBex
  have hS := hBxL.1.1
  have hB : GLAIsBmax p B := hS.1
  have hBCx : B ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer hB.1 hS.2.1.1
  obtain ⟨J, hJ, hJL, T, hTJ, hT2, hBT, hTB⟩ := lemma56 hc hno h51 h113 h336 hdih h71 hBxL
  have hBJ := lemma54 hc h51 h113 hBxL J hJ
  have hTne : T ≠ ⊥ := fun h => hTB (by rw [h]; exact Subgroup.commutator_bot_left B)
  have hoddJ : Odd (Nat.card (GLAPPrimeCoreOf p J)) := by
    have hle : GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
      rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hJ.2.1]
      exact inf_le_right
    exact Odd.of_dvd_nat (odd_card_glaPPrimeCoreOf_of_not_prop55 hp hno hBxL)
      (Subgroup.card_dvd_of_le hle)
  by_cases hZ : IsCyclic (Subgroup.center (PQuot p J))
  ·
    rcases h2611 B x J hB hS.2.1 hJ hBJ hoddJ ⟨T, hTJ, hT2, hBT, hTB⟩ hZ hrank with
      hGB | ⟨A, hA, hAJB, ⟨U, hUJB, hUne, hU2, hAU⟩, hdec, hAJ⟩
    · exact lemma57i hc hno hBxL hJ hBJ ⟨T, hTJ, hTne, hT2, hBT⟩ hGB
    · have hJB : J ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := sup_le hJ.1 hBCx
      exact hAJ (lemma57ii hc h51 hBxL hJ hJL hA (hAJB.trans hJB)
        ⟨U, hUJB.trans hJB, hUne, hU2, hAU⟩ hdec)
  ·
    apply P55.not_isCyclic_inf_of_not_isCyclic_center hp hp2 hB hJ hBJ hoddJ hTJ hTne hT2 hBT hZ
      (h64 B x J hB hS.2.1 hJ hBJ hZ)
    have hle : (B ⊓ J : Subgroup G) ≤ Subgroup.zpowers x := fun b hb =>
      (h51 B x L hBxL b hb.1).1
        (centMod_iff.2 (le_centModSubgroup_of_ne hp hJ hS.2.2 hJL hb.2))
    exact Subgroup.isCyclic_of_le hle

end CFSG.LocalAnalysis.GLTheoremA
