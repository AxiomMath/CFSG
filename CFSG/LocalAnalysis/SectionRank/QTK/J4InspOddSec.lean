module

public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspB1
public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspB2
public import CFSG.GH74.SectionalRank
public import CFSG.LocalAnalysis.SectionRank.QTK.FactJ4Of
public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA3
public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA5

public section

open scoped IsMulCommutative

namespace CFSG.SectionRank.QTK

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def OddCharSectionalTwoRankQTK : Prop :=
  ∀ (S : Type) [Group S] [Finite S], OddCharList S → CFSG.GH74.SectionalTwoRankLE S 8

theorem oddCharTwoRankQTK_of_sectional (h : OddCharSectionalTwoRankQTK) : OddCharTwoRankQTK := by
  intro S _ _ hB
  simpa only [CFSG.Open.twoRank] using (h S hB).twoRank_le

theorem two_pow_nine_le_card_frattini (hFM : FaithfulL34ModDim) {L : Type} [Group L] [Finite L]
    (Q : Subgroup L) [Q.Normal] (hQ : IsPGroup 2 ↥Q)
    (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤)
    (hPSL : CFSG.Quasithin.IsPSL 3 2 2 (L ⧸ Q)) (hnt : ⁅Q, (⊤ : Subgroup L)⁆ ≠ ⊥) :
    2 ^ 9 ≤ Nat.card (↥Q ⧸ frattini ↥Q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp : IsSimpleGroup (L ⧸ Q) := CFSG.Quasithin.H13.A5.isSimpleGroup_of_isPSL34 hPSL
  have hfe := CFSG.GroupTheory.frattini_elementary_quotient (p := 2) (P := ↥Q) hQ
  have hcomm : IsMulCommutative (↥Q ⧸ frattini ↥Q) := hfe.2.1
  have hexp : ∀ v : ↥Q ⧸ frattini ↥Q, v ^ 2 = 1 := hfe.2.2.1
  haveI := hcomm
  have hQC : Q ≤ (frattiniConjAct Q).ker := by
    intro q hq
    exact MonoidHom.mem_ker.mpr (frattiniConjAct_of_mem Q hQ ⟨q, hq⟩)
  let ψ : L ⧸ Q →* MulAut (↥Q ⧸ frattini ↥Q) := QuotientGroup.lift Q (frattiniConjAct Q) hQC
  have hψ : ∀ x : L, ψ (QuotientGroup.mk' Q x) = frattiniConjAct Q x := fun x => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q a
    rw [hψ] at ha
    have hx : x ∈ Q := frattini_kernel_le Q hQ hperf hsimp hnt x ha
    exact (QuotientGroup.eq_one_iff x).mpr hx
  have hPSLX : CFSG.Quasithin.IsPSL 3 2 2 ↥ψ.range :=
    isPSL_of_mulEquiv (MonoidHom.ofInjective hinj) hPSL
  exact hFM (↥Q ⧸ frattini ↥Q) hexp ψ.range hPSLX

theorem odd_branch_false_of_sectional (hSec : OddCharSectionalTwoRankQTK) (hFM : FaithfulL34ModDim)
    {S : Type} [Group S] [Finite S] (hB : OddCharList S)
    {L : Type} [Group L] [Finite L] (j : L →* S) (hj : Function.Injective j)
    (Q : Subgroup L) [Q.Normal] (hQ : IsPGroup 2 ↥Q)
    (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤)
    (hPSL : CFSG.Quasithin.IsPSL 3 2 2 (L ⧸ Q)) (hnt : ⁅Q, (⊤ : Subgroup L)⁆ ≠ ⊥) : False := by
  have h9 := two_pow_nine_le_card_frattini hFM Q hQ hperf hPSL hnt
  have hsec : CFSG.GH74.SectionalTwoRankLE ↥Q 8 :=
    (CFSG.GH74.SectionalTwoRankLE.of_injective j hj (hSec S hB)).subgroup Q
  have hquot : CFSG.GH74.SectionalTwoRankLE (↥Q ⧸ frattini ↥Q) 8 :=
    hsec.quotient (frattini ↥Q)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfe := CFSG.GroupTheory.frattini_elementary_quotient (p := 2) (P := ↥Q) hQ
  have hEab : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup (↥Q ⧸ frattini ↥Q)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · exact Subtype.ext
        (hfe.2.1.is_comm.comm (a : ↥Q ⧸ frattini ↥Q) (b : ↥Q ⧸ frattini ↥Q))
    · intro x _
      exact hfe.2.2.1 x
  have hcard : Nat.card (↥Q ⧸ frattini ↥Q) ≤ 2 ^ 8 := by
    have h := hquot.card_le_of_elementary (⊤ : Subgroup (↥Q ⧸ frattini ↥Q)) hEab
    rwa [Subgroup.card_top] at h
  norm_num at h9 hcard
  omega

theorem j4ListInspect_of_sectional
    (hFM : FaithfulL34ModDim) (hChar2 : Char2LeviFactorsRank2) (hL34Levi : L34NotLeviFamily)
    (hSec : OddCharSectionalTwoRankQTK) (hSp6 : Sp6TwoOrder) : J4ListInspect := by
  unfold J4ListInspect
  intro S _ _ hS L _ _ j hj hperf Q _ hQ hPSL hnt
  unfold QTKSimpleList at hS
  have h15 := two_pow_fifteen_dvd_card hFM j hj Q hQ hperf hPSL hnt
  rcases hS with hA | hB | hC | hD | hE
  · obtain ⟨n, h5, h9, ⟨e⟩⟩ := hA
    exact absurd h15 (not_two_pow_fifteen_dvd_alt h5 h9 e)
  · exact (odd_branch_false_of_sectional hSec hFM hB j hj Q hQ hperf hPSL hnt).elim
  · exact (char2_branch_false hChar2 hL34Levi hC j hj Q hQ hperf hPSL hnt).elim
  · rcases hD with ⟨n, hn, hPSLn⟩ | hPSp
    · exact absurd h15 (not_two_pow_fifteen_dvd_psl_four_five_two hn hPSLn)
    · rw [hSp6 S hPSp] at h15
      norm_num at h15
  · obtain ⟨s, hs, ⟨e⟩⟩ := hE
    by_cases hJ : s = .J4
    · subst hJ
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
      exact ⟨e.trans b⟩
    · exfalso
      have hs' : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨
          s = .J3 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .McL := by
        tauto
      have hc : Nat.card S = Nat.card (CFSG.Blueprint.NativeSporadic.Carrier s) :=
        Nat.card_congr e.toEquiv
      rw [hc] at h15
      exact not_two_pow_fifteen_dvd_sporadic s hs' h15

theorem j4ListInspect_of_char2_sectional
    (hChar2 : Char2LeviFactorsRank2) (hSec : OddCharSectionalTwoRankQTK) : J4ListInspect :=
  j4ListInspect_of_sectional faithfulL34ModDim_holds hChar2 l34NotLeviFamily_holds hSec
    sp6TwoOrder_holds

end CFSG.SectionRank.QTK

end
