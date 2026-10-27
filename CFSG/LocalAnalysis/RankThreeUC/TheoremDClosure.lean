module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDSolvableQuotient
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClosureCount
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClosurePick
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClosureComb
import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.Quasithin.Background.B216Quotient

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_card_of_two_le_pRank {K : Subgroup G} (h : 2 ≤ CFSG.Open.pRank 3 K) :
    3 ∣ Nat.card K := by
  obtain ⟨E, hEK, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) K
  have h3 : 3 ∣ Nat.card E := by
    rw [hE]
    exact dvd_pow_self 3 (by omega)
  exact h3.trans (Subgroup.card_dvd_of_le hEK)

theorem IsWitnessGen.normalizer_le_of_normalizer_le_inf_centralizer_thompsonJ_core
    (hS : StandingGen G) {P : Sylow 3 G} {M : Subgroup G} (hp : IsWitnessPrime 3 P)
    (hw : IsWitnessGen 3 P M) {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hSE : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M)
    (hsolv : Group.IsSolvable ↥(autOn M (uCore M T)))
    (hJe : ¬ thompsonJ T ≤ centralizer (uCore M T : Set G))
    (hJM : 2 ≤ CFSG.Open.pRank 3 (thompsonJ M))
    (hN' : normalizer (T : Set G) ≤
      normalizer ((uCore M T ⊓ centralizer (thompsonJ T : Set G) : Subgroup G) : Set G)) :
    normalizer (T : Set G) ≤ M := by
  classical
  obtain ⟨hU, hred, hcase, -⟩ := B2_16_of_quot (hS.charTwo M hw.maxLocal.1) hsolv
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hT) (uCore_eq_conjClosure M T)
  rcases hcase with ⟨hJ, -⟩ | ⟨-, I, hSyl, hN, hcomm, hindep, hnat, -, -, hvindep, hperm⟩
  · exact absurd hJ hJe
  have hMN : M ≤ normalizer (uCore M T : Set G) := hred.2.1
  have hJMM : thompsonJ M ≤ M := thompsonJ_le_self M
  have hJTM : thompsonJ T ≤ M := (thompsonJ_le_self T).trans hT.le
  have hBD : BlockData (autI hU M) I :=
    ⟨hcomm, hindep, hnat, hvindep, hperm, by rw [← hN]; exact autI_mono hU hJMM⟩
  have hAcomm : ∀ a ∈ uCore M T ⊓ centralizer (thompsonJ T : Set G),
      ∀ b ∈ uCore M T ⊓ centralizer (thompsonJ T : Set G), a * b = b * a := by
    have := hU.1
    intro a ha b hb
    exact setLike_mul_comm ha.1 hb.1
  have hA2 : ∀ a ∈ uCore M T ⊓ centralizer (thompsonJ T : Set G), a ^ 2 = 1 :=
    fun a ha => hU.2 a ha.1
  have hAe : IsElemAbelian 2 (uCore M T ⊓ centralizer (thompsonJ T : Set G)) :=
    ⟨⟨⟨fun a b => Subtype.ext (hAcomm a a.2 b b.2)⟩⟩, hA2⟩
  refine hw.normalizer_le_of_ncard_lt hSE hAe hN' ?_
  have hI : I.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    have hbot : autI hU (thompsonJ M) = ⊥ := by rw [hN]; simp
    have hle : thompsonJ M ≤ centralizer (uCore M T : Set G) :=
      (autI_eq_bot_iff hU (hJMM.trans hMN)).1 hbot
    exact hJe ((thompsonJ_le_thompsonJ_of_isSylowTwoOf
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hT)).trans hle)
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEM, hE, hEc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 3)
      (hw.three_le_pRank hp)
  have hEcard : Nat.card E = 27 := by
    rw [hEc]
    norm_num
  have hgb : ∀ a : G, 2 ≤ CFSG.Open.pRank 3 (M ⊓ centralizer ({a} : Set G)) →
      ¬ ¬ 3 ∣ Nat.card ↥(M ⊓ centralizer ({a} : Set G)) :=
    fun a ha h => h (three_dvd_card_of_two_le_pRank ha)
  by_cases h1 : I.card = 1
  · obtain ⟨L, rfl⟩ := Finset.card_eq_one.1 h1
    have hL : L ∈ ({L} : Finset (Subgroup (MulAut (IntMod (uCore M T) hU)))) :=
      Finset.mem_singleton_self L
    obtain ⟨x, ε, hP⟩ := exists_pickFacts hU hMN hJTM hBD hN hSyl hL
    refine comb_one (A := uCore M T ⊓ centralizer (thompsonJ T : Set G))
      (H := (uCore M T ⊓ centralizer (thompsonJ T : Set G)) ⊓ centralizer ({x} : Set G)) _ _
      hAcomm hA2 hgb inf_le_left
      (fun a ha haH b hb hbH => hP.mul_mem_inf_centralizer ha hb haH hbH)
      (fun a ha hbad haH => hbad (hP.three_dvd_card hJMM
        (mem_centralizer_singleton_iff.1 haH.2).symm)) ?_ hP.eps_mem hP.eps_not_mem ?_
    · intro a haH ha1
      have hall : ∀ m ∈ thompsonJ M, m * a = a * m := by
        intro m hm
        have hmN : m ∈ normalizer (uCore M T : Set G) := hMN (hJMM hm)
        have hmL : convI hU ⟨m, hmN⟩ ∈ L := by
          have h := convI_mem_autI hU hm hmN
          rw [hN] at h
          simpa using h
        exact hP.gen a haH.1 (mem_centralizer_singleton_iff.1 haH.2).symm m hmN hmL
      exact two_le_pRank_inf_centralizer_of_centralized hJMM hJM hall
    · exact two_le_pRank_inf_centralizer_of_block hU hMN hBD (by simp) hL hP.εV hP.ε1 hEM hE
        hEcard
  by_cases h2 : I.card = 2
  · obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.1 h2
    have hL₁ : L₁ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod (uCore M T) hU)))) := by simp
    have hL₂ : L₂ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod (uCore M T) hU)))) := by simp
    obtain ⟨x₁, ε₁, hP₁⟩ := exists_pickFacts hU hMN hJTM hBD hN hSyl hL₁
    obtain ⟨x₂, ε₂, hP₂⟩ := exists_pickFacts hU hMN hJTM hBD hN hSyl hL₂
    refine comb_two (A := uCore M T ⊓ centralizer (thompsonJ T : Set G))
      (H₁ := (uCore M T ⊓ centralizer (thompsonJ T : Set G)) ⊓ centralizer ({x₁} : Set G))
      (H₂ := (uCore M T ⊓ centralizer (thompsonJ T : Set G)) ⊓ centralizer ({x₂} : Set G)) _ _
      hAcomm hA2 hgb inf_le_left inf_le_left
      (fun a ha haH b hb hbH => hP₁.mul_mem_inf_centralizer ha hb haH hbH)
      (fun a ha haH b hb hbH => hP₂.mul_mem_inf_centralizer ha hb haH hbH)
      (fun a ha hbad haH => hbad (hP₁.three_dvd_card hJMM
        (mem_centralizer_singleton_iff.1 haH.2).symm))
      (fun a ha hbad haH => hbad (hP₂.three_dvd_card hJMM
        (mem_centralizer_singleton_iff.1 haH.2).symm))
      (fun a ha₁ ha₂ ha1 => two_le_pRank_inf_centralizer_of_pair hU hMN hBD hL₁ hL₂ hne
        (hJMM hP₁.xJ) (hJMM hP₂.xJ) hP₁.xL hP₁.x3 hP₁.x1 hP₂.xL hP₂.x3 hP₂.x1 ha₁.1.1
        (mem_centralizer_singleton_iff.1 ha₁.2).symm (mem_centralizer_singleton_iff.1 ha₂.2).symm)
      hP₁.eps_mem hP₁.eps_not_mem (hP₁.eps_mem_other hP₂ hL₂ hne.symm)
      hP₂.eps_mem hP₂.eps_not_mem (hP₂.eps_mem_other hP₁ hL₁ hne) ?_ ?_
    · exact two_le_pRank_inf_centralizer_of_block hU hMN hBD Finset.card_le_two hL₁ hP₁.εV
        hP₁.ε1 hEM hE hEcard
    · exact two_le_pRank_inf_centralizer_of_block hU hMN hBD Finset.card_le_two hL₂ hP₂.εV
        hP₂.ε1 hEM hE hEcard
  have h3 : 2 < I.card := by
    have := Finset.card_pos.2 hI
    omega
  obtain ⟨L₁, hL₁, L₂, hL₂, L₃, hL₃, h12, h13, h23⟩ := Finset.two_lt_card.1 h3
  obtain ⟨x₁, ε₁, hP₁⟩ := exists_pickFacts hU hMN hJTM hBD hN hSyl hL₁
  obtain ⟨x₂, ε₂, hP₂⟩ := exists_pickFacts hU hMN hJTM hBD hN hSyl hL₂
  obtain ⟨x₃, ε₃, hP₃⟩ := exists_pickFacts hU hMN hJTM hBD hN hSyl hL₃
  exact comb_three (A := uCore M T ⊓ centralizer (thompsonJ T : Set G))
    (H₁ := (uCore M T ⊓ centralizer (thompsonJ T : Set G)) ⊓ centralizer ({x₁} : Set G))
    (H₂ := (uCore M T ⊓ centralizer (thompsonJ T : Set G)) ⊓ centralizer ({x₂} : Set G))
    (H₃ := (uCore M T ⊓ centralizer (thompsonJ T : Set G)) ⊓ centralizer ({x₃} : Set G)) _ _
    hAcomm hA2 hgb inf_le_left inf_le_left inf_le_left
    (fun a ha haH b hb hbH => hP₁.mul_mem_inf_centralizer ha hb haH hbH)
    (fun a ha haH b hb hbH => hP₂.mul_mem_inf_centralizer ha hb haH hbH)
    (fun a ha haH b hb hbH => hP₃.mul_mem_inf_centralizer ha hb haH hbH)
    (fun a ha hbad haH => hbad (hP₁.three_dvd_card hJMM
      (mem_centralizer_singleton_iff.1 haH.2).symm))
    (fun a ha hbad haH => hbad (hP₂.three_dvd_card hJMM
      (mem_centralizer_singleton_iff.1 haH.2).symm))
    (fun a ha hbad haH => hbad (hP₃.three_dvd_card hJMM
      (mem_centralizer_singleton_iff.1 haH.2).symm))
    (fun a ha₂ ha₃ ha1 => two_le_pRank_inf_centralizer_of_pair hU hMN hBD hL₂ hL₃ h23
      (hJMM hP₂.xJ) (hJMM hP₃.xJ) hP₂.xL hP₂.x3 hP₂.x1 hP₃.xL hP₃.x3 hP₃.x1 ha₂.1.1
      (mem_centralizer_singleton_iff.1 ha₂.2).symm (mem_centralizer_singleton_iff.1 ha₃.2).symm)
    (fun a ha₁ ha₃ ha1 => two_le_pRank_inf_centralizer_of_pair hU hMN hBD hL₁ hL₃ h13
      (hJMM hP₁.xJ) (hJMM hP₃.xJ) hP₁.xL hP₁.x3 hP₁.x1 hP₃.xL hP₃.x3 hP₃.x1 ha₁.1.1
      (mem_centralizer_singleton_iff.1 ha₁.2).symm (mem_centralizer_singleton_iff.1 ha₃.2).symm)
    hP₁.eps_mem hP₁.eps_not_mem (hP₁.eps_mem_other hP₂ hL₂ h12.symm)
    (hP₁.eps_mem_other hP₃ hL₃ h13.symm) hP₂.eps_mem hP₂.eps_not_mem
    (hP₂.eps_mem_other hP₁ hL₁ h12) (hP₂.eps_mem_other hP₃ hL₃ h23.symm)

end CFSG.LocalAnalysis.RankThreeUC
