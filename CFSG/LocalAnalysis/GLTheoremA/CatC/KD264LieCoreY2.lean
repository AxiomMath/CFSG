module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieIdx
public import CFSG.GroupTheory.ElemAbelianRank
import CFSG.StronglyEmbedded.Catalog.SuzukiThree
public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.GroupActions

theorem kd264CaseY2_holds (hI : KD264LieInputs) : KD264CaseY2 := by
  intro d hd A m hβ hov2 hTri β hβA J hJ e heq hcomp he8 hN5 hAJ hcard hex
  haveI := hd
  have hfe8 : fieldSize e.1 = 8 := by
    obtain ⟨q, hq | hq, hq8⟩ := he8
    · rw [hq]; simpa [fieldSize] using hq8
    · rw [hq]; simpa [fieldSize] using hq8
  have hfd8 : fieldSize d.1 = 8 := by
    rcases fieldSize_of_compRel_of_eight hcomp hfe8 with h2 | h8
    · exact absurd h2 (by simpa [ov2Idx] using hov2)
    · exact h8
  have hsuz : ¬ ∃ k, d.1 = .suzuki k := by
    rintro ⟨k, hk⟩
    have hv : (TauCeti.LieTypeIndex.suzuki k).Valid := hk ▸ d.2
    have hdvd : 3 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := hβ.dvd
    rw [show d = ⟨.suzuki k, hv⟩ from Subtype.ext hk] at hdvd
    exact CFSG.BenderSuzuki.Catalog.not_three_dvd_card_lie_suzuki hv hdvd
  have hover : overEight d.1 := overEight_of_fieldSize_eq_eight hfd8 hsuz
  obtain ⟨a, haA, haStab, haOut⟩ := hex
  have hcomm : β * a = a * β := by
    haveI := hβ.elem.1
    exact congrArg Subtype.val (mul_comm' ⟨β, hβA⟩ ⟨a, haA⟩)
  have haNotInn : a ∉ innAutDerived (TauCeti.CFSGIndex.lie d).Group := by
    intro haInn
    exact haOut (hN5 a haInn (hβ.elem.2 a haA) hcomm haStab)
  have hnotA : ¬ A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group :=
    fun hle => haNotInn (hle haA)
  have hprA : CFSG.Open.pRank 3 A = m := pRank_eq_of_card hβ.prime hβ.elem hβ.card
  have hm4 : m ≤ 4 := by
    obtain ⟨D, hD, hAD⟩ := hcard
    obtain ⟨φ⟩ := heq
    haveI : Finite (TauCeti.CFSGIndex.lie e).Group := by
      haveI : Finite (↥J ⧸ Subgroup.center ↥J) :=
        Finite.of_surjective (QuotientGroup.mk' (Subgroup.center ↥J))
          (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
      exact Finite.of_equiv _ φ.toEquiv
    have hDcard : Nat.card D = 3 ^ CFSG.Open.pRank 3 D :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hβ.prime hD
    have hmono : CFSG.Open.pRank 3 D ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group)) :=
      CFSG.SectionRank.pRank_mono (by norm_num) le_top
    have htop : CFSG.Open.pRank 3
        (⊤ : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group)) ≤ 3 := by
      obtain ⟨q, hq | hq, hq8⟩ := he8
      · have h2 := (hI.i5Aut e).2.1 ⟨q, hq, hq8⟩
        omega
      · exact (hI.i5Aut e).2.2 ⟨q, hq, hq8⟩
    have hAle : Nat.card A ≤ 3 ^ 4 := by
      have h1 : Nat.card A = 3 ^ (CFSG.Open.pRank 3 D + 1) := by
        rw [hAD, hDcard, pow_succ]
        ring
      rw [h1]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hβ.card] at hAle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hAle
  have h3A : 3 ≤ CFSG.Open.pRank 3 A := by
    have := hβ.four_le
    omega
  have h4A : CFSG.Open.pRank 3 A ≤ 4 := by omega
  have hf4 : ∀ k, i5FieldBound d.1 k → k + 1 ≤ 4 := by
    intro k hk
    have := hβ.field rfl a haA haNotInn k hk
    omega
  have hfields := not_multIdx_field_of_overEight d hover hβ.notK2 hf4
  have hnoMult := hβ.noMult (not_multIdx_three_of_overEight hover hfields.1 hfields.2)
  exact hI.f8Row d hβ.notChev hβ.notK2 (fun hk => hβ.notK3 ⟨rfl, hk⟩) hover
    (fun htri => hnotA (hTri htri)) hfields.1 hfields.2
    A hβ.elem h3A h4A (by rw [hprA]; exact hnoMult.1)
    (fun a haA haconj E hE hEelem => by
      have := hnoMult.2 a haA haconj E hE hEelem
      omega)
    hnotA

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
