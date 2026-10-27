module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBInputs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
import CFSG.LocalAnalysis.ComponentClassification.Walter86.Asc75.L97Prep
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankSmallSources
import CFSG.Quasithin.SteinbergCCRankOneSplitting
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup

variable {B : Type} [Group B] [Finite B]

open CFSG.CGT.PushingUpLit.CGT6
open CFSG.OddStandard.SmallF3

theorem isSubnormal_or_standard_of_star (h5 : GSThmB.AschbacherTheorem5Input)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) {A : Subgroup B}
    (hA : CFSG.IsQuasisimple ↥A)
    (hstar : ∀ v : B, orderOf v = 2 → A ≤ centralizer ({v} : Set B) →
      IsComponent (A.subgroupOf (centralizer ({v} : Set B))))
    {a : B} (ha : orderOf a = 2) (hAa : A ≤ centralizer ({a} : Set B))
    (hA2 : 2 ≤ CFSG.pRank 2 ↥A) :
    A.IsSubnormal ∨ Open.standardComponentIsStandard A := by
  have hQA : Nine7.QS A :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥A).2 hA
  have hs : Nine7.Star A := fun v hv hAv => (hstar v hv hAv).2
  have hglaub : Nine7.GlaubermanAt (↥A ⧸ Subgroup.center ↥A) :=
    CFSG.ComponentClassification.Walter86.Asc75.glaubermanAt_holds _
  rcases Nine7.nine_seven_star h5 hK hQA hs hglaub with h1 | ⟨x, hx⟩ | h3
  ·
    refine Or.inr (Omega.standard_of_componentAtCentralInvolutions
      ⟨a, ha, hAa, hstar a ha hAa⟩ ?_ ?_)
    · intro y hy hyC
      have hAy : A ≤ centralizer ({y} : Set B) := by
        intro z hz
        rw [Nine7.mem_centralizer_single]
        exact (Subgroup.mem_centralizer_iff.mp hyC z hz).symm
      exact ⟨hAy, hstar y hy hAy⟩
    · intro g
      simpa [CFSG.conjugate] using h1.2.2 g⁻¹
  ·
    exfalso
    have hp1 : CFSG.Open.pRank 2 A = 1 := hx.2.2.1
    have hpA : CFSG.Open.pRank 2 A = CFSG.pRank 2 ↥A := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
        ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    omega
  · exact Or.inl h3

theorem two_le_pRank_of_quotient_center {T : Type} [Group T] {A : Subgroup B}
    (e : ↥A ⧸ center ↥A ≃* T) (hZ : Odd (Nat.card (center ↥A)))
    (hT : ∃ V : Subgroup T, IsKleinFour ↥V) : 2 ≤ CFSG.pRank 2 ↥A := by
  obtain ⟨V, hV⟩ := hT
  haveI : Finite T := Finite.of_surjective e e.surjective
  have hEA : IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [hV.exponent_two] }
  have hpT : 2 ≤ CFSG.pRank 2 T :=
    CFSG.ComponentClassification.UnbalancedGS.RankSmallSources.two_le_pRank_of_four hEA
      hV.card_four
  have hpQ : 2 ≤ CFSG.pRank 2 (↥A ⧸ center ↥A) := by
    rw [CFSG.pRank_congr_of_mulEquiv e 2]
    exact hpT
  have hI : ¬ 2 ∣ Nat.card (⊤ ⊓ center ↥A : Subgroup ↥A) := by
    simpa using hZ.not_two_dvd_nat
  have hquot : CFSG.pRank 2 (↥A ⧸ center ↥A) = CFSG.pRank 2 (⊤ : Subgroup ↥A) :=
    CFSG.Quasithin.SteinbergCC.pRank_quotient_eq_of_sup_eq_top (p := 2) Nat.prime_two
      (K₁ := ⊤) (K₂ := center ↥A) (by simp) hI
  have hpTop : 2 ≤ CFSG.pRank 2 (⊤ : Subgroup ↥A) := by
    rw [← hquot]
    exact hpQ
  simpa using (CFSG.pRank_congr_of_mulEquiv (Subgroup.topEquiv (G := ↥A)) 2) ▸ hpTop

end CFSG.ComponentClassification.FooteMarked
