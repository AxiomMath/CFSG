module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.HData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XSets
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XFusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem exists_tableX_at (hI : TwoHSInterface) (hS : SuborbitFacts) {G : Type} [Group G] {a z p : G}
    (hbF : IsF5Type p z) (hF1 : Fusion1Facts p z) (hF2 : Fusion2Facts p z) (hPic : A8Pictures p z)
    (hap : IsConj a p) (hzp : z ∈ Gx p) (hpz : IsConj p (p * z)) :
    ∃ (x b₀ u₀ : ↥(Gx p)), (x : G) = z ∧ TableXData (GxSelf p) x b₀ u₀ ∧
      orb2A a p ∩ orb2A a (p * z) = Subtype.val '' tabXSet (GxSelf p) x b₀ u₀ 0 ∧
      orb2A a p ∩ orb2B a z (p * z) = Subtype.val '' tabXSet (GxSelf p) x b₀ u₀ 1 ∧
      CFSG.Open.pCoreOf 2 (Gxy p z) = Gxy p z ⊓ Qz z := by
  obtain ⟨E, hE⟩ := hbF.cent_a
  obtain ⟨z₀, b₀, u₀, hF, hz₀, hbz₀, -, -, hpc, -⟩ := hF1.rep_z
  obtain ⟨⟨hb, hbb, -, -⟩, ⟨hu, hbu, -⟩⟩ := hF2.reps_bu z₀ b₀ u₀ hF hz₀
  have hL : HLab p z z₀ b₀ u₀ :=
    ⟨hF, not_isConj_of_isF5Type hI hbF, hz₀, hbz₀, hb, hbb, hu, hbu⟩
  have hD : A8Dict z₀ b₀ := a8Dict_of_pictures hPic hL
  let x : ↥(Gx p) := ⟨z, hzp⟩
  have hx : IsConj z₀ x := (HLab.isConj_z₀_iff hL (t := x) (IsConj.refl z)).2 hpz
  have hT : TableXData (GxSelf p) x b₀ u₀ :=
    hS.tableX ↥(Gx p) E hE (GxSelf p) z₀ b₀ u₀ hF hD x hx
  have h1 : orb2A a p ∩ orb2A a (p * z) = Subtype.val '' tabXSet (GxSelf p) x b₀ u₀ 0 :=
    orb2A_inter_orb2A_eq hL hap hx
  have h2 : orb2A a p ∩ orb2B a z (p * z) = Subtype.val '' tabXSet (GxSelf p) x b₀ u₀ 1 :=
    orb2A_inter_orb2B_eq hL hap hx
  obtain ⟨h, hh⟩ := isConj_iff.1 hx
  have hhG : (h : G) * (z₀ : G) * (h : G)⁻¹ = z := by
    have := congrArg (fun y : ↥(Gx p) => (y : G)) hh
    simpa using this
  have hpc' : CFSG.Open.pCoreOf 2 (Gxy p z) = Qz z ⊓ Gx p :=
    pCore_Gxy_of_conj h.2 hhG hpc
  have hR : CFSG.Open.pCoreOf 2 (Gxy p z) = Gxy p z ⊓ Qz z := by
    rw [← Gxy_inf_Qz_eq p z] at hpc'
    exact hpc'
  exact ⟨x, b₀, u₀, rfl, hT, h1, h2, hR⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
