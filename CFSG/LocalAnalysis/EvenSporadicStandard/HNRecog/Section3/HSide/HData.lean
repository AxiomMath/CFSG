module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Dict
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

@[expose] def HSideData (b z : G) : Prop :=
  ∃ (E : Subgroup ↥(Gx b)) (z₀ b₀ u₀ : ↥(Gx b)), TwoHS.IsF5Centralizer ↥(Gx b) E ∧
    HLab b z z₀ b₀ u₀ ∧ A8Dict z₀ b₀

theorem a8Dict_of_pictures {b z : G} {z₀ b₀ u₀ : ↥(Gx b)} (hPic : A8Pictures b z)
    (L : HLab b z z₀ b₀ u₀) : A8Dict z₀ b₀ := by
  intro φ t ht
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_derivedOf_Gxy_subtype (b := b) b₀ φ
  have hb₀ : (b₀ : G) ∈ orb2A b b := ⟨L.b₀_A, L.bb₀_A⟩
  have hfig := hPic.fig8b (b₀ : G) hb₀ ψ t ht
  have hz : IsConj z (((φ t : ↥(derivedOf (Gx b₀))) : ↥(Gx b)) : G) := by
    have := hfig.1
    rwa [hψ t] at this
  refine (L.isConj_z₀_iff hz).2 ?_
  have := hfig.2.1
  rwa [hψ t] at this

theorem exists_hSideData (hI : TwoHSInterface) {b z : G} (hbF : IsF5Type b z)
    (hF1 : Fusion1Facts b z) (hF2 : Fusion2Facts b z) (hPic : A8Pictures b z) : HSideData b z := by
  obtain ⟨E, hE⟩ := hbF.cent_a
  obtain ⟨z₀, b₀, u₀, hF, hz₀, hbz₀, -⟩ := hF1.rep_z
  obtain ⟨⟨hb, hbb, -, -⟩, ⟨hu, hbu, -⟩⟩ := hF2.reps_bu z₀ b₀ u₀ hF hz₀
  have hL : HLab b z z₀ b₀ u₀ :=
    ⟨hF, not_isConj_of_isF5Type hI hbF, hz₀, hbz₀, hb, hbb, hu, hbu⟩
  exact ⟨E, z₀, b₀, u₀, hE, hL, a8Dict_of_pictures hPic hL⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
