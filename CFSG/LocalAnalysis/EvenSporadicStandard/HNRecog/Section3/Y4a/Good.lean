module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.PairRep
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Conj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_conj_of_good (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) {x w x' w' : G} (hx : IsConj a x)
    (hw : IsConj z w) (hxw : x * w = w * x) (hxwB : IsConj z (x * w)) (hx' : IsConj a x')
    (hw' : IsConj z w') (hxw' : x' * w' = w' * x') (hxwB' : IsConj z (x' * w')) :
    ∃ g : G, g * x * g⁻¹ = x' ∧ g * w * g⁻¹ = w' := by
  have hnot : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  obtain ⟨z₀, u, hrep⟩ := exists_pair_reps hI h hF1 hF2
  obtain ⟨g₁, hg₁x, hg₁w⟩ : ∃ g : G, g * x * g⁻¹ = a ∧ g * w * g⁻¹ = u := by
    rcases hrep x w hx hw hxw with ⟨hA, -⟩ | ⟨-, hg⟩
    · exact absurd (hA.trans hxwB.symm) hnot
    · exact hg
  obtain ⟨g₂, hg₂x, hg₂w⟩ : ∃ g : G, g * x' * g⁻¹ = a ∧ g * w' * g⁻¹ = u := by
    rcases hrep x' w' hx' hw' hxw' with ⟨hA, -⟩ | ⟨-, hg⟩
    · exact absurd (hA.trans hxwB'.symm) hnot
    · exact hg
  refine ⟨g₂⁻¹ * g₁, ?_, ?_⟩
  · calc g₂⁻¹ * g₁ * x * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * x * g₁⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (g₂ * x' * g₂⁻¹) * g₂ := by rw [hg₁x, hg₂x]
      _ = x' := by group
  · calc g₂⁻¹ * g₁ * w * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * w * g₁⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (g₂ * w' * g₂⁻¹) * g₂ := by rw [hg₁w, hg₂w]
      _ = w' := by group

theorem y4a_good_data (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) {x w : G} (hx : IsConj a x)
    (hw : IsConj z w) (hxw : x * w = w * x) (hxwB : IsConj z (x * w)) :
    IsElemTwo 5 (Qz w ⊓ Gx x) ∧
      CFSG.Open.pCoreOf 2 (derivedOf (Gxy x w)) = Qz w ⊓ Qz (x * w) ∧
      IsElemTwo 4 (Qz w ⊓ Qz (x * w)) := by
  obtain ⟨z₀, b, u, hF, hz₀, -, -, -, -, -⟩ := hF1.rep_z
  obtain ⟨-, ⟨huB, hauB, -, h5, hM, h4, -⟩⟩ := hF2.reps_bu z₀ b u hF hz₀
  obtain ⟨g, hga, hgu⟩ := y4a_conj_of_good hI h hF1 hF2 (IsConj.refl a) huB
    (mem_Gx.mp u.2) hauB hx hw hxw hxwB
  have hd := y4a_conj_data g h5 hM h4
  rw [hga, hgu] at hd
  exact hd

end CFSG.EvenSporadicStandard.HNRecog.Section3
