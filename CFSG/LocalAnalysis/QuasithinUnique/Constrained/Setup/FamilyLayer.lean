module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem ActorLayer.odd_card_center {V : Type} [CommGroup V] [Finite V]
    {H T M : Subgroup (MulAut V)} (hLay : ActorLayer V H T M) {L : Subgroup (MulAut V)}
    (hL : IsComp L H) : Odd (Nat.card (Subgroup.center ↥L)) := by
  have hLK : L ≤ oddOrderSubgroup H := by
    rw [← hLay.components_generate]
    exact le_iSup₂ (f := fun (L' : Subgroup (MulAut V)) (_ : IsComp L' H) => L') L hL
  have hle : (Subgroup.center ↥L).map L.subtype ≤ centerIn (oddOrderSubgroup H) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hLK z.2, ?_⟩
    have hK : oddOrderSubgroup H ≤ Subgroup.centralizer ({(z : MulAut V)} : Set (MulAut V)) := by
      rw [← hLay.components_generate]
      refine iSup₂_le fun L' hL' x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      by_cases hLL' : L = L'
      · subst hLL'
        have := Subgroup.mem_center_iff.1 hz ⟨x, hx⟩
        exact (congrArg Subtype.val this).symm
      · exact hLay.components_commute L L' hL hL' hLL' z z.2 x hx
    exact Subgroup.mem_centralizer_iff.2 fun y hy => by
      have := Subgroup.mem_centralizer_iff.1 (hK hy) z (Set.mem_singleton _)
      exact this.symm
  have hdvd : Nat.card ((Subgroup.center ↥L).map L.subtype) ∣
      Nat.card (centerIn (oddOrderSubgroup H)) := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective L.subtype_injective] at hdvd
  have hodd : Odd (Nat.card (centerIn (oddOrderSubgroup H))) := by
    rw [← hLay.fitting_eq_center, ← hLay.rad_eq_fitting]
    exact hLay.rad_odd
  exact hodd.of_dvd_nat hdvd

end CFSG.QuasithinUnique.Setup.Family
