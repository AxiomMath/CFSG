module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.Alternating.Multipliers.Small

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.RankThree.PerfectCover (hopfMultiplier hopfMultiplierToKer_surjective)
open CFSG.Alternating.Multipliers
  (hopfMultiplier_alternatingGroup_six hopfMultiplier_alternatingGroup_seven)

theorem ivAlt_card_center_dvd {Y X : Type} [Group Y] [Group X] (hY : Group.IsPerfect Y)
    (e : Y ⧸ Subgroup.center Y ≃* X) :
    Nat.card (Subgroup.center Y) ∣ Nat.card (hopfMultiplier X) := by
  haveI := hY
  have hsurj : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))).ker =
      Subgroup.center Y := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' _ x) = 1 ↔ x ∈ Subgroup.center Y
    rw [e.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h := Subgroup.card_dvd_of_surjective (hopfMultiplierToKer_surjective _ hsurj hker.le)
  rwa [hker] at h

theorem altSixSevenCentre_holds : AltSixSevenCentre := by
  unfold AltSixSevenCentre
  intro n hn Y _ _ hY hne
  obtain ⟨e⟩ := hne
  have hd := ivAlt_card_center_dvd (Group.isPerfect_def.2 hY) e
  rcases hn with rfl | rfl
  · rwa [hopfMultiplier_alternatingGroup_six.2] at hd
  · rwa [hopfMultiplier_alternatingGroup_seven.2] at hd

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
