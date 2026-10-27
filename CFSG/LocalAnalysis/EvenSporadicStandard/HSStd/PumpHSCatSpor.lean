module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersSporadic
public import CFSG.LocalAnalysis.SectionRank.Monster

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSmallLie.CatalogOrders
  CFSG.SectionRank

theorem eightyone_dvd_card_of_mulEquiv_M {T : Type} [Group T] [Finite T] [Nontrivial T]
    (e : T ≃* NativeSporadic.M) : 81 ∣ Nat.card T := by
  have : Nontrivial NativeSporadic.M := e.injective.nontrivial
  have : Finite NativeSporadic.M := Finite.of_equiv _ e.toEquiv
  obtain ⟨E, -, hcard⟩ := M_nontrivial_elementary_three_rank_four
  have h := Subgroup.card_subgroup_dvd_card E
  rw [hcard, ← Nat.card_congr e.toEquiv] at h
  simpa using h


theorem eq_HS_of_card_carrier
    {s : TauCeti.SporadicName} (h : Nat.card (NativeSporadic.Carrier s) = 44352000) :
    s = .HS := by
  cases s
  case M11 => exact absurd (CFSG.Sporadic.Mathieu.card_M11.symm.trans h) (by norm_num)
  case M12 => exact absurd (CFSG.Sporadic.Mathieu.card_M12.symm.trans h) (by norm_num)
  case M22 => exact absurd (CFSG.Sporadic.Mathieu.card_M22.symm.trans h) (by norm_num)
  case M23 => exact absurd (card_M23.symm.trans h) (by norm_num)
  case M24 => exact absurd (CFSG.Sporadic.Mathieu.card_M24.symm.trans h) (by norm_num)
  case J1 => exact absurd (CFSG.Sporadic.J1.card_J1.symm.trans h) (by norm_num)
  case J2 => exact absurd (CFSG.Sporadic.J2.card_J2.symm.trans h) (by norm_num)
  case J3 => exact absurd (CFSG.Sporadic.J3.card_J3.symm.trans h) (by norm_num)
  case J4 => exact absurd (CFSG.Sporadic.J4.card_J4.symm.trans h) (by norm_num)
  case HS => rfl
  case McL => exact absurd (CFSG.Sporadic.McL.card_McL.symm.trans h) (by norm_num)
  case He => exact absurd (CFSG.Sporadic.He.fam_he_order.1.symm.trans h) (by norm_num)
  case Ru => exact absurd (CFSG.Sporadic.Ru.card_Ru.symm.trans h) (by norm_num)
  case Suz => exact absurd (CFSG.Sporadic.Suz.card_Suz.symm.trans h) (by norm_num)
  case ONan => exact absurd (CFSG.Sporadic.ON.card_ON.symm.trans h) (by norm_num)
  case Co1 => exact absurd (CFSG.Sporadic.Co1.card_Co1.symm.trans h) (by norm_num)
  case Co2 => exact absurd (CFSG.Sporadic.Co2.card_Co2.symm.trans h) (by norm_num)
  case Co3 => exact absurd (CFSG.Sporadic.Co3.card_Co3.symm.trans h) (by norm_num)
  case Fi22 => exact absurd (CFSG.Sporadic.Fi22.card_Fi22.symm.trans h) (by norm_num)
  case Fi23 => exact absurd (CFSG.Sporadic.Fi23.card_Fi23.symm.trans h) (by norm_num)
  case Fi24Prime =>
    exact absurd (CFSG.Sporadic.Fi24.card_Fi24prime.symm.trans h) (by norm_num)
  case HN => exact absurd (CFSG.Sporadic.HN.card_HN.symm.trans h) (by norm_num)
  case Ly => exact absurd (CFSG.Sporadic.Ly.card_Ly.symm.trans h) (by norm_num)
  case Th =>
    have h19 := nineteen_dvd_card_Th
    rw [show Nat.card NativeSporadic.Th = 44352000 from h] at h19
    exact absurd h19 (by norm_num)
  case B =>
    exact absurd (CFSG.Monster.Existence.card_nativeB.symm.trans h)
      (by unfold CFSG.Open.monsterBabyOrder; norm_num)
  case M =>
    have h' : Nat.card NativeSporadic.M = 44352000 := h
    have : Finite NativeSporadic.M := Nat.finite_of_card_ne_zero (by rw [h']; norm_num)
    have : Nontrivial NativeSporadic.M :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [h']; norm_num)
    have h81 := eightyone_dvd_card_of_mulEquiv_M (T := NativeSporadic.M) (MulEquiv.refl _)
    rw [h'] at h81
    exact absurd h81 (by norm_num)

end CFSG.EvenSporadicStandard.HSStd.PumpHS
