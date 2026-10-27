module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Vacuous
public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Perf
public import CFSG.LieType.BorelTits.AllModels
public import CFSG.Quasithin.Background.C35InspSmall

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem twoLocalsSolvable_of_statedClassicalModel_psl_three_two {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 3 2 1) : TwoLocalsSolvable S := by
  haveI hsimple : IsSimpleGroup S :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h
  have hcard : Nat.card S = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h
  intro Q hQ hQ2
  by_cases htop : Subgroup.normalizer (Q : Set S) = ⊤
  · exfalso
    have hnormal : Q.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases (haveI := hnormal; hsimple.eq_bot_or_eq_top_of_normal Q) with hbot | hQtop
    · exact hQ hbot
    · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hQtop ▸ hQ2)
      have hn' : Nat.card S = 2 ^ n := by
        simpa only [Subgroup.card_top] using hn
      have h3 : 3 ∣ Nat.card S := by
        rw [hcard]
        norm_num
      rw [hn'] at h3
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      norm_num at h32
  · exact CFSG.Quasithin.J4Fam.solvable_of_ne_top_card168 hcard htop

theorem twoLocalsSolvable_of_reeTitsModel_tits
    {S : Type} [Group S] [Finite S] (h : ReeTitsModel S .Tits 2 1) : TwoLocalsSolvable S := by
  have hmodel : LieModel S .Tits 0 2 1 := Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩))
  intro Q hQ hQ2
  obtain ⟨T, P, hP, hN, -, -, -, hTP⟩ :=
    CFSG.LieType.BorelTits.lieModel_conclusion S .Tits 0 2 1 hmodel Q hQ hQ2
  have hTits : IsTits S := by
    rw [IsTits]
    exact h
  have hsolv : Group.IsSolvable ↥P :=
    CFSG.Quasithin.C35Pf.solvOver_of_isTits hTits (T : Subgroup S) P
      (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow T) (hTP rfl) hP
  haveI : Group.IsSolvable ↥P := hsolv
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hN)
    (Subgroup.inclusion_injective hN)

theorem for_L32 : For (fun S _ => StatedClassicalModel S .PSL 3 2 1) := by
  refine For.of_twoLocalsSolvable (fun S _ _ h => ?_)
  exact twoLocalsSolvable_of_statedClassicalModel_psl_three_two h

theorem for_Tits :
    For (fun S _ => ReeTitsModel S .Tits 2 1) := by
  refine For.of_twoLocalsSolvable (fun S _ _ h => ?_)
  exact twoLocalsSolvable_of_reeTitsModel_tits h

end CFSG.SectionRank.QTK.Insp443

end
