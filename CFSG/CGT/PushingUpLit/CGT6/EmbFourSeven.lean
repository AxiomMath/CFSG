module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAdm
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenPlus
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenSL
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.G18Minus

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit

@[expose] def FourSevenAlt : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Cfg G T Y → IsShortGroup ↥(yuHol Y) →
      (∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥(yuHol Y) m) →
      ∀ X : Subgroup (MulAut V), X ≤ G → ¬ 2 ∣ Nat.card X →
        Y ≤ Subgroup.normalizer (X : Set (MulAut V)) →
          X ≤ Subgroup.centralizer (Y : Set (MulAut V))

@[expose] def FourSevenL24 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Cfg G T Y → IsShortGroup ↥(yuHol Y) →
      IsNaturalSLTwoModule ↥(yuHol Y) 2 →
      ∀ X : Subgroup (MulAut V), X ≤ G → ¬ 2 ∣ Nat.card X →
        Y ≤ Subgroup.normalizer (X : Set (MulAut V)) →
          X ≤ Subgroup.centralizer (Y : Set (MulAut V))

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem emb_four_seven (hM4 : SchurMultL2Two) (hAlt : FourSevenAlt) (hL24 : FourSevenL24)
    (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)} (cfg : Emb4Cfg G T Y)
    {X : Subgroup (MulAut V)} (hXG : X ≤ G) (hX : ¬ 2 ∣ Nat.card X)
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut V))) :
    X ≤ Subgroup.centralizer (Y : Set (MulAut V)) := by
  have hperf : ⁅Y, Y⁆ = Y := cfg.adm.hperf
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  rcases cfg.adm.hcls with ⟨hshort, halt | ⟨m, hm, hsl⟩⟩ | ⟨n, hn, hY⟩ | ⟨n, hn, hY⟩
  · exact hAlt V hV G T Y cfg hshort halt X hXG hX hYX
  · have hm2 := two_le_of_isNaturalSLTwoModule hV hm hsl
    by_cases hm3 : 3 ≤ m
    · exact sl_oddInvariant_le_centralizer hM4 hV hperf hshort hm3 hsl hX hYX
    · have : m = 2 := by omega
      subst this
      exact hL24 V hV G T Y cfg hshort hsl X hXG hX hYX
  · exact omegaMinus_oddInvariant_le_centralizer hV hn hY hX hYX
  · exact omegaPlus_oddInvariant_le_centralizer hV hn hY hX hYX

end Main

end CFSG.CGT.PushingUpLit.CGT6
