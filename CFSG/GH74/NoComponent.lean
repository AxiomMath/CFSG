module

public import CFSG.GH74.Assembly
public import CFSG.GH74.Bender
public import CFSG.GH74.EvenRank
public import CFSG.Milestones.CLS_component_dichotomy
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.GH74

open Blueprint

theorem catalog_of_lieModel {X : Type} [Group X] {t : Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (h : LieModel X t n p f) : Catalog X := by
  rcases h with ⟨-, h⟩ | ⟨-, ht, h⟩ | ⟨-, ht, h⟩ | ⟨-, -, h⟩
  · exact Or.inr (Or.inr (Or.inl ⟨t, n, p, f, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨t, p, f, ht, h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨t, p, f, ht, h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨p, f, h⟩)))))

theorem catalog_of_isSporadic {X : Type} [Group X] {s : TauCeti.SporadicName}
    (h : NativeSporadic.IsSporadic X s) : Catalog X :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨s, h⟩)))

theorem catalog_of_ghList {X : Type} [Group X] (h : GHList X) : Catalog X := by
  rcases h with ⟨n, hn, -, he⟩ | hs | ⟨p, f, -, -, h⟩
  · exact Or.inr (Or.inl ⟨n, by omega, he⟩)
  · rcases hs with h | h | h | h | h | h | h | h | h <;> exact catalog_of_isSporadic h
  · rcases h with ⟨-, h | h | h | h | h | h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | h |
        ⟨-, h | h | h | h | h⟩ <;>
      exact catalog_of_lieModel h

theorem kProper_of_kgh {G : Type} [Group G] (h : KGH G) : Assembly.KProper Catalog G := by
  intro K L hK _ _ hsimple hnonab
  exact catalog_of_ghList (h K hK (L.subgroupOf K) inferInstance hsimple hnonab)

@[expose] def S_QTKE_Gen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G → Assembly.Quasithin.quasithinEvenCharacteristic G →
      Assembly.evenRank G ≤ 2 → Catalog G

theorem quasithinEvenCharacteristic_of_isCharTwoType {G : Type} [Group G]
    (h : Assembly.IsCharTwoType G) : Assembly.Quasithin.quasithinEvenCharacteristic G :=
  Assembly.Quasithin.quasithinEvenCharacteristic_of_isCharTwoType h

@[expose] def S_filter : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Catalog G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → GH74Conclusion G

theorem noComponent_of_qtke
    (hQ : S_QTKE_Gen4) (hF : S_filter) : S_noComponent := by
  intro G _ _ hsimple hnonab hrank hgen hkgh hlayer
  by_cases hpre : (Assembly.involutionGraph G).Preconnected
  · obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := G) 2
      (even_iff_two_dvd.mp (even_card_of_three_le_twoRank hrank))
    have : Nonempty {t : G // orderOf t = 2} := ⟨⟨t, ht⟩⟩
    rcases Milestones.cls_component_dichotomy G hnonab hrank ⟨hpre⟩ with hcomp | hchar
    · exact absurd hcomp (not_isComponentType_of_layerBar_eq_bot hlayer)
    · exact hF G (hQ G inferInstance hnonab hrank hgen hkgh
        (quasithinEvenCharacteristic_of_isCharTwoType hchar)
        (evenRank_le_two_of_charTwoType_gen4 hchar hgen)) hnonab hrank hgen
  · exact gh74Conclusion_of_disconnected hpre hrank hgen

end CFSG.GH74
