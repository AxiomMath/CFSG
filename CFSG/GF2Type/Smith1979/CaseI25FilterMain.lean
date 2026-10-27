module

public import CFSG.GF2Type.Smith1979.CaseI25Filter
public import CFSG.Assembly.CatalogTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case25

open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3 CFSG.Assembly.LowTwoRank
  CFSG.Blueprint

theorem filter_X {X : Type} [Group X] [IsSimpleGroup X] (hX : CFSG.Blueprint.Catalog X)
    (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hord : Nat.card X ∣ 2 ^ 31 * 3 ^ 8 * 5 ^ 2 * 7 ^ 2 * 11 * 17 * 31)
    (h1 : 25920 ∣ Nat.card X) (h2 : 2 ^ 7 ∣ Nat.card X) (h3 : ¬ 2 ^ 9 ∣ Nat.card X) :
    Nonempty (X ≃* alternatingGroup (Fin 10)) ∨ Nonempty (X ≃* alternatingGroup (Fin 11)) ∨
      CFSG.Open.StatedClassicalModel X .PSU 4 3 1 := by
  rcases catalog_model_cases hX hnonab with ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, p, f, ht, hp, hf, hn, hn0, hnB,
    hadm, hc, hm⟩ | ⟨p, f, h⟩ | ⟨p, f, h⟩ | ⟨s, ⟨e⟩⟩
  ·
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hc : Nat.card X = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rw [hc] at hord h1 h2 h3
    rcases filterX_alt hn5 hord h1 h2 h3 with rfl | rfl
    · exact Or.inl ⟨e⟩
    · exact Or.inr (Or.inl ⟨e⟩)
  ·
    rw [hc] at hord h1 h2 h3
    obtain ⟨rfl, rfl, rfl, rfl⟩ := filterX_lieTuple ht hp hf hn hn0 hnB hadm hord h1 h2 h3
    exact Or.inr (Or.inr (LieModel.statedClassicalModel_of_ne_zero (by norm_num) hm))
  ·
    exact (false_of_reeTitsModel_twistedF4 h hord filterX_not_two_pow_sixtySeven_dvd
      filterX_not_thirtySeven_dvd filterX_not_fortyOne_dvd).elim
  ·
    exact (filterX_not_dvd_titsOrd (h1.trans (card_dvd_of_reeTitsModel_Tits h))).elim
  ·
    obtain ⟨hTh, hM, hc⟩ := sporadic_cases e hord filterX_not_nineteen_dvd
      filterX_not_twentyNine_dvd
    rw [hc] at hord h1 h2 h3
    exact (filterX_false_of_sporadic s hTh hM hord h1 h2 h3).elim

theorem filter_X_of_inCatalog
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Assembly.InCatalog CFSG.Blueprint.Catalog)
    {X : Type} [Group X] [IsSimpleGroup X] (hX : CFSG.Assembly.InCatalog X)
    (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hord : Nat.card X ∣ 2 ^ 31 * 3 ^ 8 * 5 ^ 2 * 7 ^ 2 * 11 * 17 * 31)
    (h1 : 25920 ∣ Nat.card X) (h2 : 2 ^ 7 ∣ Nat.card X) (h3 : ¬ 2 ^ 9 ∣ Nat.card X) :
    Nonempty (X ≃* alternatingGroup (Fin 10)) ∨ Nonempty (X ≃* alternatingGroup (Fin 11)) ∨
      CFSG.Open.StatedClassicalModel X .PSU 4 3 1 := by
  have hfin : Finite X := Nat.finite_of_card_ne_zero (fun h0 => by
    rw [h0] at hord
    exact absurd (Nat.eq_zero_of_zero_dvd hord) (by norm_num))
  exact filter_X (hbridge X hnonab hX) hnonab hord h1 h2 h3

end CFSG.GF2Type.Smith1979.Case25
