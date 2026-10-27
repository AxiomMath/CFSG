module

public import CFSG.GF2Type.Smith1979.CaseIIFilter
public import CFSG.Assembly.CatalogTransport
import CFSG.GH74.Exceptional.LinearFourTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3 CFSG.Assembly.LowTwoRank
  CFSG.Blueprint

section FilterBinders

theorem filter_II {X : Type} [Group X] [IsSimpleGroup X] (hX : CFSG.Blueprint.Catalog X)
    (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hord : Nat.card X ∣ 2 ^ 31 * 3 ^ 8 * 5 ^ 2 * 7 ^ 2 * 11 * 17 * 31)
    (h1 : 1344 ∣ Nat.card X) (h2 : ¬ 2 ^ 11 ∣ Nat.card X) :
    (∃ n : ℕ, 8 ≤ n ∧ n ≤ 12 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      CFSG.Open.StatedClassicalModel X .PSL 3 2 2 ∨
      CFSG.Open.StatedClassicalModel X .PSL 5 2 1 ∨
      CFSG.Open.StatedClassicalModel X .PSp 3 2 1 ∨
      CFSG.Open.StatedClassicalModel X .PSU 4 3 1 ∨
      Nonempty (X ≃* NativeSporadic.Carrier .J2) ∨
      Nonempty (X ≃* NativeSporadic.Carrier .M22) := by
  rcases catalog_model_cases hX hnonab with ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, p, f, ht, hp, hf, hn, hn0, hnB,
    hadm, hc, hm⟩ | ⟨p, f, h⟩ | ⟨p, f, h⟩ | ⟨s, ⟨e⟩⟩
  ·
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hc : Nat.card X = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rw [hc] at hord h1 h2
    obtain ⟨h8, h12⟩ := filterII_alt hn5 hord h1 h2
    exact Or.inl ⟨n, h8, h12, ⟨e⟩⟩
  ·
    rw [hc] at hord h1 h2
    have hmem := filterII_lieTuple ht hp hf hn hn0 hnB hadm hord h1 h2
    simp only [lieTuplesII, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    ·
      exact Or.inr (Or.inl (LieModel.statedClassicalModel_of_ne_zero (by norm_num) hm))
    ·
      obtain ⟨e⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hm
      exact Or.inl ⟨8, le_rfl, by norm_num, ⟨e⟩⟩
    ·
      exact Or.inr (Or.inr (Or.inl (LieModel.statedClassicalModel_of_ne_zero (by norm_num) hm)))
    ·
      exact Or.inr (Or.inr (Or.inr (Or.inl
        (LieModel.statedClassicalModel_of_ne_zero (by norm_num) hm))))
    ·
      obtain ⟨-, -, -, h2'⟩ := LieModel.admissible hm
      exact absurd rfl h2'
    ·
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (LieModel.statedClassicalModel_of_ne_zero (by norm_num) hm)))))
    ·
      obtain ⟨-, -, -, h3⟩ := LieModel.admissible hm
      exact absurd h3 (by norm_num)
  ·
    exact (false_of_reeTitsModel_twistedF4 h hord Case25.filterX_not_two_pow_sixtySeven_dvd
      Case25.filterX_not_thirtySeven_dvd Case25.filterX_not_fortyOne_dvd).elim
  ·
    exact (filterII_not_dvd_titsOrd (h1.trans (card_dvd_of_reeTitsModel_Tits h))).elim
  ·
    obtain ⟨hTh, hM, hc⟩ := sporadic_cases e hord Case25.filterX_not_nineteen_dvd
      Case25.filterX_not_twentyNine_dvd
    rw [hc] at hord h1 h2
    rcases filterII_sporadic s hTh hM hord h1 h2 with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))))

theorem filter_II_of_inCatalog
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Assembly.InCatalog CFSG.Blueprint.Catalog)
    {X : Type} [Group X] [IsSimpleGroup X] (hX : CFSG.Assembly.InCatalog X)
    (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hord : Nat.card X ∣ 2 ^ 31 * 3 ^ 8 * 5 ^ 2 * 7 ^ 2 * 11 * 17 * 31)
    (h1 : 1344 ∣ Nat.card X) (h2 : ¬ 2 ^ 11 ∣ Nat.card X) :
    (∃ n : ℕ, 8 ≤ n ∧ n ≤ 12 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      CFSG.Open.StatedClassicalModel X .PSL 3 2 2 ∨
      CFSG.Open.StatedClassicalModel X .PSL 5 2 1 ∨
      CFSG.Open.StatedClassicalModel X .PSp 3 2 1 ∨
      CFSG.Open.StatedClassicalModel X .PSU 4 3 1 ∨
      Nonempty (X ≃* NativeSporadic.Carrier .J2) ∨
      Nonempty (X ≃* NativeSporadic.Carrier .M22) := by
  have hfin : Finite X := Nat.finite_of_card_ne_zero (fun h0 => by
    rw [h0] at hord
    exact absurd (Nat.eq_zero_of_zero_dvd hord) (by norm_num))
  exact filter_II (hbridge X hnonab hX) hnonab hord h1 h2

theorem filterIIInCatalog_of_bridge
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Assembly.InCatalog CFSG.Blueprint.Catalog) :
    ∀ {X : Type} [Group X] [IsSimpleGroup X], CFSG.Assembly.InCatalog X →
      (∃ a b : X, a * b ≠ b * a) →
      Nat.card X ∣ 2 ^ 31 * 3 ^ 8 * 5 ^ 2 * 7 ^ 2 * 11 * 17 * 31 → 1344 ∣ Nat.card X →
      ¬ 2 ^ 11 ∣ Nat.card X →
        (∃ n : ℕ, 8 ≤ n ∧ n ≤ 12 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
          CFSG.Open.StatedClassicalModel X .PSL 3 2 2 ∨
          CFSG.Open.StatedClassicalModel X .PSL 5 2 1 ∨
          CFSG.Open.StatedClassicalModel X .PSp 3 2 1 ∨
          CFSG.Open.StatedClassicalModel X .PSU 4 3 1 ∨
          Nonempty (X ≃* NativeSporadic.Carrier .J2) ∨
          Nonempty (X ≃* NativeSporadic.Carrier .M22) :=
  fun hX hnonab hord h1 h2 => filter_II_of_inCatalog hbridge hX hnonab hord h1 h2

end FilterBinders

end CFSG.GF2Type.Smith1979.Case2
