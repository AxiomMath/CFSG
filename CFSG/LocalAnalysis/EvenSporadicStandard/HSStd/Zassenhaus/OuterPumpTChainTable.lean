module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTType
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpExcludeE
public import CFSG.Sporadic.HN
public import CFSG.Sporadic.HS

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HSStd

theorem factorial_ne_of_between {a n c : ℕ} (h1 : a.factorial < c) (h2 : c < (a + 1).factorial) :
    n.factorial ≠ c := by
  intro h
  rcases le_or_gt n a with hn | hn
  · have := Nat.factorial_le hn
    omega
  · have := Nat.factorial_le (show a + 1 ≤ n by omega)
    omega

theorem card_eq_of_alt_equiv {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n)
    (e : Nonempty (S ≃* alternatingGroup (Fin n))) : Nat.card S = n.factorial / 2 := by
  obtain ⟨e⟩ := e
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin]

theorem not_alt_of_card {S : Type} [Group S] {n a c : ℕ} (hn : 2 ≤ n) (hc : Nat.card S = c)
    (h1 : a.factorial < 2 * c) (h2 : 2 * c < (a + 1).factorial) :
    ¬ Nonempty (S ≃* alternatingGroup (Fin n)) := by
  intro e
  have h := card_eq_of_alt_equiv hn e
  rw [hc] at h
  have h2n : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  exact factorial_ne_of_between (n := n) h1 h2 (by omega)

theorem alt_degree_unique {S : Type} [Group S] {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (ea : Nonempty (S ≃* alternatingGroup (Fin a))) (eb : Nonempty (S ≃* alternatingGroup (Fin b))) :
    a = b := by
  have h := (card_eq_of_alt_equiv ha ea).symm.trans (card_eq_of_alt_equiv hb eb)
  have h2a : 2 ∣ a.factorial := Nat.dvd_factorial (by norm_num) ha
  have h2b : 2 ∣ b.factorial := Nat.dvd_factorial (by norm_num) hb
  exact (Nat.factorial_inj (by omega : 1 < a)).1 (by omega)

theorem card_of_hs {S : Type} [Group S] (h : IsSporadic S .HS) : Nat.card S = 44352000 := by
  obtain ⟨e⟩ := h
  exact (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS

theorem card_of_mcl {S : Type} [Group S] (h : IsSporadic S .McL) :
    Nat.card S = 898128000 := by
  obtain ⟨e⟩ := h
  exact (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.McL.card_McL

theorem card_of_hn {S : Type} [Group S] (h : IsSporadic S .HN) :
    Nat.card S = 273030912000000 := by
  obtain ⟨e⟩ := h
  exact (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HN.card_HN

theorem not_alt_of_hs {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n) (h : IsSporadic S .HS) :
    ¬ Nonempty (S ≃* alternatingGroup (Fin n)) :=
  not_alt_of_card (a := 11) hn (card_of_hs h) (by norm_num [Nat.factorial])
    (by norm_num [Nat.factorial])

theorem not_alt_of_mcl {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n)
    (h : IsSporadic S .McL) : ¬ Nonempty (S ≃* alternatingGroup (Fin n)) :=
  not_alt_of_card (a := 12) hn (card_of_mcl h) (by norm_num [Nat.factorial])
    (by norm_num [Nat.factorial])

theorem not_alt_of_hn {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n)
    (h : IsSporadic S .HN) : ¬ Nonempty (S ≃* alternatingGroup (Fin n)) :=
  not_alt_of_card (a := 17) hn (card_of_hn h) (by norm_num [Nat.factorial])
    (by norm_num [Nat.factorial])

theorem not_hs_of_hn {S : Type} [Group S] (h : IsSporadic S .HN) :
    ¬ IsSporadic S .HS := by
  intro hs
  have := (card_of_hn h).symm.trans (card_of_hs hs)
  norm_num at this

theorem two_pow_twelve_dvd_card_lieModel_T {Y : Type} [Group Y] {i : ℕ} (hi : 1 ≤ i)
    (h : LieModel Y .PSL 4 2 (2 ^ i)) : 2 ^ 12 ∣ Nat.card Y := by
  rw [card_psl_four Nat.one_le_two_pow h]
  have h2 : 2 ≤ 2 ^ i := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  refine Dvd.dvd.mul_right ?_ _
  rw [← pow_mul]
  exact pow_dvd_pow 2 (by omega)

theorem not_alt_of_lieModel_psl_four {Y : Type} [Group Y] {i n : ℕ} (hi : 1 ≤ i) (hn : 2 ≤ n)
    (hnd : ¬ 2 ^ 12 ∣ n.factorial / 2) (h : LieModel Y .PSL 4 2 (2 ^ i)) :
    ¬ Nonempty (Y ≃* alternatingGroup (Fin n)) := fun e => by
  have := two_pow_twelve_dvd_card_lieModel_T hi h
  rw [card_eq_of_alt_equiv hn e] at this
  exact hnd this

theorem not_hs_of_lieModel_psl_four {Y : Type} [Group Y] {i : ℕ} (hi : 1 ≤ i)
    (h : LieModel Y .PSL 4 2 (2 ^ i)) : ¬ IsSporadic Y .HS := fun hs => by
  have := two_pow_twelve_dvd_card_lieModel_T hi h
  rw [card_of_hs hs] at this
  norm_num at this

theorem kgPumpTable_of_T
    (hT : KGPumpTableT) : KGPumpTable := by
  intro S _ _ hcat hsimple τ hτ2 hτ1 N hN hNq hsub hZ hpump
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hT S hcat hsimple τ hτ2 hτ1 N hN hNq hsub hZ
  rcases hpump with ⟨k, hk, hQ⟩ | hHS | hMcL | hHN | ⟨i, hi, hL⟩
  · rcases (by omega : k = 4 ∨ 5 ≤ k) with rfl | hk5
    · have hA8 : Nonempty (↥N ⧸ center ↥N ≃* alternatingGroup (Fin 8)) := hQ
      rcases h1 hA8 with ⟨m, hm, hS⟩ | hS | hS | ⟨hS, -⟩
      · refine ⟨Or.inl ⟨m, by omega, hS⟩, fun e => ?_, fun _ => hA8⟩
        have := alt_degree_unique (by omega) (by omega) hS e
        omega
      · exact ⟨Or.inr (Or.inl hS), not_alt_of_hs (by norm_num) hS, fun _ => hA8⟩
      · refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨1, le_rfl, by simpa using hS⟩))),
          not_alt_of_lieModel_psl_four (i := 1) (n := 8) le_rfl (by norm_num)
            (by norm_num [Nat.factorial]) (by simpa using hS), fun _ => hA8⟩
      · exact ⟨Or.inr (Or.inr (Or.inl hS)), not_alt_of_mcl (by norm_num) hS, fun _ => hA8⟩
    · rcases h2 k hk5 hQ with ⟨m, hm, hS⟩ | ⟨rfl, hS⟩
      · refine ⟨Or.inl ⟨m, by omega, hS⟩, fun e => ?_, fun hs => ?_⟩
        · have := alt_degree_unique (by omega) (by omega) hS e
          omega
        · exact absurd hS (not_alt_of_hs (by omega) hs)
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl hS))), not_alt_of_hn (by norm_num) hS,
          fun hs => absurd hs (not_hs_of_hn hS)⟩
  · obtain ⟨hS, -⟩ := h3 hHS
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl hS))), not_alt_of_hn (by norm_num) hS,
      fun hs => absurd hs (not_hs_of_hn hS)⟩
  · exact absurd hMcL h4
  · exact absurd hHN h5
  · have hS := h6 i hi hL
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨i + 1, by omega, hS⟩))),
      not_alt_of_lieModel_psl_four (i := i + 1) (n := 8) (by omega) (by norm_num)
        (by norm_num [Nat.factorial]) hS,
      fun hs => absurd hs (not_hs_of_lieModel_psl_four (i := i + 1) (by omega) hS)⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
