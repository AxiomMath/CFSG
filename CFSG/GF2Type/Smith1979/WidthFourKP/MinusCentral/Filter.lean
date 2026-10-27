module

public import CFSG.Assembly.CatalogTransport
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4MinusC

open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3 CFSG.Assembly.LowTwoRank
  CFSG.Blueprint

@[expose] def FilterW4MinusInCatalog : Prop :=
  ∀ {X : Type} [Group X] [IsSimpleGroup X], CFSG.Assembly.InCatalog X →
    (∃ a b : X, a * b ≠ b * a) → Nat.card X ∣ 348364800 → 5 ∣ Nat.card X →
    2 ^ 4 ∣ Nat.card X → ¬ 2 ^ 6 ∣ Nat.card X → False

@[expose] def orthPlus8Primes : List (ℕ × ℕ) := [(2, 13), (3, 5), (5, 2), (7, 1)]

@[expose] def filterCheckW4 (t : StatedLieTag) (n p f o : ℕ) : Bool :=
  decide (5 ∣ o → 2 ^ 4 ∣ o → ¬ 2 ^ 6 ∣ o → t = .PSp ∧ n = 2 ∧ p = 2 ∧ f = 1)

theorem primes_orthPlus8 : ∀ p : ℕ, p.Prime → p ∣ 348364800 →
    ∃ e, (p, e) ∈ orthPlus8Primes ∧ ¬ p ^ (e + 1) ∣ 348364800 := by
  refine primes_of_factorization ?_ (by decide +kernel) (by decide +kernel)
  simp only [orthPlus8Primes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq]
  norm_num

theorem lieSearch_w4 : lieSearchV orthPlus8Primes 348364800 filterCheckW4 = true := by
  decide +kernel

theorem filterW4_lieTuple {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ searchTags) (hp : p.Prime)
    (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hn0 : lieMin t = 0 → n = 0) (hnB : n ≤ lieExp t n + 1)
    (hadm : lieAdm t p f = true) (hord : lieOrd t n (p ^ f) ∣ 348364800)
    (h5 : 5 ∣ lieOrd t n (p ^ f)) (h1 : 2 ^ 4 ∣ lieOrd t n (p ^ f))
    (h2 : ¬ 2 ^ 6 ∣ lieOrd t n (p ^ f)) : t = .PSp ∧ n = 2 ∧ p = 2 ∧ f = 1 := by
  have hC := lieSearchV_sound primes_orthPlus8 lieSearch_w4 ht hp hf hn hn0 hnB hadm hord
  simp only [filterCheckW4, decide_eq_true_eq] at hC
  exact hC h5 h1 h2

theorem not_admissible_psp_two_two {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (h : t = .PSp ∧ n = 2 ∧ p = 2 ∧ f = 1) : False := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  exact absurd rfl hadm.2.2.2

theorem filterW4_alt {n : ℕ} (hn : 5 ≤ n) (hord : n.factorial / 2 ∣ 348364800)
    (h5 : 5 ∣ n.factorial / 2) (h1 : 2 ^ 4 ∣ n.factorial / 2) (h2 : ¬ 2 ^ 6 ∣ n.factorial / 2) :
    False := by
  have h13 : ¬ 13 ∣ 348364800 := by decide +kernel
  have hle : n ≤ 12 := le_twelve_of_factorial_div_two_dvd (by omega) h13 hord
  interval_cases n
  all_goals (revert hord h5 h1 h2; decide +kernel)

theorem filterW4_false_of_sporadic : ∀ s : TauCeti.SporadicName, s ≠ .Th → s ≠ .M →
    sporadicCard s ∣ 348364800 → 5 ∣ sporadicCard s → 2 ^ 4 ∣ sporadicCard s →
      ¬ 2 ^ 6 ∣ sporadicCard s → False := by
  decide +kernel

section FilterBinders

theorem filter_W4Minus {X : Type} [Group X] [IsSimpleGroup X] (hX : CFSG.Blueprint.Catalog X)
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hord : Nat.card X ∣ 348364800) (h5 : 5 ∣ Nat.card X)
    (h1 : 2 ^ 4 ∣ Nat.card X) (h2 : ¬ 2 ^ 6 ∣ Nat.card X) : False := by
  rcases catalog_model_cases hX hnonab with ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, p, f, ht, hp, hf, hn, hn0, hnB,
    hadm, hc, hm⟩ | ⟨p, f, h⟩ | ⟨p, f, h⟩ | ⟨s, ⟨e⟩⟩
  ·
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hc : Nat.card X = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rw [hc] at hord h5 h1 h2
    exact filterW4_alt hn5 hord h5 h1 h2
  ·
    rw [hc] at hord h5 h1 h2
    exact not_admissible_psp_two_two (LieModel.admissible hm)
      (filterW4_lieTuple ht hp hf hn hn0 hnB hadm hord h5 h1 h2)
  ·
    exact absurd ((thirteen_dvd_card_of_reeTitsModel_twistedF4 h).trans hord) (by decide)
  ·
    exact absurd ((thirteen_dvd_card_of_reeTitsModel_Tits h).trans hord) (by decide)
  ·
    obtain ⟨hTh, hM, hc⟩ := sporadic_cases e hord (by decide +kernel) (by decide +kernel)
    rw [hc] at hord h5 h1 h2
    exact filterW4_false_of_sporadic s hTh hM hord h5 h1 h2

theorem filter_W4Minus_of_inCatalog
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Assembly.InCatalog CFSG.Blueprint.Catalog)
    {X : Type} [Group X] [IsSimpleGroup X] (hX : CFSG.Assembly.InCatalog X)
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hord : Nat.card X ∣ 348364800) (h5 : 5 ∣ Nat.card X)
    (h1 : 2 ^ 4 ∣ Nat.card X) (h2 : ¬ 2 ^ 6 ∣ Nat.card X) : False := by
  have hfin : Finite X := Nat.finite_of_card_ne_zero (fun h0 => by
    rw [h0] at hord
    exact absurd (Nat.eq_zero_of_zero_dvd hord) (by norm_num))
  exact filter_W4Minus (hbridge X hnonab hX) hnonab hord h5 h1 h2

theorem filterW4MinusInCatalog_of_bridge
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Assembly.InCatalog CFSG.Blueprint.Catalog) :
    FilterW4MinusInCatalog :=
  fun hX hnonab hord h5 h1 h2 => filter_W4Minus_of_inCatalog hbridge hX hnonab hord h5 h1 h2

end FilterBinders

end CFSG.GF2Type.Smith1979.W4MinusC
