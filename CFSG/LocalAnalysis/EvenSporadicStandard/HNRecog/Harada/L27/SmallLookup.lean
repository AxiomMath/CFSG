module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GSmall
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3 CFSG.Assembly.LowTwoRank
  CFSG.Blueprint

@[expose] def lookupPrimes : List (ℕ × ℕ) := [(2, 13), (3, 5), (5, 2), (7, 1)]

@[expose] def lookupBad : List (StatedLieTag × ℕ × ℕ × ℕ) :=
  [(.PSL, 2, 2, 1), (.PSL, 2, 3, 1), (.PSU, 3, 2, 1), (.PSp, 2, 2, 1), (.G2, 0, 2, 1)]

@[expose] def lookupCheck (t : StatedLieTag) (n p f o : ℕ) : Bool :=
  decide (o ≤ 16200 → o ∈ smallSimpleOrders) || lookupBad.contains (t, n, p, f)

theorem primes_lookup : ∀ p : ℕ, p.Prime → p ∣ 348364800 →
    ∃ e, (p, e) ∈ lookupPrimes ∧ ¬ p ^ (e + 1) ∣ 348364800 := by
  refine primes_of_factorization ?_ (by decide +kernel) (by decide +kernel)
  simp only [lookupPrimes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq]
  norm_num

theorem lieSearch_smallLookup : lieSearchV lookupPrimes 348364800 lookupCheck = true := by
  decide +kernel

theorem lookup_lieTuple {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ searchTags) (hp : p.Prime)
    (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hn0 : lieMin t = 0 → n = 0) (hnB : n ≤ lieExp t n + 1)
    (hadm : lieAdm t p f = true) (hord : lieOrd t n (p ^ f) ∣ 348364800)
    (hle : lieOrd t n (p ^ f) ≤ 16200) :
    lieOrd t n (p ^ f) ∈ smallSimpleOrders ∨ (t, n, p, f) ∈ lookupBad := by
  have hC := lieSearchV_sound primes_lookup lieSearch_smallLookup ht hp hf hn hn0 hnB hadm hord
  simp only [lookupCheck, Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hC
  rcases hC with hC | hC
  · exact Or.inl (hC hle)
  · exact Or.inr hC

theorem lookup_alt {n : ℕ} (hn : 5 ≤ n) (hord : n.factorial / 2 ∣ 348364800)
    (hle : n.factorial / 2 ≤ 16200) : n.factorial / 2 ∈ smallSimpleOrders := by
  have h13 : ¬ 13 ∣ 348364800 := by decide +kernel
  have h12 : n ≤ 12 := le_twelve_of_factorial_div_two_dvd (by omega) h13 hord
  interval_cases n
  all_goals first
    | decide +kernel
    | (exfalso; revert hord hle; decide +kernel)

theorem lookup_false_of_sporadic : ∀ s : TauCeti.SporadicName, s ≠ .Th → s ≠ .M →
    sporadicCard s ∣ 348364800 → sporadicCard s ≤ 16200 → False := by
  decide +kernel

theorem not_admissible_of_mem_lookupBad {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (hmem : (t, n, p, f) ∈ lookupBad) : False := by
  simp only [lookupBad, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact absurd rfl hadm.2.2.2.1
  · exact absurd rfl hadm.2.2.2.2
  · exact absurd rfl hadm.2.2.2
  · exact absurd rfl hadm.2.2.2
  · exact absurd hadm.2.2.2 (by norm_num)

theorem smallSimpleLookup_of_certificates : SmallSimpleLookup := by
  intro T _ _ _ hT hnonab hdvd hle
  rcases catalog_model_cases hT hnonab with ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, p, f, ht, hp, hf, hn, hn0,
    hnB, hadm, hc, hm⟩ | ⟨p, f, h⟩ | ⟨p, f, h⟩ | ⟨s, ⟨e⟩⟩
  ·
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hc : Nat.card T = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rw [hc] at hdvd hle ⊢
    exact lookup_alt hn5 hdvd hle
  ·
    rw [hc] at hdvd hle ⊢
    rcases lookup_lieTuple ht hp hf hn hn0 hnB hadm hdvd hle with h | h
    · exact h
    · exact (not_admissible_of_mem_lookupBad (LieModel.admissible hm) h).elim
  ·
    exact absurd ((thirteen_dvd_card_of_reeTitsModel_twistedF4 h).trans hdvd) (by decide)
  ·
    exact absurd ((thirteen_dvd_card_of_reeTitsModel_Tits h).trans hdvd) (by decide)
  ·
    obtain ⟨hTh, hM, hc⟩ := sporadic_cases e hdvd (by decide +kernel) (by decide +kernel)
    rw [hc] at hdvd hle
    exact (lookup_false_of_sporadic s hTh hM hdvd hle).elim

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
