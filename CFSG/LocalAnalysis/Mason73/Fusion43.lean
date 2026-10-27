module

public import CFSG.LocalAnalysis.Mason73.Fusion42
public import CFSG.LocalAnalysis.Mason73.Model43

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem map_subtype_derivedSeries_zero (C : Subgroup G) :
    (derivedSeries C 0).map C.subtype = C := by
  rw [derivedSeries_zero, ← MonoidHom.range_eq_map, range_subtype]

theorem map_subtype_derivedSeries_succ (C : Subgroup G) (m : ℕ) :
    (derivedSeries C (m + 1)).map C.subtype =
      ⁅(derivedSeries C m).map C.subtype, (derivedSeries C m).map C.subtype⁆ := by
  rw [derivedSeries_succ, Subgroup.map_commutator]

theorem conj_mem_map_subtype_derivedSeries {C : Subgroup G} (m : ℕ) {c k : G} (hc : c ∈ C)
    (hk : k ∈ (derivedSeries C m).map C.subtype) :
    c * k * c⁻¹ ∈ (derivedSeries C m).map C.subtype := by
  obtain ⟨k', hk', rfl⟩ := hk
  exact ⟨⟨c, hc⟩ * k' * ⟨c, hc⟩⁻¹, (derivedSeries_normal C m).conj_mem _ hk' _, rfl⟩

theorem le_normalizer_map_subtype_derivedSeries (C : Subgroup G) (m : ℕ) :
    C ≤ normalizer (((derivedSeries C m).map C.subtype : Subgroup G) : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro k
  refine ⟨conj_mem_map_subtype_derivedSeries m hc, fun hk => ?_⟩
  have := conj_mem_map_subtype_derivedSeries m (inv_mem hc) hk
  convert this using 1
  group

theorem mem_commutator_of_mem_T1T [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S) {g : L4Model n}
    (hg : g ∈ T1T (n := n) (by omega)) :
    ι g ∈
      ⁅centralizer {ι (zT (n := n) (by omega))}, centralizer {ι (zT (n := n) (by omega))}⁆ := by
  have hC := range_le_centralizer_zT (by omega) ι
  have hu := uT_mem_commutator_centralizer hn hι S hS
  have hgV : g ∈ Q1T n := hg.1
  have hgp : xParity (n := n) (by omega) g = 1 := hg.2
  have hu' : ∀ σ : Fin81.R0, piT g = σ → (s23⁻¹ * σ = 1 ∨ s23⁻¹ * σ = zP) →
      ι g ∈
        ⁅centralizer {ι (zT (n := n) (by omega))}, centralizer {ι (zT (n := n) (by omega))}⁆ := by
    intro σ hσ hσ'
    have hc := mem_commutator_of_xParity hn (g := (uT (n := n) (by omega))⁻¹ * g)
      (by rw [map_mul, map_inv, xParity_uT, hgp]; exact (mul_one _).trans inv_one)
      (by rw [map_mul, map_inv, piT_uT, hσ]; exact hσ')
    have := mul_mem hu (map_mem_commutator hC hc)
    rwa [map_mul, map_inv, mul_inv_cancel_left] at this
  rcases piT_cases_of_mem_Q1T hgV with h | h | h | h
  · exact map_mem_commutator hC (mem_commutator_of_xParity hn hgp (Or.inl h))
  · exact hu' _ h (Or.inr (by decide))
  · exact hu' _ h (Or.inl (by decide))
  · exact map_mem_commutator hC (mem_commutator_of_xParity hn hgp (Or.inr h))

theorem mem_T1T_of_mem_commutator [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S) {g : L4Model n}
    (hg : ι g ∈
      ⁅centralizer {ι (zT (n := n) (by omega))}, centralizer {ι (zT (n := n) (by omega))}⁆) :
    g ∈ T1T (n := n) (by omega) := by
  have hS' : IsSylowOf 2 ι.range ⊤ := by
    rw [hS]
    exact GHarris.isSylowOf_top S
  have key : ∀ a : L4Model n, a⁻¹ * g ∈ T1T (n := n) (by omega) →
      ι a ∈
        ⁅centralizer {ι (zT (n := n) (by omega))}, centralizer {ι (zT (n := n) (by omega))}⁆ := by
    intro a ha
    have := mul_mem hg (inv_mem (mem_commutator_of_mem_T1T hn hι S hS ha))
    rwa [map_mul, map_inv, mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
  rcases mem_T1T_or hn g with h | h | h | h
  · exact h
  · exact absurd (key _ h) (lemma42 hn hι S hS)
  · exact absurd (key _ h) (lemma34 hn hι hS')
  · exact absurd (key _ h) (lemma34_txT hn hι hS')

theorem lemma43_one [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S) (g : L4Model n) :
    ι g ∈ ⁅centralizer {ι (zT (n := n) (by omega))}, centralizer {ι (zT (n := n) (by omega))}⁆ ↔
      g ∈ T1T (n := n) (by omega) :=
  ⟨mem_T1T_of_mem_commutator hn hι S hS, mem_commutator_of_mem_T1T hn hι S hS⟩

theorem isSylowOf_map_of_mem_iff (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hS : IsSylowOf 2 ι.range ⊤) {D : Subgroup G}
    (hD : D ≤ centralizer {ι (zT (n := n) (by omega))})
    (hDn : centralizer {ι (zT (n := n) (by omega))} ≤ normalizer (D : Set G))
    {R : Subgroup (L4Model n)} (hR : ∀ g, ι g ∈ D ↔ g ∈ R) : IsSylowOf 2 (R.map ι) D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (isSylowOf_zT hn hS).inf_of_le_normalizer hD hDn
  convert h using 1
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨⟨g, rfl⟩, range_le_centralizer_zT (by omega) ι ⟨g, rfl⟩⟩, (hR g).2 hg⟩
  · rintro ⟨⟨⟨g, rfl⟩, -⟩, hx⟩
    exact ⟨g, (hR g).1 hx, rfl⟩

theorem exists_conj_zT_of_mem_T2T [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S)
    (hu : ∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (zT (by omega))) {b : L4Model n}
    (hb : b ∈ T2T (n := n) (by omega)) (h1 : b ≠ 1) (h2 : b * b = 1) :
    ∃ g : G, g * ι b * g⁻¹ = ι (zT (by omega)) := by
  obtain ⟨⟨g₁, hg₁⟩, -, hzP, -⟩ := fusionPattern hn hι S hS
  obtain ⟨g₀, hg₀⟩ := hu
  have hnot : ∀ c : L4Model n, c ∉ T2T (n := n) (by omega) → ¬ IsConj b c := by
    intro c hc hbc
    obtain ⟨x, rfl⟩ := isConj_iff.1 hbc
    exact hc (T2T_normal _ x hb)
  rcases isConj_rep hn h1 h2 with h | h | h | h | h | h | h | h | h
  · exact exists_conj_of_isConj h (g := 1) (by rw [one_mul, inv_one, mul_one])
  · exact exists_conj_of_isConj h hg₁
  · exact absurd h (hnot _ (w1T_not_mem_T2T hn))
  · exact exists_conj_of_isConj h hg₀
  · exact absurd h (hnot _ (uw1T_not_mem_T2T hn))
  · obtain ⟨g, hg⟩ := hzP _ (uvT_mul_self (by omega)) (piT_uvT _)
    exact exists_conj_of_isConj h hg
  · obtain ⟨g, hg⟩ := hzP _ (uvxyT_mul_self (by omega)) rfl
    exact exists_conj_of_isConj h hg
  · exact absurd h (hnot _ (tT_not_mem_T2T (by omega)))
  · exact absurd h (hnot _ (txT_not_mem_T2T (by omega)))

theorem w1T_not_mem_commutator_commutator [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S)
    (hu : ∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (zT (by omega))) :
    ι (w1T hn) ∉
      ⁅⁅centralizer {ι (zT (n := n) (by omega))}, centralizer {ι (zT (n := n) (by omega))}⁆,
        ⁅centralizer {ι (zT (n := n) (by omega))}, centralizer {ι (zT (n := n) (by omega))}⁆⁆ := by
  have hS' : IsSylowOf 2 ι.range ⊤ := by
    rw [hS]
    exact GHarris.isSylowOf_top S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer {ι (zT (n := n) (by omega))} with hCdef
  have hw := (fusionPattern hn hι S hS).2.2.2.2.2
  have hsyl : IsSylowOf 2 ((T1T (n := n) (by omega)).map ι) ⁅C, C⁆ := by
    refine isSylowOf_map_of_mem_iff hn hS' (commutator_le_self C) ?_ (lemma43_one hn hι S hS)
    have h := le_normalizer_map_subtype_derivedSeries C 1
    rwa [derivedSeries_one, map_subtype_commutator] at h
  have hindex : Nat.Coprime 2 (((T1T (n := n) (by omega)).map ι).relIndex ⁅C, C⁆) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (isSylowOf_iff.1 hsyl).2.2
  refine CFSG.Quasithin.generalized_thompson_transfer_two_subgroup
    (K := (T2T (n := n) (by omega)).map ι) hsyl.le hindex (map_mono (T2T_le_T1T hn)) ?_ ?_
    ⟨_, w1T_mem_T1T hn, rfl⟩ ?_ ?_ ?_
  · rintro _ ⟨a, -, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b * a⁻¹, T2T_normal _ a hb, by rw [map_mul, map_mul, map_inv]⟩
  · rw [← map_commutator]
    exact map_mono (commutator_T1T_le_T2T hn)
  · rintro ⟨b, hb, hbw⟩
    exact w1T_not_mem_T2T hn (hι hbw ▸ hb)
  · rw [orderOf_injective ι hι]
    exact orderOf_eq_prime (by rw [pow_two, w1T_mul_self hn]) (w1T_ne_one hn)
  · rintro a - ⟨b, hbT, hbeq⟩
    have hconj : a⁻¹ * ι (w1T hn) * a⁻¹⁻¹ = ι b := by rw [inv_inv, hbeq]
    have hb2 := mul_self_of_conj_eq hι (w1T_mul_self hn) hconj
    have hb1 := ne_one_of_conj_eq hι (w1T_ne_one hn) hconj
    rcases mem_T2T_or_of_mul_self hn hbT.1 hb2 with h | h
    · exfalso
      obtain ⟨g, hg⟩ := exists_conj_zT_of_mem_T2T hn hι S hS hu h hb1 hb2
      obtain ⟨g', hg'⟩ := exists_conj_trans hconj hg
      exact hw g' hg'
    · exact ⟨_, h, by rw [map_mul, map_inv, hbeq]⟩

theorem T2T_le_comap_derivedSeries [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S)
    (hu : ∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (zT (by omega))) (m : ℕ) :
    T2T (n := n) (by omega) ≤ ((derivedSeries (centralizer {ι (zT (n := n) (by omega))}) m).map
      (centralizer {ι (zT (n := n) (by omega))}).subtype).comap ι := by
  have hS' : IsSylowOf 2 ι.range ⊤ := by
    rw [hS]
    exact GHarris.isSylowOf_top S
  set C := centralizer {ι (zT (n := n) (by omega))} with hCdef
  have hC : ι.range ≤ C := range_le_centralizer_zT (by omega) ι
  obtain ⟨hzx, -⟩ := fusionPattern hn hι S hS
  obtain ⟨g₀, hg₀⟩ := hu
  obtain ⟨h, hh, hux⟩ := lemma41_uT hn hι hS' hzx hg₀
  induction m with
  | zero =>
    intro g _
    change ι g ∈ (derivedSeries C 0).map C.subtype
    rw [map_subtype_derivedSeries_zero]
    exact hC ⟨g, rfl⟩
  | succ m ih =>
    set D := (derivedSeries C (m + 1)).map C.subtype with hDdef
    have hconj : ∀ c ∈ C, ∀ k ∈ D, c * k * c⁻¹ ∈ D := fun c hc k hk =>
      conj_mem_map_subtype_derivedSeries (m + 1) hc hk
    have hTconj : ∀ c k : L4Model n, ι k ∈ D → ι (c * k * c⁻¹) ∈ D := fun c k hk => by
      rw [map_mul, map_mul, map_inv]
      exact hconj _ (hC ⟨c, rfl⟩) _ hk
    have hx1 : ι (x1T (n := n) (by omega)) ∈ D := by
      have hle : (⁅T2T (n := n) (by omega), T2T (n := n) (by omega)⁆).map ι ≤ D := by
        rw [hDdef, map_subtype_derivedSeries_succ, map_commutator]
        exact commutator_mono (map_le_iff_le_comap.2 ih) (map_le_iff_le_comap.2 ih)
      exact hle ⟨_, x1T_mem_commutator_T2T hn, rfl⟩
    have huD : ι (uT (n := n) (by omega)) ∈ D := by
      have : ι (uT (n := n) (by omega)) = h⁻¹ * ι (x1T (by omega)) * h⁻¹⁻¹ := by
        rw [← hux]
        group
      rw [this]
      exact hconj _ (inv_mem hh) _ hx1
    have hvD : ι (vT (n := n) (by omega)) ∈ D := by
      have := hTconj (tT (by omega)) _ huD
      rwa [tT_inv (by omega), tT_mul_uT_mul_tT (by omega)] at this
    have hurD : ι (uT (n := n) (by omega) * r2T n) ∈ D := by
      obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_uT_mul_r2T (n := n) hn).symm
      have := hTconj c _ huD
      rwa [hc] at this
    have hvrD : ι (vT (n := n) (by omega) * r1T n) ∈ D := by
      have := hTconj (tT (by omega)) _ hurD
      rwa [tT_conj_uT_mul_r2T (by omega)] at this
    have hr2 : ι (r2T n) ∈ D := by
      have := mul_mem (inv_mem huD) hurD
      rwa [map_mul, inv_mul_cancel_left] at this
    have hr1 : ι (r1T n) ∈ D := by
      have := mul_mem (inv_mem hvD) hvrD
      rwa [map_mul, inv_mul_cancel_left] at this
    refine (T2T_le_closure hn).trans ((closure_le _).2 ?_)
    rintro _ (rfl | rfl | rfl | rfl)
    · exact huD
    · exact hvD
    · exact hr1
    · exact hr2

theorem lemma43 [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S)
    (hu : ∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (zT (by omega))) {m : ℕ} (hm : 2 ≤ m)
    (g : L4Model n) :
    ι g ∈ (derivedSeries (centralizer {ι (zT (n := n) (by omega))}) m).map
        (centralizer {ι (zT (n := n) (by omega))}).subtype ↔
      g ∈ T2T (n := n) (by omega) := by
  set C := centralizer {ι (zT (n := n) (by omega))} with hCdef
  have h2 : (derivedSeries C 2).map C.subtype = ⁅⁅C, C⁆, ⁅C, C⁆⁆ := by
    rw [map_subtype_derivedSeries_succ, map_subtype_derivedSeries_succ,
      map_subtype_derivedSeries_zero]
  refine ⟨fun hg => ?_, fun hg => T2T_le_comap_derivedSeries hn hι S hS hu m hg⟩
  have hg2 : ι g ∈ (derivedSeries C 2).map C.subtype :=
    map_mono (derivedSeries_antitone C hm) hg
  have hgT1 : g ∈ T1T (n := n) (by omega) := by
    refine mem_T1T_of_mem_commutator hn hι S hS (commutator_le_self _ ?_)
    rw [← h2]
    exact hg2
  by_contra hgT2
  obtain ⟨k, hk⟩ := exists_pow_mem_w1T_coset hn hgT1.1 hgT2
  have hkD := T2T_le_comap_derivedSeries hn hι S hS hu 2 hk
  have hw : ι (w1T hn) ∈ (derivedSeries C 2).map C.subtype := by
    have := mul_mem (pow_mem hg2 k) (inv_mem hkD)
    rwa [map_mul, map_inv, map_pow, mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
  rw [h2] at hw
  exact w1T_not_mem_commutator_commutator hn hι S hS hu hw

theorem isSylowOf_T2T [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S)
    (hu : ∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (zT (by omega))) {m : ℕ} (hm : 2 ≤ m) :
    IsSylowOf 2 ((T2T (n := n) (by omega)).map ι)
      ((derivedSeries (centralizer {ι (zT (n := n) (by omega))}) m).map
        (centralizer {ι (zT (n := n) (by omega))}).subtype) := by
  have hS' : IsSylowOf 2 ι.range ⊤ := by
    rw [hS]
    exact GHarris.isSylowOf_top S
  exact isSylowOf_map_of_mem_iff hn hS' (map_subtype_le _)
    (le_normalizer_map_subtype_derivedSeries _ m) (lemma43 hn hι S hS hu hm)

end CFSG.LocalAnalysis.Mason73
