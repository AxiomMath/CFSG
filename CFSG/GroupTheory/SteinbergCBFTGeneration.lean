module

public import CFSG.GroupTheory.SteinbergCBFTPPrimePSeries
public import CFSG.GroupTheory.HallCunihin
public import CFSG.GroupTheory.SteinbergCBFTPSolvable

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup CFSG.HallHigman

section Generation

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

@[expose] def ftS (p : ℕ) (P : Subgroup G) : Set (Subgroup G) :=
  {H | P ≤ H ∧ pLength p H ≤ 2 ∧ (Nat.card H).primeFactors.card ≤ 2}

omit hp in
theorem mem_ftS_of {P H : Subgroup G} {q : ℕ} (hPH : P ≤ H) (hser : HasPSeries p H 5)
    (hpr : (Nat.card H).primeFactors ⊆ {p, q}) : H ∈ ftS p P :=
  ⟨hPH, pLength_le_of_hasPSeries hser, (Finset.card_le_card hpr).trans Finset.card_le_two⟩

theorem le_sSup_ftS_of_primeFactors_subset (hG : IsPiSeparable {r : Nat.Primes | r.val = p} G)
    (P : Sylow p G) {q : ℕ} (n : ℕ) :
    ∀ Y : Subgroup G, Nat.card Y = n → (P : Subgroup G) ≤ Y →
      (Nat.card Y).primeFactors ⊆ {p, q} → Y ≤ sSup (ftS p (P : Subgroup G)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hYn hPY hYpq
  have hYsep : IsPiSeparable {r : Nat.Primes | r.val = p} Y := hG.subgroup Y
  have hprimes : ∀ H : Subgroup G, H ≤ Y → (Nat.card H).primeFactors ⊆ {p, q} := fun H hH =>
    (Nat.primeFactors_mono (card_dvd_of_le hH) Nat.card_pos.ne').trans hYpq
  set PY : Sylow p Y := P.subtype hPY with hPYdef
  have hPYmap : (PY : Subgroup Y).map Y.subtype = P := by
    rw [hPYdef, Sylow.coe_subtype, subgroupOf_map_subtype, inf_eq_left.2 hPY]
  set K := (PY : Subgroup Y) ⊔ corePP' p Y with hKdef
  have hKmap : K.map Y.subtype ≤ sSup (ftS p (P : Subgroup G)) := by
    refine le_sSup (mem_ftS_of ?_ ((hasPSeries_sup_corePP' PY).of_mulEquiv
      (K.equivMapOfInjective _ Y.subtype_injective)) (hprimes _ (map_subtype_le _)))
    rw [← hPYmap]
    exact map_mono le_sup_left
  by_cases hKtop : K = ⊤
  · rw [hKtop, ← MonoidHom.range_eq_map, range_subtype] at hKmap
    exact hKmap
  · set L := normalizer (((PY : Subgroup Y) ⊓ corePP'P p Y : Subgroup Y) : Set Y) with hLdef
    have hT₃n : (corePP'P p Y).Normal := coreAbove_normal _ _
    have hLtop : L ≠ ⊤ := fun h =>
      hKtop (by rw [hKdef, corePP'_eq_top_of_normal hYsep PY h]; exact sup_top_eq _)
    have hPL : (PY : Subgroup Y) ≤ L :=
      le_normalizer_inf_of_le le_normalizer (fun x _ =>
        (normalizer_eq_top (H := corePP'P p Y)).symm ▸ mem_top x)
    have hLmap : L.map Y.subtype ≤ sSup (ftS p (P : Subgroup G)) := by
      refine ih _ ?_ _ rfl ?_ (hprimes _ (map_subtype_le _))
      · rw [card_map_of_injective Y.subtype_injective, ← hYn, ← card_top (G := Y)]
        exact card_lt_of_lt (lt_top_iff_ne_top.2 hLtop)
      · rw [← hPYmap]
        exact map_mono hPL
    have hY : Y = (corePP' p Y).map Y.subtype ⊔ L.map Y.subtype := by
      rw [← Subgroup.map_sup, corePP'_sup_normalizer PY, ← MonoidHom.range_eq_map, range_subtype]
    rw [hY]
    exact sup_le ((map_mono le_sup_right).trans hKmap) hLmap

theorem ft_lemma_7_6 (hG : IsPSolvable p G) (P : Sylow p G) :
    sSup (ftS p (P : Subgroup G)) = ⊤ := by
  have hsep := isPiSeparable_of_isPSolvable hp.out hG
  have hPX : (P : Subgroup G) ≤ sSup (ftS p (P : Subgroup G)) := by
    refine le_sSup (mem_ftS_of (q := p) le_rfl (hasPSeries_of_isPGroup P.isPGroup') ?_)
    intro r hr
    have hr' := Nat.prime_of_mem_primeFactors hr
    have := (Nat.prime_dvd_prime_iff_eq hr' hp.out).1
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    rw [Nat.mem_primeFactors, hk] at hr
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inl (this (hr'.dvd_of_dvd_pow hr.2.1))
  rw [← index_eq_one]
  by_contra hne
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne
  by_cases hrp : r = p
  · subst hrp
    exact P.not_dvd_index (hrdvd.trans (index_dvd_of_le hPX))
  · obtain ⟨Y, hY, hPY⟩ := (CFSG.HallHigman.hall_pq_subgroups_p_solvable hp.out hr hsep).2 P
    have hYle := le_sSup_ftS_of_primeFactors_subset hsep P (q := r) _ Y rfl hPY (by
      intro s hs
      have hs' := Nat.prime_of_mem_primeFactors hs
      rcases hY.p_in_pi_of_p_dvd_card ⟨s, hs'⟩ (Nat.dvd_of_mem_primeFactors hs) with h | h
      · rw [Finset.mem_insert]
        exact Or.inl h
      · rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr h)
    exact hY.p_in_pi_of_p_dvd_index ⟨r, hr⟩ (hrdvd.trans (index_dvd_of_le hYle)) (Or.inr rfl)

end Generation

end CFSG.GroupTheory.FT63ChII
