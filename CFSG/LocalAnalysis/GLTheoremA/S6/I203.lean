module

public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt73

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I203Aux

variable {n : ℕ}

open Classical in
noncomputable def orb (H : Subgroup (Equiv.Perm (Fin n))) (w : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun y => ∃ f ∈ H, f w = y)

theorem mem_orb {H : Subgroup (Equiv.Perm (Fin n))} {w y : Fin n} :
    y ∈ orb H w ↔ ∃ f ∈ H, f w = y := by
  simp [orb]

theorem self_mem_orb (H : Subgroup (Equiv.Perm (Fin n))) (w : Fin n) : w ∈ orb H w :=
  mem_orb.2 ⟨1, H.one_mem, rfl⟩

theorem orb_eq_of_mem (H : Subgroup (Equiv.Perm (Fin n))) {w y : Fin n} (hy : y ∈ orb H w) :
    orb H y = orb H w := by
  obtain ⟨g, hg, rfl⟩ := mem_orb.1 hy
  ext z
  simp only [mem_orb]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f * g, H.mul_mem hf hg, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f * g⁻¹, H.mul_mem hf (H.inv_mem hg), by simp⟩

theorem card_orb_dvd (H : Subgroup (Equiv.Perm (Fin n))) (w : Fin n) :
    (orb H w).card ∣ Nat.card H := by
  have hset : MulAction.orbit H w = ((orb H w : Finset (Fin n)) : Set (Fin n)) := by
    ext y
    simp only [MulAction.mem_orbit_iff, Finset.mem_coe, mem_orb]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, g.2, hg⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
  have h1 : (MulAction.stabilizer (↥H) w).index = (orb H w).card := by
    rw [MulAction.index_stabilizer, hset, Set.ncard_coe_finset]
  rw [← h1]
  exact Subgroup.index_dvd_card (H := MulAction.stabilizer (↥H) w)

theorem card_orb_prime_pow {p k : ℕ} (hp : p.Prime) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : Nat.card H = p ^ k) (w : Fin n) : ∃ a, (orb H w).card = p ^ a := by
  have h := card_orb_dvd H w
  rw [hH] at h
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).1 h
  exact ⟨a, ha⟩

theorem orb_conj (H E : Subgroup (Equiv.Perm (Fin n)))
    (hN : ∀ f ∈ E, ∀ u ∈ H, f * u * f⁻¹ ∈ H) {f : Equiv.Perm (Fin n)} (hf : f ∈ E) (w : Fin n) :
    orb H (f w) = (orb H w).image f := by
  ext z
  constructor
  · intro hz
    obtain ⟨u, hu, rfl⟩ := mem_orb.1 hz
    have hconj : f⁻¹ * u * f ∈ H := by
      have := hN f⁻¹ (E.inv_mem hf) u hu
      simpa using this
    rw [Finset.mem_image]
    refine ⟨(f⁻¹ * u * f) w, mem_orb.2 ⟨f⁻¹ * u * f, hconj, rfl⟩, ?_⟩
    simp
  · intro hz
    rw [Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨u, hu, rfl⟩ := mem_orb.1 hy
    exact mem_orb.2 ⟨f * u * f⁻¹, hN f hf u hu, by simp⟩

theorem card_orb_conj (H E : Subgroup (Equiv.Perm (Fin n)))
    (hN : ∀ f ∈ E, ∀ u ∈ H, f * u * f⁻¹ ∈ H) {f : Equiv.Perm (Fin n)} (hf : f ∈ E) (w : Fin n) :
    (orb H (f w)).card = (orb H w).card := by
  rw [orb_conj H E hN hf w, Finset.card_image_of_injective _ f.injective]

theorem dvd_card_of_blocks (d : ℕ) (B : Fin n → Finset (Fin n)) :
    ∀ X : Finset (Fin n), (∀ w ∈ X, w ∈ B w) → (∀ w ∈ X, B w ⊆ X) →
      (∀ w ∈ X, ∀ v ∈ B w, B v = B w) → (∀ w ∈ X, d ∣ (B w).card) → d ∣ X.card := by
  intro X
  induction X using Finset.strongInduction with
  | H X ih =>
    intro hself hsub heq hdvd
    rcases X.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
    · simp
    · have hBsub : B w ⊆ X := hsub w hw
      have hYss : X \ B w ⊂ X :=
        (Finset.ssubset_iff_of_subset Finset.sdiff_subset).2
          ⟨w, hw, fun h => (Finset.mem_sdiff.1 h).2 (hself w hw)⟩
      have hcard : (X \ B w).card + (B w).card = X.card :=
        Finset.card_sdiff_add_card_eq_card hBsub
      have hYdvd : d ∣ (X \ B w).card := by
        refine ih (X \ B w) hYss ?_ ?_ ?_ ?_
        · intro v hv
          exact hself v (Finset.mem_sdiff.1 hv).1
        · intro v hv z hz
          rw [Finset.mem_sdiff]
          refine ⟨hsub v (Finset.mem_sdiff.1 hv).1 hz, fun hzw => (Finset.mem_sdiff.1 hv).2 ?_⟩
          have hvB : B v = B w :=
            (heq v (Finset.mem_sdiff.1 hv).1 z hz).symm.trans (heq w hw z hzw)
          rw [← hvB]
          exact hself v (Finset.mem_sdiff.1 hv).1
        · intro v hv
          exact heq v (Finset.mem_sdiff.1 hv).1
        · intro v hv
          exact hdvd v (Finset.mem_sdiff.1 hv).1
      rw [← hcard]
      exact dvd_add hYdvd (hdvd w hw)

theorem succ_le_pow {p : ℕ} (hp : 2 ≤ p) (c : ℕ) : c + 1 ≤ p ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_left (p ^ c) hp]

theorem mul_le_pow_of_three {p : ℕ} (hp : 3 ≤ p) (b : ℕ) : p * b ≤ p ^ b := by
  cases b with
  | zero => simp
  | succ c =>
    have h1 : c + 1 ≤ p ^ c := succ_le_pow (by omega) c
    rw [pow_succ, mul_comm (p ^ c) p]
    exact Nat.mul_le_mul_left p h1

theorem mul_lt_pow_of_two_le {p : ℕ} (hp : 3 ≤ p) (b : ℕ) (hb : 2 ≤ b) : p * b < p ^ b := by
  induction b, hb using Nat.le_induction with
  | base => nlinarith [Nat.mul_le_mul_left p hp]
  | succ b hb ih =>
    rw [pow_succ]
    have h1 : p * b + 1 ≤ p ^ b := ih
    nlinarith [Nat.mul_le_mul_right p h1, Nat.mul_le_mul_left (p * b) hp,
      Nat.mul_pos (show 0 < p by omega) (show 0 < b by omega)]

theorem eq_one_of_pow_eq_mul {p b : ℕ} (hp : 3 ≤ p) (h : p ^ b = p * b) : b = 1 := by
  by_contra hb
  rcases Nat.lt_or_ge b 2 with h2 | h2
  · interval_cases b
    · simp at h
    · exact hb rfl
  · have := mul_lt_pow_of_two_le hp b h2
    linarith

theorem orbit_structure {p k : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hn : n = p * k)
    (E : Subgroup (Equiv.Perm (Fin n))) (hEc : ∀ f ∈ E, ∀ g ∈ E, f * g = g * f)
    (hEcard : Nat.card E = p ^ k) :
    (∀ w : Fin n, (orb E w).card = p) ∧
      ∀ v w : Fin n, w ∉ orb E v → ∀ z ∈ orb E v, ∃ f ∈ E, f v = z ∧ f w = w := by
  classical
  haveI : Fintype E := Fintype.ofFinite _
  have hmin : ∀ w : Fin n, ∃ m, m ∈ orb E w ∧ ∀ v ∈ orb E w, m ≤ v := fun w =>
    ⟨(orb E w).min' ⟨w, self_mem_orb E w⟩, Finset.min'_mem _ _,
      fun v hv => Finset.min'_le _ _ hv⟩
  obtain ⟨R, hRmem⟩ : ∃ R : Finset (Fin n), ∀ r, r ∈ R ↔ ∀ v ∈ orb E r, r ≤ v :=
    ⟨Finset.univ.filter (fun r => ∀ v ∈ orb E r, r ≤ v), fun r => by simp⟩
  have hR1 : ∀ w, ∃ r ∈ R, w ∈ orb E r := by
    intro w
    obtain ⟨m, hmw, hmin'⟩ := hmin w
    refine ⟨m, (hRmem m).2 ?_, ?_⟩
    · intro v hv
      rw [orb_eq_of_mem E hmw] at hv
      exact hmin' v hv
    · rw [orb_eq_of_mem E hmw]
      exact self_mem_orb E w
  have hR2 : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → s ∉ orb E r := by
    intro r hr s hs hne hsr
    have h1 : orb E s = orb E r := orb_eq_of_mem E hsr
    have hrs : r ∈ orb E s := by
      rw [h1]
      exact self_mem_orb E r
    exact hne (le_antisymm ((hRmem r).1 hr s hsr) ((hRmem s).1 hs r hrs))
  have hdisj : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (orb E r) (orb E s) := by
    intro r hr s hs hne
    rw [Finset.disjoint_left]
    intro z hzr hzs
    have h3 : orb E s = orb E r := (orb_eq_of_mem E hzs).symm.trans (orb_eq_of_mem E hzr)
    apply hR2 r hr s hs hne
    rw [← h3]
    exact self_mem_orb E s
  have hpd : (R : Set (Fin n)).PairwiseDisjoint (orb E) := by
    intro r hr s hs hne
    exact hdisj r hr s hs hne
  have hcover : R.biUnion (orb E) = Finset.univ := by
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    obtain ⟨r, hr, hw⟩ := hR1 w
    exact ⟨r, hr, hw⟩
  have hsum : ∑ r ∈ R, (orb E r).card = n := by
    rw [← Finset.card_biUnion hpd, hcover]
    simp
  have hexp : ∀ w : Fin n, ∃ a, (orb E w).card = p ^ a := fun w =>
    card_orb_prime_pow hp E hEcard w
  choose a ha using hexp
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : E → ((r : R) → ↥(orb E r.1)),
      ∀ (f : E) (r : R), ((Φ f r : ↥(orb E r.1)) : Fin n) = (f : Equiv.Perm (Fin n)) r.1 :=
    ⟨fun f r => ⟨(f : Equiv.Perm (Fin n)) r.1, mem_orb.2 ⟨f, f.2, rfl⟩⟩, fun _ _ => rfl⟩
  have hinj : Function.Injective Φ := by
    intro f g hfg
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨r, hr, hx⟩ := hR1 x
    obtain ⟨k', hk', rfl⟩ := mem_orb.1 hx
    have hfr : (f : Equiv.Perm (Fin n)) r = (g : Equiv.Perm (Fin n)) r := by
      have h1 : ((Φ f ⟨r, hr⟩ : ↥(orb E r)) : Fin n) = ((Φ g ⟨r, hr⟩ : ↥(orb E r)) : Fin n) := by
        rw [hfg]
      rw [hΦ, hΦ] at h1
      exact h1
    have hcf := hEc (f : Equiv.Perm (Fin n)) f.2 k' hk'
    have hcg := hEc (g : Equiv.Perm (Fin n)) g.2 k' hk'
    have ef : (f : Equiv.Perm (Fin n)) (k' r) = k' ((f : Equiv.Perm (Fin n)) r) := by
      have := congrArg (fun σ : Equiv.Perm (Fin n) => σ r) hcf
      simpa [Equiv.Perm.mul_apply] using this
    have eg : (g : Equiv.Perm (Fin n)) (k' r) = k' ((g : Equiv.Perm (Fin n)) r) := by
      have := congrArg (fun σ : Equiv.Perm (Fin n) => σ r) hcg
      simpa [Equiv.Perm.mul_apply] using this
    rw [ef, eg, hfr]
  have hEcardF : Fintype.card E = p ^ k := by
    rw [← Nat.card_eq_fintype_card]
    exact hEcard
  have hprodpow : ∏ r : R, (orb E r.1).card = p ^ ∑ r ∈ R, a r := by
    have h1 : ∏ r : R, (orb E r.1).card = ∏ r ∈ R, (orb E r).card :=
      Finset.prod_coe_sort R (fun r => (orb E r).card)
    rw [h1]
    simp only [ha]
    exact Finset.prod_pow_eq_pow_sum R a p
  have hk_le : k ≤ ∑ r ∈ R, a r := by
    have h1 := Fintype.card_le_of_injective Φ hinj
    rw [Fintype.card_pi, hEcardF] at h1
    have h2 : ∏ r : R, Fintype.card ↥(orb E r.1) = ∏ r : R, (orb E r.1).card := by
      simp [Fintype.card_coe]
    rw [h2, hprodpow] at h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  have hterm : ∀ r ∈ R, p * a r ≤ p ^ a r := fun r _ => mul_le_pow_of_three hp3 (a r)
  have hsumpow : ∑ r ∈ R, p ^ a r = n :=
    (Finset.sum_congr rfl (fun r _ => (ha r).symm)).trans hsum
  have hle2 : ∑ r ∈ R, p * a r ≤ ∑ r ∈ R, p ^ a r := Finset.sum_le_sum hterm
  have heq : ∑ r ∈ R, p * a r = ∑ r ∈ R, p ^ a r := by
    apply le_antisymm hle2
    rw [hsumpow, ← Finset.mul_sum]
    exact hn.trans_le (Nat.mul_le_mul_left p hk_le)
  have hterm_eq : ∀ r ∈ R, p * a r = p ^ a r := (Finset.sum_eq_sum_iff_of_le hterm).1 heq
  have ha1 : ∀ r ∈ R, a r = 1 := fun r hr => eq_one_of_pow_eq_mul hp3 (hterm_eq r hr).symm
  have h0 : ∀ r ∈ R, (orb E r).card = p := fun r hr => by
    rw [ha r, ha1 r hr, pow_one]
  have hRcard : R.card = k := by
    have h1 : ∑ r ∈ R, (orb E r).card = R.card * p := by
      rw [Finset.sum_congr rfl h0]
      simp [Finset.sum_const, mul_comm]
    have h2 : R.card * p = k * p := by
      calc R.card * p = ∑ r ∈ R, (orb E r).card := h1.symm
        _ = n := hsum
        _ = p * k := hn
        _ = k * p := mul_comm p k
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  have hcardeq : Fintype.card E = Fintype.card ((r : R) → ↥(orb E r.1)) := by
    rw [Fintype.card_pi, hEcardF]
    have h3 : ∀ r : R, Fintype.card ↥(orb E r.1) = p := fun r => by
      rw [Fintype.card_coe, h0 r.1 r.2]
    simp only [h3]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, hRcard]
  have hsurj : Function.Surjective Φ :=
    ((Fintype.bijective_iff_injective_and_card Φ).2 ⟨hinj, hcardeq⟩).2
  have hall : ∀ w : Fin n, (orb E w).card = p := by
    intro w
    obtain ⟨r, hr, hwr⟩ := hR1 w
    rw [orb_eq_of_mem E hwr]
    exact h0 r hr
  refine ⟨hall, fun v w hw z hz => ?_⟩
  obtain ⟨r, hr, hv⟩ := hR1 v
  obtain ⟨s, hs, hws⟩ := hR1 w
  obtain ⟨g, hg, hgr⟩ := mem_orb.1 hv
  obtain ⟨q, hq, hqs⟩ := mem_orb.1 hws
  obtain ⟨k', hk', hkv⟩ := mem_orb.1 hz
  have hrs : r ≠ s := by
    rintro rfl
    apply hw
    rw [orb_eq_of_mem E hv]
    exact hws
  have hcgk : ∀ x, (k' : Equiv.Perm (Fin n)) ((g : Equiv.Perm (Fin n)) x) = (g : Equiv.Perm (Fin n)) (k' x) := by
    intro x
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ x) (hEc (k' : Equiv.Perm (Fin n)) hk' (g : Equiv.Perm (Fin n)) hg)
    simpa [Equiv.Perm.mul_apply] using this
  have hginv : ∀ x, (g : Equiv.Perm (Fin n)) ((g : Equiv.Perm (Fin n))⁻¹ x) = x := fun x => by
    rw [Equiv.Perm.inv_def]
    exact Equiv.apply_symm_apply _ _
  have hginv' : ∀ x, (g : Equiv.Perm (Fin n))⁻¹ ((g : Equiv.Perm (Fin n)) x) = x := fun x => by
    rw [Equiv.Perm.inv_def]
    exact Equiv.symm_apply_apply _ _
  have hgz : (g : Equiv.Perm (Fin n))⁻¹ z ∈ orb E r := by
    rw [mem_orb]
    refine ⟨k', hk', ?_⟩
    rw [← hkv, ← hgr, hcgk, hginv']
  have hmem : ∀ t : R, (if t.1 = r then (g : Equiv.Perm (Fin n))⁻¹ z else t.1) ∈ orb E t.1 := by
    intro t
    by_cases ht : t.1 = r
    · rw [if_pos ht, ht]
      exact hgz
    · rw [if_neg ht]
      exact self_mem_orb E t.1
  obtain ⟨F, hF⟩ := hsurj (fun t => ⟨_, hmem t⟩)
  have hFval : ∀ t ∈ R, (F : Equiv.Perm (Fin n)) t = if t = r then (g : Equiv.Perm (Fin n))⁻¹ z else t := by
    intro t ht
    have h1 : ((Φ F ⟨t, ht⟩ : ↥(orb E t)) : Fin n) =
        (if t = r then (g : Equiv.Perm (Fin n))⁻¹ z else t) := by
      rw [hF]
    rw [hΦ] at h1
    exact h1
  have hcFg : ∀ x, (F : Equiv.Perm (Fin n)) ((g : Equiv.Perm (Fin n)) x) =
      (g : Equiv.Perm (Fin n)) ((F : Equiv.Perm (Fin n)) x) := by
    intro x
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ x)
      (hEc (F : Equiv.Perm (Fin n)) F.2 (g : Equiv.Perm (Fin n)) hg)
    simpa [Equiv.Perm.mul_apply] using this
  have hcFq : ∀ x, (F : Equiv.Perm (Fin n)) ((q : Equiv.Perm (Fin n)) x) =
      (q : Equiv.Perm (Fin n)) ((F : Equiv.Perm (Fin n)) x) := by
    intro x
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ x)
      (hEc (F : Equiv.Perm (Fin n)) F.2 (q : Equiv.Perm (Fin n)) hq)
    simpa [Equiv.Perm.mul_apply] using this
  refine ⟨(F : Equiv.Perm (Fin n)), F.2, ?_, ?_⟩
  · rw [← hgr, hcFg, hFval r hr, if_pos rfl, hginv]
  · rw [← hqs, hcFq, hFval s hs, if_neg (Ne.symm hrs)]

end I203Aux

open I203Aux

theorem i203_core {n p k : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hn : n = p * k)
    (E U : Subgroup (Equiv.Perm (Fin n))) (hEc : ∀ f ∈ E, ∀ g ∈ E, f * g = g * f)
    (hEcard : Nat.card E = p ^ k) (hUcard : ∃ m, Nat.card U = 2 ^ m)
    (hN : ∀ f ∈ E, ∀ u ∈ U, f * u * f⁻¹ ∈ U) :
    ∀ u ∈ U, ∀ x : Fin n, u x = x := by
  obtain ⟨hEorb, hB⟩ := orbit_structure hp hp3 hn E hEc hEcard
  obtain ⟨m, hm⟩ := hUcard
  have hUpow : ∀ w, ∃ a, (orb U w).card = 2 ^ a := fun w =>
    card_orb_prime_pow Nat.prime_two U hm w
  have hcm : ∀ f ∈ E, ∀ w z, z ∈ orb U w → f z ∈ orb U (f w) := by
    intro f hf w z hz
    rw [orb_conj U E hN hf w]
    exact Finset.mem_image_of_mem f hz
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
  intro u hu x
  have hcard1 : (orb U x).card ≤ 1 := by
    obtain ⟨a, ha⟩ := hUpow x
    by_cases hcase : ∃ y ∈ orb U x, y ∉ orb E x
    · exfalso
      obtain ⟨y, hyS, hyE⟩ := hcase
      have hxy : orb U y = orb U x := orb_eq_of_mem U hyS
      have C1 : ∀ z ∈ orb E x, z ∈ orb U x := by
        intro z hz
        obtain ⟨f, hf, hfx, hfy⟩ := hB x y hyE z hz
        have hx' : x ∈ orb U y := by
          rw [hxy]
          exact self_mem_orb U x
        have h1 := hcm f hf y x hx'
        rw [hfy, hxy] at h1
        rw [← hfx]
        exact h1
      have C2 : ∀ w ∈ orb U x, ∀ z ∈ orb E w, z ∈ orb U x := by
        intro w hw z hz
        by_cases hwE : w ∈ orb E x
        · rw [orb_eq_of_mem E hwE] at hz
          exact C1 z hz
        · have hxw : x ∉ orb E w := by
            intro hxw
            apply hwE
            rw [orb_eq_of_mem E hxw]
            exact self_mem_orb E w
          obtain ⟨f, hf, hfw, hfx⟩ := hB w x hxw z hz
          have h1 := hcm f hf x w hw
          rw [hfx] at h1
          rw [← hfw]
          exact h1
      have hdiv : p ∣ (orb U x).card :=
        dvd_card_of_blocks p (orb E) (orb U x)
          (fun w _ => self_mem_orb E w)
          (fun w hw => by
            intro z hz
            exact C2 w hw z hz)
          (fun w _ v hv => orb_eq_of_mem E hv)
          (fun w _ => by simp [hEorb w])
      rw [ha] at hdiv
      have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hdiv
      have hp2' : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2
      omega
    · push_neg at hcase
      have hblock : 2 ^ a ∣ (orb E x).card :=
        dvd_card_of_blocks (2 ^ a) (orb U) (orb E x)
          (fun w _ => self_mem_orb U w)
          (fun w hw => by
            intro z hz
            obtain ⟨f, hf, rfl⟩ := mem_orb.1 hw
            obtain ⟨v, hv, rfl⟩ := mem_orb.1 hz
            have hmem : f⁻¹ * v * f ∈ U := by
              have := hN f⁻¹ (E.inv_mem hf) v hv
              simpa using this
            obtain ⟨k', hk', hk''⟩ :=
              mem_orb.1 (hcase _ (mem_orb.2 ⟨f⁻¹ * v * f, hmem, rfl⟩))
            exact mem_orb.2 ⟨f * k', E.mul_mem hf hk', by rw [Equiv.Perm.mul_apply, hk'']; simp⟩)
          (fun w _ v hv => orb_eq_of_mem U hv)
          (fun w hw => by
            obtain ⟨f, hf, rfl⟩ := mem_orb.1 hw
            simp [card_orb_conj U E hN hf x, ha])
      rw [hEorb x] at hblock
      have h2a : 2 ^ a = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left a hcop) hblock
      simp [ha, h2a]
  have hux : u x ∈ orb U x := mem_orb.2 ⟨u, hu, rfl⟩
  exact Finset.card_le_one.1 hcard1 _ hux _ (self_mem_orb U x)

theorem i203At_holds : I203At := by
  unfold I203At
  intro p n hp hp2 hpn _ Q _ e E U hE hEcard hU hEN
  classical
  obtain ⟨hEcomm, -⟩ := hE
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hn : n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
  haveI : Finite Q := Finite.of_equiv _ e.symm.toEquiv
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hEcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let ρ : Q →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply e.injective
    apply Subtype.ext
    exact hab
  have hEc' : ∀ f ∈ E.map ρ, ∀ g ∈ E.map ρ, f * g = g * f := by
    intro f hf g hg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hf
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hg
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hEcard' : Nat.card (E.map ρ) = p ^ (n / p) := by
    rw [Subgroup.card_map_of_injective hρ]
    exact hEcard
  have hUcard : ∃ m, Nat.card (U.map ρ) = 2 ^ m := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hU
    exact ⟨m, by rw [Subgroup.card_map_of_injective hρ]; exact hm⟩
  have hN' : ∀ f ∈ E.map ρ, ∀ u ∈ U.map ρ, f * u * f⁻¹ ∈ U.map ρ := by
    intro f hf u hu
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hf
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hu
    refine Subgroup.mem_map.2 ⟨a * v * a⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hEN ha) v).1 hv
    · simp [map_mul, map_inv]
  have hcore := i203_core hp hp3 hn (E.map ρ) (U.map ρ) hEc' hEcard' hUcard hN'
  rw [Subgroup.eq_bot_iff_forall]
  intro v hv
  apply hρ
  rw [map_one]
  apply Equiv.ext
  intro x
  rw [Equiv.Perm.one_apply]
  exact hcore (ρ v) (Subgroup.mem_map_of_mem ρ hv) x

end CFSG.LocalAnalysis.GLTheoremA
