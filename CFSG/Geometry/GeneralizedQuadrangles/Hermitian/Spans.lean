module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.SpanSizes
public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.NoSpansTwo
public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.PropertyH
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Setting

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin CFSG.Quasithin.Stroth

variable {V : Type} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {H : Type} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

theorem dvd_of_ncard_lineSpan (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ L M : V, c L = 1 → Γ.dist L M = 4 → (spanSet Γ L M).ncard = s + 1) :
    s + 1 ∣ (t + 1) * (s * t + 1) * t ^ 2 := by
  classical
  let O : Finset (Σ _ : V, V) :=
    (lineFinset c).sigma fun L => Finset.univ.filter fun M => Γ.dist L M = 4
  have hinner : ∀ L ∈ lineFinset c,
      (Finset.univ.filter fun M => Γ.dist L M = 4).card = s * t ^ 2 := by
    intro L hL
    have hLc : c L = 1 := mem_lineFinset.mp hL
    have hL0 : dualColoring c L = 0 := by
      rw [dualColoring_apply, hLc]
      decide
    have hcard := card_opposite hP hT (dualColoring c) (s := t) (t := s)
      (degree_eq_of_dualColoring hdeg) (x := L) hL0
    rw [hcard]
    exact Nat.mul_comm (t ^ 2) s
  have hOcard : O.card = s * ((t + 1) * (s * t + 1) * t ^ 2) := by
    rw [Finset.card_sigma]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul,
      card_lineFinset hP hT c hdeg]
    ring
  let f : (Σ _ : V, V) → Finset V := fun p => (spanSet Γ p.1 p.2).toFinset
  have hfiber : ∀ N ∈ O.image f, (O.filter fun p => f p = N).card = (s + 1) * s := by
    intro N hN
    obtain ⟨p0, hp0O, hp0N⟩ := Finset.mem_image.mp hN
    have hp0O' := hp0O
    simp only [O, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp0O'
    obtain ⟨hp0line, hp0dist⟩ := hp0O'
    have hcL0 : c p0.1 = 1 := mem_lineFinset.mp hp0line
    have hdist0 : Γ.dist p0.1 p0.2 = 4 := hp0dist
    let S : Set V := spanSet Γ p0.1 p0.2
    have hN_eq : N = S.toFinset := by rw [← hp0N]
    have hScard : S.toFinset.card = s + 1 := by
      rw [← Set.ncard_eq_toFinset_card']
      exact hp p0.1 p0.2 hcL0 hdist0
    have hScolor : ∀ a ∈ S, c a = 1 := by
      intro a ha
      rw [color_eq_of_mem_span hP hT c hdist0 ha]
      exact hcL0
    have hfiber_eq : (O.filter fun p => f p = N) =
        S.toFinset.sigma fun a => S.toFinset.erase a := by
      rw [hN_eq]
      ext p
      obtain ⟨a, b⟩ := p
      simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_erase, Set.mem_toFinset]
      constructor
      · rintro ⟨hpO, hpf⟩
        have hpO' := hpO
        simp only [O, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hpO'
        have hb4 : Γ.dist a b = 4 := hpO'.2
        have hpf' : (spanSet Γ a b).toFinset = S.toFinset := hpf
        have haS : a ∈ S := by
          have h : a ∈ (spanSet Γ a b).toFinset := by
            rw [Set.mem_toFinset]
            exact left_mem_spanSet hb4
          rw [hpf'] at h
          simpa using h
        have hbS : b ∈ S := by
          have h : b ∈ (spanSet Γ a b).toFinset := by
            rw [Set.mem_toFinset]
            exact right_mem_spanSet hb4
          rw [hpf'] at h
          simpa using h
        exact ⟨haS, by intro h; rw [h] at hb4; exact absurd hb4 (by simp), hbS⟩
      · rintro ⟨haS, hba, hbS⟩
        have hne : a ≠ b := fun h => hba h.symm
        have h4 : Γ.dist a b = 4 :=
          dist_eq_four_of_mem_span hP hT hdist0 haS hbS hne
        have hspan : spanSet Γ a b = S :=
          (span_eq_of_mem hP hT hdist0 haS hbS hne).2.1
        refine ⟨?_, ?_⟩
        · simp only [O, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨mem_lineFinset.mpr (hScolor a haS), h4⟩
        · show (spanSet Γ a b).toFinset = S.toFinset
          rw [hspan]
    rw [hfiber_eq, Finset.card_sigma]
    have hterm : ∀ a ∈ S.toFinset, (S.toFinset.erase a).card = s := by
      intro a ha
      rw [Finset.card_erase_of_mem ha, hScard]
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hScard]
  have hOcard' : O.card = (O.image f).card * ((s + 1) * s) := by
    calc O.card = ∑ N ∈ O.image f, (O.filter fun p => f p = N).card :=
          Finset.card_eq_sum_card_image f O
      _ = ∑ _N ∈ O.image f, ((s + 1) * s) := Finset.sum_congr rfl hfiber
      _ = (O.image f).card * ((s + 1) * s) := by
          rw [Finset.sum_const, smul_eq_mul]
  have hs : 0 < s := by
    have h2 := two_le_s hP hT c hdeg
    omega
  have hEq : s * ((s + 1) * (O.image f).card) =
      s * ((t + 1) * (s * t + 1) * t ^ 2) := by
    calc s * ((s + 1) * (O.image f).card) = (O.image f).card * ((s + 1) * s) := by ring
      _ = O.card := hOcard'.symm
      _ = s * ((t + 1) * (s * t + 1) * t ^ 2) := hOcard
  exact ⟨(O.image f).card, (Nat.eq_of_mul_eq_mul_left hs hEq).symm⟩

private theorem two_le_q_of_hermitianOrder (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {q : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then q ^ 3 + 1 else q ^ 2 + 1) : 2 ≤ q := by
  have h2s : 2 ≤ q ^ 2 := two_le_s hP hT c hdeg
  rcases Nat.lt_or_ge q 2 with hq1 | hq2
  · interval_cases q <;> norm_num at h2s
  · exact hq2

theorem ncard_spanSet_of_hermitianOrder (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {q : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then q ^ 3 + 1 else q ^ 2 + 1)
    (hM : MoufangCondition H Γ 4) :
    (∀ x y, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = q + 1) ∧
      (∀ L M, c L = 1 → Γ.dist L M = 4 → (spanSet Γ L M).ncard = 2) := by
  classical
  have hq : 2 ≤ q := two_le_q_of_hermitianOrder hP hT c hdeg
  obtain ⟨⟨x, hx⟩⟩ := hP.exists_point (by norm_num : 2 ≤ 4) hT c
  obtain ⟨p, hp⟩ := exists_ncard_spanSet_eq hP hT hM c 0
  obtain ⟨p', hp'⟩ := exists_ncard_spanSet_eq hP hT hM c 1
  have hH : ∀ u : V, HasPropertyH Γ u := hasPropertyH hP hT hM
  have htri := trichotomy hP hT c (s := q ^ 2) (t := q ^ 3) hdeg
    (fun u _ => hH u) hp
  have htri' := trichotomy_dual hP hT c (s := q ^ 2) (t := q ^ 3) hdeg
    (fun u _ => hH u) hp'
  have hline : p' = 1 := by
    rcases htri' with hp's | hp'1 | ⟨hpt2, hps3⟩
    · exfalso
      have hpcount : ∀ L M : V, c L = 1 → Γ.dist L M = 4 →
          (spanSet Γ L M).ncard = q ^ 2 + 1 := by
        intro L M hL hLM
        rw [hp' L M hL hLM, hp's]
      have hdvd := dvd_of_ncard_lineSpan hP hT c (s := q ^ 2) (t := q ^ 3) hdeg hpcount
      have hdvd' : q ^ 2 + 1 ∣ (q ^ 3 + 1) * (q ^ 5 + 1) * q ^ 6 := by
        have h1 : q ^ 2 * q ^ 3 + 1 = q ^ 5 + 1 := by ring
        have h2 : (q ^ 3) ^ 2 = q ^ 6 := by ring
        simpa [h1, h2] using hdvd
      have hN2 : (((q ^ 3 + 1) * (q ^ 5 + 1) * q ^ 6 : ℕ) : ℤ) + 2 =
          ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 12 - (q : ℤ) ^ 10 + (q : ℤ) ^ 9 +
            (q : ℤ) ^ 8 - (q : ℤ) ^ 6 + 2 * (q : ℤ) ^ 4 - 2 * (q : ℤ) ^ 2 + 2) := by
        push_cast
        ring
      have hdvdZ : ((q ^ 2 + 1 : ℕ) : ℤ) ∣
          (((q ^ 3 + 1) * (q ^ 5 + 1) * q ^ 6 : ℕ) : ℤ) := by
        exact_mod_cast hdvd'
      have hdvd2Z : ((q ^ 2 + 1 : ℕ) : ℤ) ∣ (2 : ℤ) := by
        have h1 : ((q ^ 2 + 1 : ℕ) : ℤ) ∣
            (((q ^ 3 + 1) * (q ^ 5 + 1) * q ^ 6 : ℕ) : ℤ) + 2 := by
          rw [hN2]
          exact dvd_mul_right _ _
        simpa using dvd_sub h1 hdvdZ
      have hdvd2 : q ^ 2 + 1 ∣ 2 := Int.natCast_dvd_natCast.mp hdvd2Z
      have hle : q ^ 2 + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
      have hq2 : 4 ≤ q ^ 2 := by
        have h := Nat.pow_le_pow_left hq 2
        norm_num at h
        exact h
      omega
    · exact hp'1
    · exfalso
      have hq49 : q ^ 4 = q ^ 9 := by
        calc q ^ 4 = (q ^ 2) ^ 2 := by ring
          _ = (p' ^ 3) ^ 2 := by rw [hps3]
          _ = (p' ^ 2) ^ 3 := by ring
          _ = (q ^ 3) ^ 3 := by rw [hpt2]
          _ = q ^ 9 := by ring
      have h49 : 4 = 9 := Nat.pow_right_injective (by omega : 1 < q) hq49
      omega
  have hpoint : p = q := by
    rcases htri with hpt | hp1 | ⟨hps, hpt3⟩
    · exfalso
      have hreg : IsRegularVertex Γ x := by
        intro y hy
        rw [hp x y hx hy, hpt, hdeg x, if_pos hx]
      have hts := t_le_s_of_isRegularVertex hP hT c (s := q ^ 2) (t := q ^ 3) hdeg hx hreg
      have hlt : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right (by omega : 1 < q) (by norm_num)
      omega
    · exfalso
      have h1 : ∀ y, Γ.dist x y = 4 → (spanSet Γ x y).ncard = 2 := by
        intro y hy
        rw [hp x y hx hy, hp1]
      have h2 : ∀ L M : V, Γ.Adj x L → Γ.dist L M = 4 →
          (spanSet Γ L M).ncard = 2 := by
        intro L M hxL hLM
        have hcL : c L = 1 :=
          Fin.eq_one_of_ne_zero _ fun h => c.valid hxL (hx.trans h.symm)
        rw [hp' L M hcL hLM, hline]
      have hst : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega : 0 < q) (by norm_num)
      exact false_of_spans_two hP hT c (s := q ^ 2) (t := q ^ 3) hdeg hst hM hx h1 h2
    · exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hps).symm
  refine ⟨?_, ?_⟩
  · intro y z hy hyz
    rw [hp y z hy hyz, hpoint]
  · intro L M hL hLM
    rw [hp' L M hL hLM, hline]

theorem isThasQuadrangle_of_moufang (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {q : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then q ^ 3 + 1 else q ^ 2 + 1)
    (hM : MoufangCondition H Γ 4) : IsThasQuadrangle Γ c q := by
  obtain ⟨hspan, -⟩ := ncard_spanSet_of_hermitianOrder hP hT c hdeg hM
  refine ⟨hP, hT, two_le_q_of_hermitianOrder hP hT c hdeg, hdeg, hspan, fun u _ =>
    hasPropertyH hP hT hM u⟩

end CFSG.Geometry.GeneralizedQuadrangles

end
