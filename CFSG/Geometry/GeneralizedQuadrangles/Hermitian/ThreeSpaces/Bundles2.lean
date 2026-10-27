module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Bundles

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

theorem ncard_abs_threeBundle_of_isConePlane (hΓ : IsThasQuadrangle Γ c q) {T : Set V}
    (hT : IsConePlane Γ c T) :
    {E | E ∈ threeBundle Γ c q T ∧ ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}}.ncard = 1 := by
  classical
  obtain ⟨x, y, z, hx0, hxy, hztrace, rfl⟩ := hT
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hThick : IsThick Γ := hΓ.thick
  have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP hx0 hztrace.1
  have hzT : z ∈ ptPerp Γ c {z} ∩ clSet Γ x y := by
    refine ⟨?_, ?_⟩
    · rw [mem_ptPerp]
      refine ⟨hz0, ?_⟩
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      simp
    · rw [mem_clSet]
      refine ⟨x, left_mem_spanSet hxy, ?_⟩
      rw [SimpleGraph.dist_comm]
      exact le_of_eq hztrace.1
  have hset : {E | E ∈ threeBundle Γ c q (ptPerp Γ c {z} ∩ clSet Γ x y) ∧
      ∃ u, c u = 0 ∧ E = ptPerp Γ c {u}} = {ptPerp Γ c {z}} := by
    ext E
    constructor
    · rintro ⟨hE, u, hu0, rfl⟩
      have hEβ : IsThreespace Γ c q (ptPerp Γ c {u}) ∧
          (ptPerp Γ c {z} ∩ clSet Γ x y) ⊆ ptPerp Γ c {u} := by
        simpa only [threeBundle, Set.mem_setOf_eq] using hE
      have huEq : u = z := by
        by_contra hune
        have hspanCard : (spanSet Γ x y).ncard = q + 1 := hΓ.span x y hx0 hxy
        have h2 : 1 < (spanSet Γ x y).ncard := by
          rw [hspanCard]
          have hq := hΓ.two_le
          omega
        obtain ⟨w, hw, w', hw', hww'⟩ := (Set.one_lt_ncard (s := spanSet Γ x y)).mp h2
        have mem_cone : ∀ v : V, v ∈ spanSet Γ x y →
            v ∈ ptPerp Γ c {z} ∩ clSet Γ x y := by
          intro v hv
          have hzv : Γ.dist z v = 2 := by
            rw [SimpleGraph.dist_comm]
            exact dist_eq_two_of_mem_span_of_mem_trace hP hThick hxy hv hztrace
          refine ⟨?_, ?_⟩
          · rw [mem_ptPerp]
            exact ⟨(color_eq_of_mem_span hP hThick c hxy hv).trans hx0,
              fun a ha => by
                rw [Set.mem_singleton_iff] at ha
                subst a
                exact le_of_eq (by rw [SimpleGraph.dist_comm]; exact hzv)⟩
          · rw [mem_clSet]
            exact ⟨v, hv, by simp⟩
        have hwT := mem_cone w hw
        have hw'T := mem_cone w' hw'
        have huwle : Γ.dist u w ≤ 2 := by
          simpa [SimpleGraph.dist_comm] using (mem_ptPerp.mp (hEβ.2 hwT)).2 u (by simp)
        have huw'le : Γ.dist u w' ≤ 2 := by
          simpa [SimpleGraph.dist_comm] using (mem_ptPerp.mp (hEβ.2 hw'T)).2 u (by simp)
        have huzle : Γ.dist u z ≤ 2 := by
          simpa [SimpleGraph.dist_comm] using (mem_ptPerp.mp (hEβ.2 hzT)).2 u (by simp)
        have hw0 : c w = 0 := (color_eq_of_mem_span hP hThick c hxy hw).trans hx0
        have hw'0 : c w' = 0 := (color_eq_of_mem_span hP hThick c hxy hw').trans hx0
        have huw_ne : u ≠ w := by
          intro huw
          rw [huw] at huw'le
          have h4 : Γ.dist w w' = 4 := dist_eq_four_of_mem_span hP hThick hxy hw hw' hww'
          omega
        have huw'_ne : u ≠ w' := by
          intro huw'
          rw [huw'] at huwle
          have h4 : Γ.dist w w' = 4 := dist_eq_four_of_mem_span hP hThick hxy hw hw' hww'
          rw [SimpleGraph.dist_comm] at h4
          omega
        have huz2 : Γ.dist u z = 2 :=
          dist_eq_two_of_le_two_of_ne hP hu0 hz0 hune huzle
        have huw2 : Γ.dist u w = 2 :=
          dist_eq_two_of_le_two_of_ne hP hu0 hw0 huw_ne huwle
        have huw'2 : Γ.dist u w' = 2 :=
          dist_eq_two_of_le_two_of_ne hP hu0 hw'0 huw'_ne huw'le
        have hzw2 : Γ.dist z w = 2 := by
          rw [SimpleGraph.dist_comm]
          exact dist_eq_two_of_mem_span_of_mem_trace hP hThick hxy hw hztrace
        have hzw'2 : Γ.dist z w' = 2 := by
          rw [SimpleGraph.dist_comm]
          exact dist_eq_two_of_mem_span_of_mem_trace hP hThick hxy hw' hztrace
        let Kw : V := commonNeighbor hP hzw2
        let Kw' : V := commonNeighbor hP hzw'2
        have huKw : Γ.Adj u Kw := by
          obtain ⟨K, ⟨hKu, hKz, hKw⟩, -⟩ :=
            existsUnique_commonNeighbor_of_pairwise_dist_two hP huz2 huw2 hzw2
          have hKeq : K = Kw :=
            (existsUnique_commonNeighbor hP hzw2).unique ⟨hKz, hKw⟩
              ⟨commonNeighbor_adj_left hP hzw2, commonNeighbor_adj_right hP hzw2⟩
          rw [hKeq] at hKu
          exact hKu
        have huKw' : Γ.Adj u Kw' := by
          obtain ⟨K, ⟨hKu, hKz, hKw⟩, -⟩ :=
            existsUnique_commonNeighbor_of_pairwise_dist_two hP huz2 huw'2 hzw'2
          have hKeq : K = Kw' :=
            (existsUnique_commonNeighbor hP hzw'2).unique ⟨hKz, hKw⟩
              ⟨commonNeighbor_adj_left hP hzw'2, commonNeighbor_adj_right hP hzw'2⟩
          rw [hKeq] at hKu
          exact hKu
        have hKwne : Kw ≠ Kw' := by
          intro hKeq
          have h1 : Γ.Adj Kw w := (commonNeighbor_adj_right hP hzw2).symm
          have h2 : Γ.Adj Kw w' := by
            rw [hKeq]
            exact (commonNeighbor_adj_right hP hzw'2).symm
          have h2dist : Γ.dist w w' = 2 :=
            dist_eq_two_of_adj_of_adj_of_ne hP h1.symm h2 hww'
          have h4dist : Γ.dist w w' = 4 :=
            dist_eq_four_of_mem_span hP hThick hxy hw hw' hww'
          omega
        exact hKwne (eq_of_two_common_points hP hune huKw.symm
          (commonNeighbor_adj_left hP hzw2).symm huKw'.symm
          (commonNeighbor_adj_left hP hzw'2).symm)
      rw [Set.mem_singleton_iff, huEq]
    · intro hE
      rw [Set.mem_singleton_iff] at hE
      subst E
      refine ⟨⟨Or.inl ⟨z, hz0, rfl⟩, ?_⟩, z, hz0, rfl⟩
      intro t ht
      exact ht.1
  rw [hset, Set.ncard_singleton]

private theorem threeBundle_card_equation (hΓ : IsThasQuadrangle Γ c q) {T : Set V}
    (hT : IsTracePlane Γ c T ∨ IsConePlane Γ c T) {absCard a b : ℕ}
    (habsCard : {E | E ∈ threeBundle Γ c q T ∧ ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}}.ncard =
      absCard)
    (habsA : ∀ E, E ∈ threeBundle Γ c q T → (∃ x, c x = 0 ∧ E = ptPerp Γ c {x}) →
      (E \ T).ncard = a)
    (hnonB : ∀ E, E ∈ threeBundle Γ c q T → ¬ (∃ x, c x = 0 ∧ E = ptPerp Γ c {x}) →
      (E \ T).ncard = b) :
    absCard * a + ((threeBundle Γ c q T).ncard - absCard) * b =
      ((pointFinset c : Set V)).ncard - T.ncard := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  let P : Finset V := pointFinset c
  have hTsubP : T ⊆ (P : Set V) := by
    rcases hT with ⟨y, z, hy0, hyz, rfl⟩ | ⟨x, y, z, hx0, hxy, hz, rfl⟩
    · intro t ht
      have ht0 : c t = 0 := color_eq_zero_of_dist_eq_two hP hy0 ht.1
      simpa [P, mem_pointFinset] using ht0
    · intro t ht
      have ht0 : c t = 0 := (mem_ptPerp.mp ht.1).1
      simpa [P, mem_pointFinset] using ht0
  have hEsubP : ∀ E ∈ threeBundle Γ c q T, E ⊆ (P : Set V) := by
    intro E hE x hx
    have hEβ : IsThreespace Γ c q E ∧ T ⊆ E := by
      simpa only [threeBundle, Set.mem_setOf_eq] using hE
    have hx0 : c x = 0 := by
      rcases hEβ.1 with ⟨u, -, rfl⟩ | hF
      · exact (mem_ptPerp.mp hx).1
      · exact hF.1 x hx
    simpa [P, mem_pointFinset] using hx0
  let β : Set (Set V) := threeBundle Γ c q T
  let βfin : Finset (Set V) := β.toFinset
  let Abs : Set V → Prop := fun E => ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}
  let L : Finset (Set V) := βfin.filter Abs
  let R : Finset (Set V) := βfin.filter (fun E => ¬ Abs E)
  have hβmem : ∀ E, E ∈ βfin ↔ E ∈ β := by
    intro E
    simp [βfin]
  have hLmem : ∀ E, E ∈ L ↔ E ∈ β ∧ Abs E := by
    intro E
    simp [L, βfin, Abs]
  have hRmem : ∀ E, E ∈ R ↔ E ∈ β ∧ ¬ Abs E := by
    intro E
    simp [R, βfin, Abs]
  have hLcard : L.card = absCard := by
    rw [← habsCard]
    have hLset : L = {E | E ∈ β ∧ Abs E}.toFinset := by
      ext E
      rw [hLmem]
      simp
    change L.card = {E | E ∈ β ∧ Abs E}.ncard
    rw [hLset, ← Set.ncard_eq_toFinset_card']
  have hRcard : R.card = β.ncard - absCard := by
    have hsum : L.card + R.card = βfin.card := by
      simpa [L, R] using (Finset.card_filter_add_card_filter_not (s := βfin) (p := Abs))
    have hβfincard : βfin.card = β.ncard := by
      change β.toFinset.card = β.ncard
      exact (Set.ncard_eq_toFinset_card' β).symm
    omega
  have hterm : ∀ E ∈ βfin, (E \ T).ncard = if Abs E then a else b := by
    intro E hE
    have hEβ : E ∈ threeBundle Γ c q T := by
      have := (hβmem E).1 hE
      simpa [β] using this
    by_cases hA : Abs E
    · rw [if_pos hA]
      exact habsA E hEβ hA
    · rw [if_neg hA]
      exact hnonB E hEβ hA
  have htermSum : (∑ E ∈ βfin, (E \ T).ncard) =
      ∑ E ∈ βfin, (if Abs E then a else b) :=
    Finset.sum_congr rfl hterm
  have hsum2 : (∑ E ∈ βfin, (if Abs E then a else b)) =
      absCard * a + (β.ncard - absCard) * b := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    change L.card • a + R.card • b = absCard * a + (β.ncard - absCard) * b
    rw [hLcard, hRcard, smul_eq_mul, smul_eq_mul]
  let U : Finset V := βfin.biUnion (fun E => (E \ T).toFinset)
  have hUeq : (U : Set V) = (P : Set V) \ T := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_coe, Finset.mem_biUnion] at hv
      obtain ⟨E, hE, hvE⟩ := hv
      have hEβ : E ∈ threeBundle Γ c q T := by
        have := (hβmem E).1 hE
        simpa [β] using this
      have hvE' : v ∈ E \ T := by simpa using hvE
      exact ⟨hEsubP E hEβ hvE'.1, hvE'.2⟩
    · rintro ⟨hvP, hvT⟩
      have hv0 : c v = 0 := by
        simpa [P, mem_pointFinset] using hvP
      obtain ⟨E0, ⟨hE0th, hTE0, hvE0⟩, -⟩ :=
        existsUnique_threespace hΓ hT hv0 hvT
      rw [Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨E0, ?_, ?_⟩
      · rw [hβmem]
        exact ⟨hE0th, hTE0⟩
      · simp [hvE0, hvT]
  have hUcard : U.card = ∑ E ∈ βfin, (E \ T).ncard := by
    rw [Finset.card_biUnion]
    · exact Finset.sum_congr rfl (fun E _ =>
        (Set.ncard_eq_toFinset_card' (E \ T)).symm)
    · intro E hE E' hE' hne
      rw [Function.onFun, Finset.disjoint_left]
      intro v hv hv'
      have hv1 : v ∈ E \ T := by simpa using hv
      have hv2 : v ∈ E' \ T := by simpa using hv'
      have hEβ : E ∈ threeBundle Γ c q T := by
        have := (hβmem E).1 hE
        simpa [β] using this
      have hE'β : E' ∈ threeBundle Γ c q T := by
        have := (hβmem E').1 hE'
        simpa [β] using this
      have hinter := inter_eq_of_mem_threeBundle hΓ hT hEβ hE'β hne
      exact hv1.2 (by rw [← hinter]; exact ⟨hv1.1, hv2.1⟩)
  have hleft : ((P : Set V) \ T).ncard = U.card := by
    rw [← hUeq, Set.ncard_coe_finset]
  have hPsdiff : ((P : Set V) \ T).ncard = ((P : Set V)).ncard - T.ncard :=
    Set.ncard_sdiff hTsubP
  calc
    absCard * a + ((threeBundle Γ c q T).ncard - absCard) * b
        = ∑ E ∈ βfin, (E \ T).ncard := by
          rw [show β.ncard = (threeBundle Γ c q T).ncard from rfl]
          exact (htermSum.trans hsum2).symm
    _ = U.card := hUcard.symm
    _ = ((P : Set V) \ T).ncard := hleft.symm
    _ = ((pointFinset c : Set V)).ncard - T.ncard := by simpa [P] using hPsdiff

private theorem trace_members {q N : ℕ} (hq : 2 ≤ q)
    (h : (q + 1) * (q ^ 5 - q ^ 3 + q ^ 2) + N * (q ^ 5 + q ^ 2) =
      (q ^ 2 + 1) * (q ^ 5 + 1) - (q ^ 3 + 1)) :
    N = q ^ 2 - q := by
  have hqpos : 0 < q := by omega
  have hq35 : q ^ 3 ≤ q ^ 5 := Nat.pow_le_pow_right hqpos (by norm_num)
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hqpos
  have hTleP : q ^ 3 + 1 ≤ (q ^ 2 + 1) * (q ^ 5 + 1) := by
    have h1 : q ^ 3 + 1 ≤ q ^ 5 + 1 := by omega
    have h2 : q ^ 5 + 1 ≤ (q ^ 2 + 1) * (q ^ 5 + 1) := by
      calc q ^ 5 + 1 = 1 * (q ^ 5 + 1) := (one_mul _).symm
        _ ≤ (q ^ 2 + 1) * (q ^ 5 + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hZ : ((q : ℤ) + 1) * ((q : ℤ) ^ 5 - (q : ℤ) ^ 3 + (q : ℤ) ^ 2) +
      (N : ℤ) * ((q : ℤ) ^ 5 + (q : ℤ) ^ 2) =
      ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 5 + 1) - ((q : ℤ) ^ 3 + 1) := by
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast at hcast
    rw [Nat.cast_sub hq35, Nat.cast_sub hTleP] at hcast
    push_cast at hcast
    exact hcast
  have hEq' : ((q : ℤ) + 1) * ((q : ℤ) ^ 5 + (q : ℤ) ^ 2 + 1) +
      (N : ℤ) * ((q : ℤ) ^ 5 + (q : ℤ) ^ 2) =
      ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 5 + 1) + (q : ℤ) * ((q : ℤ) ^ 3 + 1) := by
    have h' := hZ
    ring_nf at h' ⊢
    linarith
  have hID : ((q : ℤ) + 1) * ((q : ℤ) ^ 5 + (q : ℤ) ^ 2 + 1) +
      (q : ℤ) ^ 3 * ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1) =
      ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 5 + 1) + (q : ℤ) * ((q : ℤ) ^ 3 + 1) := by
    ring
  have hN1 : (N : ℤ) * ((q : ℤ) ^ 5 + (q : ℤ) ^ 2) =
      (q : ℤ) ^ 3 * ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1) := by
    linarith
  have hN1' : ((N : ℤ) * (q : ℤ) ^ 2) * ((q : ℤ) ^ 3 + 1) =
      ((q : ℤ) ^ 3 * ((q : ℤ) - 1)) * ((q : ℤ) ^ 3 + 1) := by
    have h' := hN1
    ring_nf at h' ⊢
    linarith
  have hq3nz : ((q : ℤ) ^ 3 + 1) ≠ 0 := by positivity
  have hN2 : (N : ℤ) * (q : ℤ) ^ 2 = (q : ℤ) ^ 3 * ((q : ℤ) - 1) :=
    mul_right_cancel₀ hq3nz hN1'
  have hN3 : ((q : ℤ) ^ 2) * (N : ℤ) = ((q : ℤ) ^ 2) * ((q : ℤ) * ((q : ℤ) - 1)) := by
    rw [mul_comm ((q : ℤ) ^ 2) (N : ℤ), hN2]
    ring
  have hq2nz : ((q : ℤ) ^ 2) ≠ 0 := by positivity
  have hN4 : (N : ℤ) = (q : ℤ) * ((q : ℤ) - 1) :=
    mul_left_cancel₀ hq2nz hN3
  have hNZ : (N : ℤ) = (q : ℤ) ^ 2 - (q : ℤ) := by
    rw [hN4]
    ring
  have hqle : q ≤ q ^ 2 := by
    calc q = q * 1 := (Nat.mul_one q).symm
      _ ≤ q * q := Nat.mul_le_mul_left q (by omega)
      _ = q ^ 2 := by ring
  have hcast_sub : (((q ^ 2 - q : ℕ) : ℤ)) = (q : ℤ) ^ 2 - (q : ℤ) := by
    rw [Nat.cast_sub hqle]
    push_cast
    ring
  exact_mod_cast (hNZ.trans hcast_sub.symm)

private theorem cone_members {q N : ℕ} (hq : 2 ≤ q)
    (hTleP : q ^ 3 + q ^ 2 + 1 ≤ (q ^ 2 + 1) * (q ^ 5 + 1))
    (h : (q ^ 5 - q ^ 3) + N * q ^ 5 =
      (q ^ 2 + 1) * (q ^ 5 + 1) - (q ^ 3 + q ^ 2 + 1)) :
    N = q ^ 2 := by
  have hqpos : 0 < q := by omega
  have hq35 : q ^ 3 ≤ q ^ 5 := Nat.pow_le_pow_right hqpos (by norm_num)
  have hZ : ((q : ℤ) ^ 5 - (q : ℤ) ^ 3) + (N : ℤ) * (q : ℤ) ^ 5 =
      ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 5 + 1) - ((q : ℤ) ^ 3 + (q : ℤ) ^ 2 + 1) := by
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast at hcast
    rw [Nat.cast_sub hq35, Nat.cast_sub hTleP] at hcast
    push_cast at hcast
    exact hcast
  have hEq' : ((q : ℤ) ^ 5 + (q : ℤ) ^ 2 + 1) + (N : ℤ) * (q : ℤ) ^ 5 =
      ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 5 + 1) := by
    have h' := hZ
    ring_nf at h' ⊢
    linarith
  have hN1 : (N : ℤ) * (q : ℤ) ^ 5 = (q : ℤ) ^ 7 := by
    have h' := hEq'
    ring_nf at h' ⊢
    linarith
  have hN1' : (N : ℤ) * (q : ℤ) ^ 5 = ((q : ℤ) ^ 2) * (q : ℤ) ^ 5 := by
    rw [hN1]
    ring
  have hq5nz : ((q : ℤ) ^ 5) ≠ 0 := by positivity
  exact_mod_cast (mul_right_cancel₀ hq5nz hN1')

theorem ncard_of_isThreeBundle (hΓ : IsThasQuadrangle Γ c q) {β : Set (Set V)}
    (hβ : IsThreeBundle Γ c q β) : β.ncard = q ^ 2 + 1 := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hThick : IsThick Γ := hΓ.thick
  have hqle : q ≤ q ^ 2 := by
    calc q = q * 1 := (Nat.mul_one q).symm
      _ ≤ q * q := Nat.mul_le_mul_left q (by have := hΓ.two_le; omega)
      _ = q ^ 2 := by ring
  have hPcard : (pointFinset c).card = (q ^ 2 + 1) * (q ^ 5 + 1) := by
    rw [card_pointFinset hP hThick c (s := q ^ 2) (t := q ^ 3) hΓ.deg]
    have hpow : q ^ 2 * q ^ 3 = q ^ 5 := by ring
    rw [hpow]
  rcases hβ with ⟨T, hT, rfl⟩ | ⟨L, hL, rfl⟩
  · rcases hT with hTtrace | hTcone
    · obtain ⟨y, z, hy0, hyz, rfl⟩ := hTtrace
      have htrace : IsTracePlane Γ c (traceSet Γ y z) := ⟨y, z, hy0, hyz, rfl⟩
      have hTcard : (traceSet Γ y z).ncard = q ^ 3 + 1 := by
        rw [ncard_trace hP hyz, hΓ.deg y, if_pos hy0]
      have hEabs : ∀ E, E ∈ threeBundle Γ c q (traceSet Γ y z) →
          (∃ u, c u = 0 ∧ E = ptPerp Γ c {u}) →
          (E \ traceSet Γ y z).ncard = q ^ 5 - q ^ 3 + q ^ 2 := by
        intro E hE hAbs
        have hEβ : IsThreespace Γ c q E ∧ traceSet Γ y z ⊆ E := by
          simpa only [threeBundle, Set.mem_setOf_eq] using hE
        obtain ⟨u, hu0, rfl⟩ := hAbs
        have hEcard : (ptPerp Γ c {u}).ncard = q ^ 5 + q ^ 2 + 1 := by
          rw [ncard_ptPerp_singleton hP hThick c (s := q ^ 2) (t := q ^ 3) hΓ.deg hu0]
          have hpow : q ^ 2 * q ^ 3 = q ^ 5 := by ring
          rw [hpow]
        rw [Set.ncard_sdiff hEβ.2, hEcard, hTcard]
        have hle : q ^ 3 ≤ q ^ 5 :=
          Nat.pow_le_pow_right (by have := hΓ.two_le; omega) (by norm_num)
        omega
      have hEnon : ∀ E, E ∈ threeBundle Γ c q (traceSet Γ y z) →
          ¬ (∃ u, c u = 0 ∧ E = ptPerp Γ c {u}) →
          (E \ traceSet Γ y z).ncard = q ^ 5 + q ^ 2 := by
        intro E hE hnon
        have hEβ : IsThreespace Γ c q E ∧ traceSet Γ y z ⊆ E := by
          simpa only [threeBundle, Set.mem_setOf_eq] using hE
        have hF : IsFullSubquadrangle c E q := by
          rcases hEβ.1 with hAbs | hF
          · exact absurd hAbs hnon
          · exact hF
        have hEcard : E.ncard = (q ^ 2 + 1) * (q ^ 3 + 1) := by
          rw [ncard_of_isFullSubquadrangle hP hThick c (s := q ^ 2) (t := q ^ 3) hΓ.deg hF]
          have hpow : q ^ 2 * q = q ^ 3 := by ring
          rw [hpow]
        rw [Set.ncard_sdiff hEβ.2, hEcard, hTcard]
        have hEq : (q ^ 2 + 1) * (q ^ 3 + 1) = q ^ 2 * (q ^ 3 + 1) + (q ^ 3 + 1) := by
          ring
        rw [hEq, Nat.add_sub_cancel]
        ring
      have habsCard : {E | E ∈ threeBundle Γ c q (traceSet Γ y z) ∧
          ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}}.ncard = q + 1 :=
        ncard_abs_threeBundle hΓ htrace
      have hEq := threeBundle_card_equation hΓ (Or.inl htrace) habsCard hEabs hEnon
      have h : (q + 1) * (q ^ 5 - q ^ 3 + q ^ 2) +
          ((threeBundle Γ c q (traceSet Γ y z)).ncard - (q + 1)) * (q ^ 5 + q ^ 2) =
          (q ^ 2 + 1) * (q ^ 5 + 1) - (q ^ 3 + 1) := by
        simpa [Set.ncard_coe_finset, hPcard, hTcard] using hEq
      have hN := trace_members hΓ.two_le h
      have hle : q + 1 ≤ (threeBundle Γ c q (traceSet Γ y z)).ncard := by
        rw [← habsCard]
        exact Set.ncard_le_ncard (fun E hE => hE.1) (Set.toFinite _)
      have hsplit : (threeBundle Γ c q (traceSet Γ y z)).ncard =
          (q + 1) + ((threeBundle Γ c q (traceSet Γ y z)).ncard - (q + 1)) := by
        omega
      rw [hsplit, hN]
      omega
    · obtain ⟨x, y, z, hx0, hxy, hz, rfl⟩ := hTcone
      have hcone : IsConePlane Γ c (ptPerp Γ c {z} ∩ clSet Γ x y) :=
        ⟨x, y, z, hx0, hxy, hz, rfl⟩
      have hTcard : (ptPerp Γ c {z} ∩ clSet Γ x y).ncard = q ^ 3 + q ^ 2 + 1 :=
        ncard_of_isConePlane hΓ hcone
      have hTsubP : (ptPerp Γ c {z} ∩ clSet Γ x y) ⊆ (pointFinset c : Set V) := by
        intro t ht
        have ht0 : c t = 0 := (mem_ptPerp.mp ht.1).1
        simpa [mem_pointFinset] using ht0
      have hTleP : q ^ 3 + q ^ 2 + 1 ≤ (q ^ 2 + 1) * (q ^ 5 + 1) := by
        have hle : (ptPerp Γ c {z} ∩ clSet Γ x y).ncard ≤
            ((pointFinset c : Set V)).ncard :=
          Set.ncard_le_ncard hTsubP (Set.toFinite _)
        rw [hTcard, Set.ncard_coe_finset, hPcard] at hle
        exact hle
      have hEabs : ∀ E, E ∈ threeBundle Γ c q (ptPerp Γ c {z} ∩ clSet Γ x y) →
          (∃ u, c u = 0 ∧ E = ptPerp Γ c {u}) →
          (E \ (ptPerp Γ c {z} ∩ clSet Γ x y)).ncard = q ^ 5 - q ^ 3 := by
        intro E hE hAbs
        have hEβ : IsThreespace Γ c q E ∧
            (ptPerp Γ c {z} ∩ clSet Γ x y) ⊆ E := by
          simpa only [threeBundle, Set.mem_setOf_eq] using hE
        obtain ⟨u, hu0, rfl⟩ := hAbs
        have hEcard : (ptPerp Γ c {u}).ncard = q ^ 5 + q ^ 2 + 1 := by
          rw [ncard_ptPerp_singleton hP hThick c (s := q ^ 2) (t := q ^ 3) hΓ.deg hu0]
          have hpow : q ^ 2 * q ^ 3 = q ^ 5 := by ring
          rw [hpow]
        rw [Set.ncard_sdiff hEβ.2, hEcard, hTcard]
        have hle : q ^ 3 ≤ q ^ 5 :=
          Nat.pow_le_pow_right (by have := hΓ.two_le; omega) (by norm_num)
        omega
      have hEnon : ∀ E, E ∈ threeBundle Γ c q (ptPerp Γ c {z} ∩ clSet Γ x y) →
          ¬ (∃ u, c u = 0 ∧ E = ptPerp Γ c {u}) →
          (E \ (ptPerp Γ c {z} ∩ clSet Γ x y)).ncard = q ^ 5 := by
        intro E hE hnon
        have hEβ : IsThreespace Γ c q E ∧
            (ptPerp Γ c {z} ∩ clSet Γ x y) ⊆ E := by
          simpa only [threeBundle, Set.mem_setOf_eq] using hE
        have hF : IsFullSubquadrangle c E q := by
          rcases hEβ.1 with hAbs | hF
          · exact absurd hAbs hnon
          · exact hF
        have hEcard : E.ncard = (q ^ 2 + 1) * (q ^ 3 + 1) := by
          rw [ncard_of_isFullSubquadrangle hP hThick c (s := q ^ 2) (t := q ^ 3) hΓ.deg hF]
          have hpow : q ^ 2 * q = q ^ 3 := by ring
          rw [hpow]
        rw [Set.ncard_sdiff hEβ.2, hEcard, hTcard]
        have hEq : (q ^ 2 + 1) * (q ^ 3 + 1) = q ^ 5 + (q ^ 3 + q ^ 2 + 1) := by
          ring
        rw [hEq, Nat.add_sub_cancel]
      have habsCard : {E | E ∈ threeBundle Γ c q (ptPerp Γ c {z} ∩ clSet Γ x y) ∧
          ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}}.ncard = 1 :=
        ncard_abs_threeBundle_of_isConePlane hΓ hcone
      have hEq := threeBundle_card_equation hΓ (Or.inr hcone) habsCard hEabs hEnon
      have h : (q ^ 5 - q ^ 3) +
          ((threeBundle Γ c q (ptPerp Γ c {z} ∩ clSet Γ x y)).ncard - 1) * q ^ 5 =
          (q ^ 2 + 1) * (q ^ 5 + 1) - (q ^ 3 + q ^ 2 + 1) := by
        simpa [Set.ncard_coe_finset, hPcard, hTcard, one_mul] using hEq
      have hN := cone_members hΓ.two_le hTleP h
      have hle : 1 ≤ (threeBundle Γ c q (ptPerp Γ c {z} ∩ clSet Γ x y)).ncard := by
        rw [← habsCard]
        exact Set.ncard_le_ncard (fun E hE => hE.1) (Set.toFinite _)
      have hsplit : (threeBundle Γ c q (ptPerp Γ c {z} ∩ clSet Γ x y)).ncard =
          1 + ((threeBundle Γ c q (ptPerp Γ c {z} ∩ clSet Γ x y)).ncard - 1) := by
        omega
      rw [hsplit, hN]
      omega
  · have hset : lineBundle Γ c L =
        (fun u => ptPerp Γ c {u}) '' (Γ.neighborSet L) := by
      ext E
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, rfl⟩
    rw [hset]
    have hinj : Set.InjOn (fun u => ptPerp Γ c {u}) (Γ.neighborSet L) := by
      intro u hu v hv huv
      have hu0 : c u = 0 :=
        color_eq_zero_of_adj_of_color_eq_one hL (by simpa [mem_neighborSet] using hu)
      have hv0 : c v = 0 :=
        color_eq_zero_of_adj_of_color_eq_one hL (by simpa [mem_neighborSet] using hv)
      exact ptPerp_singleton_injective hP hThick hu0 hv0 huv
    rw [hinj.ncard_image, SimpleGraph.ncard_neighborSet, hΓ.deg L,
      if_neg (by rw [hL]; decide)]

end CFSG.Geometry.GeneralizedQuadrangles
