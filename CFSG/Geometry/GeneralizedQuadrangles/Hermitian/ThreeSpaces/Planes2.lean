module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Basic
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Subquadrangles
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Bundles

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

private theorem card_subquadrangleLines (hΓ : IsThasQuadrangle Γ c q) {E : Set V}
    (hF : IsFullSubquadrangle c E q) :
    (subquadrangleLines Γ c E).ncard = (q + 1) * (q ^ 3 + 1) := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c E)) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hT c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c E)) :=
    isThick_subquadrangleGraph hP hT c hΓ.deg hF hΓ.two_le
  have hdeg' : ∀ w : subquadrangleSet Γ c E,
      (Γ.induce (subquadrangleSet Γ c E)).degree w =
        if subquadrangleColoring c E w = 0 then q + 1 else q ^ 2 + 1 :=
    fun w => degree_subquadrangleGraph hΓ hF w
  have hcard := card_lineFinset hP' hT' (subquadrangleColoring c E) (s := q ^ 2) (t := q) hdeg'
  have hset : ((lineFinset (subquadrangleColoring c E) : Set (subquadrangleSet Γ c E))).ncard
      = (subquadrangleLines Γ c E).ncard := by
    refine Set.ncard_congr (fun v _ => (v : V)) ?_ ?_ ?_
    · intro v hv
      rw [Finset.mem_coe, mem_lineFinset] at hv
      rcases mem_subquadrangleSet.mp v.2 with hvE | hvL
      · have hc0 : subquadrangleColoring c E v = 0 := by
          rw [subquadrangleColoring_apply, hF.1 v.1 hvE]
        rw [hv] at hc0
        exact absurd hc0 (by decide)
      · exact hvL
    · intro a b ha hb hab
      exact Subtype.ext hab
    · intro L hL
      refine ⟨⟨L, mem_subquadrangleSet.mpr (Or.inr (mem_subquadrangleLines.mp hL))⟩, ?_, rfl⟩
      rw [Finset.mem_coe, mem_lineFinset, subquadrangleColoring_apply]
      exact hL.1
  rw [← hset, Set.ncard_coe_finset, hcard]
  ring


private theorem ncard_opposite_fullLines (hΓ : IsThasQuadrangle Γ c q) {E : Set V}
    (hF : IsFullSubquadrangle c E q) {L : V} (hL : L ∈ subquadrangleLines Γ c E) :
    {M : V | M ∈ subquadrangleLines Γ c E ∧ Γ.dist L M = 4}.ncard = q ^ 4 := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c E)) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hT c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c E)) :=
    isThick_subquadrangleGraph hP hT c hΓ.deg hF hΓ.two_le
  have hdeg' : ∀ w : subquadrangleSet Γ c E,
      (Γ.induce (subquadrangleSet Γ c E)).degree w =
        if subquadrangleColoring c E w = 0 then q + 1 else q ^ 2 + 1 :=
    fun w => degree_subquadrangleGraph hΓ hF w
  let c' := subquadrangleColoring c E
  let dc : (Γ.induce (subquadrangleSet Γ c E)).Coloring (Fin 2) :=
    (Γ.induce (subquadrangleSet Γ c E)).recolorOfEquiv (Equiv.swap (0 : Fin 2) 1) c'
  have hdc0 : ∀ v, dc v = 0 ↔ c' v = 1 := by
    intro v
    change Equiv.swap (0 : Fin 2) 1 (c' v) = 0 ↔ c' v = 1
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c' v) with h | h <;> rw [h] <;> decide
  have hdeg'' : ∀ v : subquadrangleSet Γ c E,
      (Γ.induce (subquadrangleSet Γ c E)).degree v =
        if dc v = 0 then q ^ 2 + 1 else q + 1 := by
    intro v
    have hv := hdeg' v
    by_cases hv0 : c' v = 0
    · have hdc : dc v ≠ 0 := by
        intro h
        have h1 : c' v = 1 := (hdc0 v).mp h
        rw [hv0] at h1
        exact absurd h1 (by decide)
      rw [hv, if_pos hv0, if_neg hdc]
    · have hv1 : c' v = 1 := by
        have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
        rcases hfin (c' v) with h | h
        · exact absurd h hv0
        · exact h
      have hdc : dc v = 0 := (hdc0 v).mpr hv1
      rw [hv, if_neg hv0, if_pos hdc]
  let L' : subquadrangleSet Γ c E :=
    ⟨L, mem_subquadrangleSet.mpr (Or.inr (mem_subquadrangleLines.mp hL))⟩
  have hL'1 : c' L' = 1 := by
    rw [subquadrangleColoring_apply]
    exact hL.1
  have hdcL : dc L' = 0 := (hdc0 L').mpr hL'1
  have hcount : {y : subquadrangleSet Γ c E
      | (Γ.induce (subquadrangleSet Γ c E)).dist L' y = 4}.ncard = q ^ 2 * q ^ 2 := by
    rw [Set.ncard_eq_toFinset_card]
    have h := card_opposite hP' hT' dc hdeg'' (x := L') hdcL
    convert h using 2
    ext y
    simp
  have hset : {M : V | M ∈ subquadrangleLines Γ c E ∧ Γ.dist L M = 4}
      = Subtype.val '' {M : subquadrangleSet Γ c E
          | (Γ.induce (subquadrangleSet Γ c E)).dist L' M = 4} := by
    ext M
    constructor
    · rintro ⟨hML, hdist⟩
      refine ⟨⟨M, mem_subquadrangleSet.mpr (Or.inr (mem_subquadrangleLines.mp hML))⟩, ?_, rfl⟩
      simp only [Set.mem_setOf_eq]
      rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF _ _, hdist]
    · rintro ⟨M', hM'dist, rfl⟩
      have hdist' : (Γ.induce (subquadrangleSet Γ c E)).dist L' M' = 4 := by
        simpa only [Set.mem_setOf_eq] using hM'dist
      have hM'1 : c' M' = 1 := by
        have heven : Even ((Γ.induce (subquadrangleSet Γ c E)).dist L' M') := by
          rw [hdist']
          exact ⟨2, by norm_num⟩
        have hc := (hP'.eq_iff_even_dist c' L' M').2 heven
        rw [← hc, hL'1]
      have hM'line : (M' : V) ∈ subquadrangleLines Γ c E := by
        rcases mem_subquadrangleSet.mp M'.2 with hE | hline
        · have hzero : c' M' = 0 := by
            rw [subquadrangleColoring_apply, hF.1 M'.1 hE]
          rw [hzero] at hM'1
          exact absurd hM'1 (by decide)
        · exact hline
      refine ⟨hM'line, ?_⟩
      rw [← dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF L'.2 M'.2]
      exact hdist'
  rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective, hcount]
  ring


private theorem card_pairs_in_subquadrangle (hΓ : IsThasQuadrangle Γ c q) {E : Set V}
    (hF : IsFullSubquadrangle c E q) :
    {p : V × V | p.1 ∈ subquadrangleLines Γ c E ∧ p.2 ∈ subquadrangleLines Γ c E ∧
      Γ.dist p.1 p.2 = 4}.ncard = (q + 1) * (q ^ 3 + 1) * q ^ 4 := by
  classical
  let LinesE : Finset V := (Set.toFinite (subquadrangleLines Γ c E)).toFinset
  have hLinesCard : LinesE.card = (q + 1) * (q ^ 3 + 1) := by
    rw [← Set.ncard_eq_toFinset_card]
    exact card_subquadrangleLines hΓ hF
  let PairF : Finset (V × V) := (LinesE ×ˢ LinesE).filter (fun p => Γ.dist p.1 p.2 = 4)
  have hcoe : (PairF : Set (V × V)) =
      {p : V × V | p.1 ∈ subquadrangleLines Γ c E ∧ p.2 ∈ subquadrangleLines Γ c E ∧
        Γ.dist p.1 p.2 = 4} := by
    ext p
    simp only [PairF, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, LinesE,
      Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    tauto
  have hmap : (PairF : Set (V × V)).MapsTo Prod.fst (LinesE : Set V) := by
    intro p hp
    simp only [Finset.mem_coe, PairF, Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.1
  have hsum := Finset.card_eq_sum_card_fiberwise (s := PairF) (t := LinesE)
    (f := Prod.fst) hmap
  have hfiber : ∀ L ∈ LinesE, (PairF.filter (fun p => p.1 = L)).card = q ^ 4 := by
    intro L hL
    have hLmem : L ∈ subquadrangleLines Γ c E := by
      simpa [LinesE] using hL
    have hfilter : PairF.filter (fun p => p.1 = L) =
        (LinesE.filter (fun M => Γ.dist L M = 4)).image (fun M => (L, M)) := by
      ext p
      constructor
      · intro hp
        simp only [Finset.mem_filter, Finset.mem_image, PairF, Finset.mem_product] at hp ⊢
        obtain ⟨⟨⟨hp1, hp2⟩, hdist⟩, hfirst⟩ := hp
        subst hfirst
        exact ⟨p.2, ⟨hp2, hdist⟩, rfl⟩
      · intro hp
        simp only [Finset.mem_filter, Finset.mem_image, PairF, Finset.mem_product] at hp ⊢
        obtain ⟨M, ⟨hMmem, hdist⟩, rfl⟩ := hp
        exact ⟨⟨⟨hL, hMmem⟩, hdist⟩, rfl⟩
    rw [hfilter, Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)]
    have hcardset : (LinesE.filter (fun M => Γ.dist L M = 4)).card
        = {M : V | M ∈ subquadrangleLines Γ c E ∧ Γ.dist L M = 4}.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext M
      simp only [Finset.mem_coe, Finset.mem_filter, LinesE, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq]
    rw [hcardset]
    exact ncard_opposite_fullLines hΓ hF hLmem
  rw [← hcoe, Set.ncard_coe_finset, hsum, Finset.sum_congr rfl hfiber, Finset.sum_const,
    smul_eq_mul, hLinesCard]


private theorem ncard_opposite_lines (hΓ : IsThasQuadrangle Γ c q) {L : V} (hL : c L = 1) :
    {M : V | c M = 1 ∧ Γ.dist L M = 4}.ncard = q ^ 8 := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  let dc : Γ.Coloring (Fin 2) := Γ.recolorOfEquiv (Equiv.swap (0 : Fin 2) 1) c
  have hdc0 : ∀ v, dc v = 0 ↔ c v = 1 := by
    intro v
    change Equiv.swap (0 : Fin 2) 1 (c v) = 0 ↔ c v = 1
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c v) with h | h <;> rw [h] <;> decide
  have hdeg' : ∀ v, Γ.degree v = if dc v = 0 then q ^ 2 + 1 else q ^ 3 + 1 := by
    intro v
    by_cases hv0 : c v = 0
    · have hdc : dc v ≠ 0 := by
        intro h
        have h1 : c v = 1 := (hdc0 v).mp h
        rw [hv0] at h1
        exact absurd h1 (by decide)
      rw [hΓ.deg v, if_pos hv0, if_neg hdc]
    · have hv1 : c v = 1 := by
        have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
        rcases hfin (c v) with h | h
        · exact absurd h hv0
        · exact h
      have hdc : dc v = 0 := (hdc0 v).mpr hv1
      rw [hΓ.deg v, if_neg hv0, if_pos hdc]
  have hdcL : dc L = 0 := (hdc0 L).mpr hL
  have hcount : {M : V | Γ.dist L M = 4}.ncard = (q ^ 3) ^ 2 * q ^ 2 := by
    rw [Set.ncard_eq_toFinset_card]
    have h := card_opposite hP hT dc hdeg' (x := L) hdcL
    convert h using 2
    ext y
    simp
  have hset : {M : V | c M = 1 ∧ Γ.dist L M = 4} = {M : V | Γ.dist L M = 4} := by
    ext M
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      refine ⟨?_, h⟩
      have hc := (hP.eq_iff_even_dist c L M).2 (by rw [h]; exact ⟨2, by norm_num⟩)
      rw [hL] at hc
      exact hc.symm
  rw [hset, hcount]
  ring

private theorem card_pairs_all (hΓ : IsThasQuadrangle Γ c q) :
    {p : V × V | c p.1 = 1 ∧ c p.2 = 1 ∧ Γ.dist p.1 p.2 = 4}.ncard
      = (q ^ 3 + 1) * (q ^ 5 + 1) * q ^ 8 := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  let Lines : Finset V := lineFinset c
  have hLinesCard : Lines.card = (q ^ 3 + 1) * (q ^ 5 + 1) := by
    rw [card_lineFinset hP hT c (s := q ^ 2) (t := q ^ 3) hΓ.deg]
    ring
  let PairF : Finset (V × V) := (Lines ×ˢ Lines).filter (fun p => Γ.dist p.1 p.2 = 4)
  have hcoe : (PairF : Set (V × V)) =
      {p : V × V | c p.1 = 1 ∧ c p.2 = 1 ∧ Γ.dist p.1 p.2 = 4} := by
    ext p
    simp only [PairF, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Lines,
      mem_lineFinset, Set.mem_setOf_eq]
    tauto
  have hmap : (PairF : Set (V × V)).MapsTo Prod.fst (Lines : Set V) := by
    intro p hp
    simp only [Finset.mem_coe, PairF, Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.1
  have hsum := Finset.card_eq_sum_card_fiberwise (s := PairF) (t := Lines)
    (f := Prod.fst) hmap
  have hfiber : ∀ L ∈ Lines, (PairF.filter (fun p => p.1 = L)).card = q ^ 8 := by
    intro L hL
    have hL1 : c L = 1 := by simpa [Lines] using hL
    have hfilter : PairF.filter (fun p => p.1 = L) =
        (Lines.filter (fun M => Γ.dist L M = 4)).image (fun M => (L, M)) := by
      ext p
      constructor
      · intro hp
        simp only [Finset.mem_filter, Finset.mem_image, PairF, Finset.mem_product] at hp ⊢
        obtain ⟨⟨⟨hp1, hp2⟩, hdist⟩, hfirst⟩ := hp
        subst hfirst
        exact ⟨p.2, ⟨hp2, hdist⟩, rfl⟩
      · intro hp
        simp only [Finset.mem_filter, Finset.mem_image, PairF, Finset.mem_product] at hp ⊢
        obtain ⟨M, ⟨hMmem, hdist⟩, rfl⟩ := hp
        exact ⟨⟨⟨hL, hMmem⟩, hdist⟩, rfl⟩
    rw [hfilter, Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)]
    have hcardset : (Lines.filter (fun M => Γ.dist L M = 4)).card
        = {M : V | c M = 1 ∧ Γ.dist L M = 4}.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext M
      simp only [Finset.mem_coe, Finset.mem_filter, Lines, mem_lineFinset,
        Set.mem_setOf_eq]
    rw [hcardset]
    exact ncard_opposite_lines hΓ hL1
  rw [← hcoe, Set.ncard_coe_finset, hsum, Finset.sum_congr rfl hfiber, Finset.sum_const,
    smul_eq_mul, hLinesCard]


private lemma cast_R {q : ℕ} (hq : 2 ≤ q) :
    ((q ^ 8 - q ^ 7 + q ^ 6 - q ^ 5 + q ^ 4 : ℕ) : ℤ)
      = (q : ℤ) ^ 8 - (q : ℤ) ^ 7 + (q : ℤ) ^ 6 - (q : ℤ) ^ 5 + (q : ℤ) ^ 4 := by
  have h1 : q ^ 7 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hq5q7 : q ^ 5 ≤ q ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hq7 : q ^ 7 + q ^ 7 ≤ q ^ 8 := by
    have h2 : q ^ 7 + q ^ 7 = 2 * q ^ 7 := by ring
    rw [h2]
    calc 2 * q ^ 7 = q ^ 7 * 2 := by ring
      _ ≤ q ^ 7 * q := Nat.mul_le_mul_left _ (by omega)
      _ = q ^ 8 := by ring
  have hsub1 : q ^ 5 ≤ q ^ 8 - q ^ 7 := by omega
  have hsub2 : q ^ 5 ≤ q ^ 8 - q ^ 7 + q ^ 6 := le_trans hsub1 (Nat.le_add_right _ _)
  rw [Nat.cast_add, Nat.cast_sub hsub2, Nat.cast_add, Nat.cast_sub h1]
  push_cast
  ring

private theorem card_fullSubquadrangles (hΓ : IsThasQuadrangle Γ c q) :
    {E : Set V | IsFullSubquadrangle c E q}.ncard =
      q ^ 8 - q ^ 7 + q ^ 6 - q ^ 5 + q ^ 4 := by
  classical
  let Sq : Set (Set V) := {E | IsFullSubquadrangle c E q}
  let SqF : Finset (Set V) := (Set.toFinite Sq).toFinset
  let Pairs : Set (V × V) := {p | c p.1 = 1 ∧ c p.2 = 1 ∧ Γ.dist p.1 p.2 = 4}
  let PairsF : Finset (V × V) := (Set.toFinite Pairs).toFinset
  let SetPair : Set V → Set (V × V) := fun E =>
    {p | p.1 ∈ subquadrangleLines Γ c E ∧ p.2 ∈ subquadrangleLines Γ c E ∧
      Γ.dist p.1 p.2 = 4}
  let PairFin : Set V → Finset (V × V) := fun E => (Set.toFinite (SetPair E)).toFinset
  let Total : Finset (Set V × (V × V)) :=
    SqF.biUnion (fun E => (PairFin E).image (fun p => (E, p)))
  have hSq_mem : ∀ E, E ∈ SqF ↔ IsFullSubquadrangle c E q := by
    intro E
    simp [SqF, Sq]
  have hPairs_mem : ∀ p, p ∈ PairsF ↔ c p.1 = 1 ∧ c p.2 = 1 ∧ Γ.dist p.1 p.2 = 4 := by
    intro p
    simp [PairsF, Pairs]
  have hPairFin_mem : ∀ E p, p ∈ PairFin E ↔ p ∈ SetPair E := by
    intro E p
    simp only [PairFin, Set.Finite.mem_toFinset]
  have hTotal_mem : ∀ E p, (E, p) ∈ Total ↔ E ∈ SqF ∧ p ∈ PairFin E := by
    intro E p
    simp only [Total, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨E₀, hE₀, p₀, hp₀, hEq⟩
      simp only [Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      exact ⟨hE₀, hp₀⟩
    · rintro ⟨hE, hp⟩
      exact ⟨E, hE, p, hp, rfl⟩
  have hfiber : ∀ E ∈ SqF, ((PairFin E).image (fun p => (E, p))).card =
      (q + 1) * (q ^ 3 + 1) * q ^ 4 := by
    intro E hE
    have hF : IsFullSubquadrangle c E q := (hSq_mem E).mp hE
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    have hcard := Set.ncard_eq_toFinset_card (SetPair E) (Set.toFinite (SetPair E))
    rw [← hcard]
    exact card_pairs_in_subquadrangle hΓ hF
  have hdisj : (SqF : Set (Set V)).PairwiseDisjoint
      (fun E => (PairFin E).image (fun p => (E, p))) := by
    intro E hE E' hE' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_image] at hz hz'
    obtain ⟨p, -, hp⟩ := hz
    obtain ⟨p', -, hp'⟩ := hz'
    have h1 : E = z.1 := by simpa using congrArg Prod.fst hp
    have h2 : E' = z.1 := by simpa using congrArg Prod.fst hp'
    exact hne (h1.trans h2.symm)
  have hTotalCard : Total.card = SqF.card * ((q + 1) * (q ^ 3 + 1) * q ^ 4) := by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
    · exact hdisj
  have hinj : Set.InjOn Prod.snd (Total : Set (Set V × (V × V))) := by
    rintro ⟨E, p⟩ hz ⟨E', p'⟩ hz' hsnd
    simp only [Finset.mem_coe] at hz hz'
    rw [hTotal_mem] at hz hz'
    have hsnd' : p = p' := by simpa using hsnd
    subst hsnd'
    have hpE : p ∈ SetPair E := (hPairFin_mem E p).mp hz.2
    have hpE' : p ∈ SetPair E' := (hPairFin_mem E' p).mp hz'.2
    have hE1 : c p.1 = 1 := (mem_subquadrangleLines.mp hpE.1).1
    have hdist : Γ.dist p.1 p.2 = 4 := hpE.2.2
    obtain ⟨E₀, ⟨hF₀, hL₀, hM₀⟩, huniq⟩ := existsUnique_fullSubquadrangle hΓ hE1 hdist
    have hEeq : E = E₀ :=
      huniq E ⟨(hSq_mem E).mp hz.1, (mem_subquadrangleLines.mp hpE.1).2,
        (mem_subquadrangleLines.mp hpE.2.1).2⟩
    have hE'eq : E' = E₀ :=
      huniq E' ⟨(hSq_mem E').mp hz'.1, (mem_subquadrangleLines.mp hpE'.1).2,
        (mem_subquadrangleLines.mp hpE'.2.1).2⟩
    rw [hEeq, hE'eq]
  have himage : Total.image Prod.snd = PairsF := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_image] at hp
      obtain ⟨z, hz, hzp⟩ := hp
      rcases z with ⟨E, q'⟩
      have hzp' : q' = p := by simpa using hzp
      rw [hTotal_mem] at hz
      have hq' : q' ∈ SetPair E := (hPairFin_mem E q').mp hz.2
      rw [hzp'] at hq'
      exact (hPairs_mem p).mpr
        ⟨(mem_subquadrangleLines.mp hq'.1).1, (mem_subquadrangleLines.mp hq'.2.1).1,
          hq'.2.2⟩
    · intro hp
      rw [hPairs_mem] at hp
      obtain ⟨h1, h2, hdist⟩ := hp
      obtain ⟨E, ⟨hF, hL, hM⟩, -⟩ := existsUnique_fullSubquadrangle hΓ h1 hdist
      have hE : E ∈ SqF := (hSq_mem E).mpr hF
      have hpE : p ∈ SetPair E :=
        ⟨mem_subquadrangleLines.mpr ⟨h1, hL⟩, mem_subquadrangleLines.mpr ⟨h2, hM⟩, hdist⟩
      have hpF : p ∈ PairFin E := (hPairFin_mem E p).mpr hpE
      exact Finset.mem_image.mpr ⟨(E, p), (hTotal_mem E p).mpr ⟨hE, hpF⟩, rfl⟩
  have hTotalSnd : Total.card = PairsF.card := by
    rw [← himage]
    exact (Finset.card_image_of_injOn hinj).symm
  have hPairsCard : PairsF.card = (q ^ 3 + 1) * (q ^ 5 + 1) * q ^ 8 := by
    have hcard := Set.ncard_eq_toFinset_card Pairs (Set.toFinite Pairs)
    rw [← hcard]
    exact card_pairs_all hΓ
  have hperpos : 0 < (q + 1) * (q ^ 3 + 1) * q ^ 4 := by
    have hq : 0 < q := by have := hΓ.two_le; omega
    positivity
  have hmain : ((q ^ 8 - q ^ 7 + q ^ 6 - q ^ 5 + q ^ 4) *
      ((q + 1) * (q ^ 3 + 1) * q ^ 4) = (q ^ 3 + 1) * (q ^ 5 + 1) * q ^ 8) := by
    set R : ℕ := q ^ 8 - q ^ 7 + q ^ 6 - q ^ 5 + q ^ 4 with hR
    have hRcast : (R : ℤ) = (q : ℤ) ^ 8 - (q : ℤ) ^ 7 + (q : ℤ) ^ 6 -
        (q : ℤ) ^ 5 + (q : ℤ) ^ 4 := by
      rw [hR]
      exact cast_R hΓ.two_le
    have hpercast : (((q + 1) * (q ^ 3 + 1) * q ^ 4 : ℕ) : ℤ)
        = ((q : ℤ) + 1) * ((q : ℤ) ^ 3 + 1) * (q : ℤ) ^ 4 := by
      push_cast
      ring
    have htotalcast : (((q ^ 3 + 1) * (q ^ 5 + 1) * q ^ 8 : ℕ) : ℤ)
        = ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 5 + 1) * (q : ℤ) ^ 8 := by
      push_cast
      ring
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_mul, hRcast, hpercast, htotalcast]
    ring
  have hSqF : SqF.card = q ^ 8 - q ^ 7 + q ^ 6 - q ^ 5 + q ^ 4 := by
    apply Nat.eq_of_mul_eq_mul_right hperpos
    rw [← hTotalCard, hTotalSnd, hPairsCard]
    exact hmain.symm
  change Sq.ncard = q ^ 8 - q ^ 7 + q ^ 6 - q ^ 5 + q ^ 4
  have hcard := Set.ncard_eq_toFinset_card Sq (Set.toFinite Sq)
  rw [hcard]
  simpa [SqF] using hSqF


private theorem ncard_abs_threespaces (hΓ : IsThasQuadrangle Γ c q) :
    {E : Set V | ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}}.ncard
      = (q ^ 2 + 1) * (q ^ 5 + 1) := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  let f : V → Set V := fun x => ptPerp Γ c {x}
  have hset : {E : Set V | ∃ x, c x = 0 ∧ E = f x} = f '' (pointFinset c : Set V) := by
    ext E
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, mem_pointFinset.mpr hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, mem_pointFinset.mp hx, rfl⟩
  have hinj : Set.InjOn f (pointFinset c : Set V) := by
    intro x hx y hy hxy
    exact ptPerp_singleton_injective hP hT (mem_pointFinset.mp hx) (mem_pointFinset.mp hy) hxy
  rw [hset, Set.InjOn.ncard_image hinj, Set.ncard_coe_finset,
    card_pointFinset hP hT c (s := q ^ 2) (t := q ^ 3) hΓ.deg]
  ring

private lemma ncard_sum_arith {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 2 + 1) * (q ^ 5 + 1) + (q ^ 8 - q ^ 7 + q ^ 6 - q ^ 5 + q ^ 4)
      = q ^ 8 + q ^ 6 + q ^ 4 + q ^ 2 + 1 := by
  set R : ℕ := q ^ 8 - q ^ 7 + q ^ 6 - q ^ 5 + q ^ 4 with hR
  have hRcast : (R : ℤ) = (q : ℤ) ^ 8 - (q : ℤ) ^ 7 + (q : ℤ) ^ 6 -
      (q : ℤ) ^ 5 + (q : ℤ) ^ 4 := by
    rw [hR]
    exact cast_R hq
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_add, hRcast]
  push_cast
  ring

theorem ncard_threespaces (hΓ : IsThasQuadrangle Γ c q) :
    {E | IsThreespace Γ c q E}.ncard = q ^ 8 + q ^ 6 + q ^ 4 + q ^ 2 + 1 := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  let Abs : Set (Set V) := {E | ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}}
  let Sub : Set (Set V) := {E | IsFullSubquadrangle c E q}
  have hUnion : {E | IsThreespace Γ c q E} = Abs ∪ Sub := by
    ext E
    constructor
    · intro hE
      rcases hE with ⟨x, hx, rfl⟩ | hF
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr hF
    · rintro (hE | hE)
      · obtain ⟨x, hx, hE⟩ := hE
        exact Or.inl ⟨x, hx, hE⟩
      · exact Or.inr hE
  have hdisj : Disjoint Abs Sub := by
    rw [Set.disjoint_left]
    rintro E ⟨x, hx, rfl⟩ hF
    have h1 : (ptPerp Γ c {x}).ncard = q ^ 5 + q ^ 2 + 1 := by
      rw [ncard_ptPerp_singleton hP hT c (s := q ^ 2) (t := q ^ 3) hΓ.deg hx]
      ring
    have h2 : (ptPerp Γ c {x}).ncard = (q ^ 2 + 1) * (q ^ 3 + 1) := by
      rw [ncard_of_isFullSubquadrangle hP hT c (s := q ^ 2) (t := q ^ 3) hΓ.deg hF]
      ring
    rw [h1] at h2
    have hq : 0 < q := by have := hΓ.two_le; omega
    have hq3 : 0 < q ^ 3 := by positivity
    have h3 : (q ^ 2 + 1) * (q ^ 3 + 1) = q ^ 5 + q ^ 3 + q ^ 2 + 1 := by ring
    rw [h3] at h2
    omega
  rw [hUnion, Set.ncard_union_eq hdisj, ncard_abs_threespaces hΓ,
    card_fullSubquadrangles hΓ]
  exact ncard_sum_arith hΓ.two_le


end CFSG.Geometry.GeneralizedQuadrangles
