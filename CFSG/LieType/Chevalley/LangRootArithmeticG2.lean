module

public import CFSG.LieType.Chevalley.GraphFixedF4Intertwiner
public import CFSG.LieType.Chevalley.RootOps.Cert.G2Simple
public import CFSG.LieType.Chevalley.RootOps.Cert.G2Tab

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps

section Forms

variable {L : Type*} [Field L]

@[expose] def formEval (x : ℕ → L) (e : List (ℕ × ℤ)) : L :=
  (e.map fun vc => (vc.2 : L) * x vc.1).sum

@[expose] def formCoeff (u : ℕ) (e : List (ℕ × ℤ)) : ℤ :=
  (e.map fun vc => if vc.1 = u then vc.2 else 0).sum

@[expose] def formLam (lam : ℕ → ℤ) (e : List (ℕ × ℤ)) : ℤ :=
  (e.map fun vc => vc.2 * lam vc.1).sum

theorem formEval_eq (x : ℕ → L) (lam : ℕ → ℤ) (u : ℕ) (e : List (ℕ × ℤ))
    (h : ∀ vc ∈ e, vc.1 = u ∨ (vc.2 : L) = 0 ∨ x vc.1 = (lam vc.1 : L) * x 0) :
    formEval x e = (formCoeff u e : L) * x u +
      ((formLam lam e - formCoeff u e * lam u : ℤ) : L) * x 0 := by
  induction e with
  | nil => simp [formEval, formCoeff, formLam]
  | cons vc e ih =>
    obtain ⟨v, c⟩ := vc
    have ih' := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    simp only [formEval, formCoeff, formLam, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih']
    by_cases hvu : v = u
    · subst hvu
      simp only [↓reduceIte]
      push_cast
      ring
    · simp only [hvu, ↓reduceIte]
      rcases h (v, c) List.mem_cons_self with h1 | h1 | h1
      · exact absurd h1 hvu
      · simp only at h1
        push_cast
        rw [h1]
        ring
      · simp only at h1
        push_cast
        rw [h1]
        ring

@[expose] def stepOk (lam : ℕ → ℤ) (D : List ℕ) (u : ℕ) (e : List (ℕ × ℤ)) : Bool :=
  (e.all fun vc => vc.1 == u || vc.2 % 3 == 0 || D.contains vc.1) &&
    (formCoeff u e % 3 != 0) && (formLam lam e % 3 == 0)

theorem eq_of_stepOk [CharP L 3] {lam : ℕ → ℤ} {D : List ℕ} {u : ℕ} {e : List (ℕ × ℤ)}
    (x : ℕ → L) (h : stepOk lam D u e = true) (hD : ∀ v ∈ D, x v = (lam v : L) * x 0)
    (he : formEval x e = 0) : x u = (lam u : L) * x 0 := by
  simp only [stepOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hall, hu⟩, hlam⟩ := h
  have hcast : ∀ z : ℤ, z % 3 = 0 → (z : L) = 0 := fun z hz =>
    (CharP.intCast_eq_zero_iff L 3 z).2 (Int.dvd_of_emod_eq_zero hz)
  rw [formEval_eq x lam u e fun vc hvc => by
    rcases hall vc hvc with (h1 | h1) | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl (hcast _ h1))
    · exact Or.inr (Or.inr (hD _ h1))] at he
  have hu0 : (formCoeff u e : L) ≠ 0 := fun h0 =>
    hu (Int.emod_eq_zero_of_dvd ((CharP.intCast_eq_zero_iff L 3 _).1 h0))
  push_cast at he
  rw [hcast _ hlam] at he
  refine mul_left_cancel₀ hu0 ?_
  linear_combination he

@[expose] def stepsOk (lam : ℕ → ℤ) (form : ℕ → ℕ → ℕ → List (ℕ × ℤ)) (n : ℕ) :
    List ℕ → List (ℕ × ℕ × ℕ × ℕ) → Bool
  | D, [] => (List.range n).all fun u => D.contains u
  | D, (u, g, p, q) :: rest =>
    decide (g < 4 ∧ p < 14 ∧ q < 14) && stepOk lam D u (form g p q) &&
      stepsOk lam form n (u :: D) rest

theorem stepsOk_sound [CharP L 3] {lam : ℕ → ℤ} {form : ℕ → ℕ → ℕ → List (ℕ × ℤ)} {n : ℕ}
    (x : ℕ → L) (hform : ∀ g p q, g < 4 → p < 14 → q < 14 → formEval x (form g p q) = 0) :
    ∀ (D : List ℕ) (steps : List (ℕ × ℕ × ℕ × ℕ)), stepsOk lam form n D steps = true →
      (∀ v ∈ D, x v = (lam v : L) * x 0) → ∀ u < n, x u = (lam u : L) * x 0
  | D, [], h, hD => fun u hu => by
    simp only [stepsOk, List.all_eq_true, List.mem_range, List.contains_iff_mem] at h
    exact hD u (h u hu)
  | D, (u, g, p, q) :: rest, h, hD => by
    simp only [stepsOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hg, hp, hq⟩, hs⟩, hrest⟩ := h
    have hu := eq_of_stepOk x hs hD (hform g p q hg hp hq)
    refine stepsOk_sound x hform (u :: D) rest hrest fun v hv => ?_
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hu
    · exact hD v hv

end Forms

section G2

@[expose] def g2GenY (g : ℕ) : Bool :=
  g % 2 == 1

@[expose] def g2GenI (g : ℕ) : Fin Tag.G2.rank :=
  ⟨g / 2 % 2, Nat.mod_lt _ two_pos⟩

variable (L : Type) [Field L]

@[expose] def g2Gen (g : ℕ) : Module.End L (RootModule Tag.G2 L) :=
  if g2GenY g then yOp Tag.G2 L (g2GenI g) 1 else xOp Tag.G2 L (g2GenI g) 1

@[expose] def g2NilCol (g q : ℕ) : List (ℕ × ℤ) :=
  (List.range 3).flatMap fun k => coeffVec .G2 (g2GenY g) (g2GenI g) (k + 1) [(q, 1)]

theorem simpleRow_G2
    (j : Fin Tag.G2.rank) : simpleRow .G2 j = true := by
  fin_cases j
  exacts [g2_simpleRow_0, g2_simpleRow_1]

theorem g2Gen_eq_sum (g : ℕ) :
    g2Gen L g = ∑ k ∈ Finset.range 4, coeffOp Tag.G2 L (g2GenY g) (g2GenI g) k := by
  unfold g2Gen coeffOp
  cases g2GenY g
  · simp only [Bool.false_eq_true, ↓reduceIte, xOp_eq_sum_xCoeff, one_pow, one_smul]
  · simp only [↓reduceIte, yOp_eq_sum_yCoeff, one_pow, one_smul]

theorem coeffOp_zero
    (y : Bool) (i : Fin Tag.G2.rank) : coeffOp Tag.G2 L y i 0 = 1 := by
  cases y
  · exact xCoeff_zero i
  · exact yCoeff_zero i

theorem validVec_g2NilCol
    (g : ℕ) {q : ℕ} (hq : q < dim Tag.G2) :
    ValidVec Tag.G2 (g2NilCol g q) := by
  intro x hx
  obtain ⟨k, hk, hxk⟩ := List.mem_flatMap.1 hx
  exact (coeffOp_vecOf (k := k + 1) simpleRow_G2 g2_allValid ℤ _ _
    (by have := List.mem_range.1 hk; omega) (validVec_single hq)).2 x hxk

theorem g2Gen_posVec
    (g : ℕ) {q : ℕ} (hq : q < dim Tag.G2) :
    g2Gen L g (posVec Tag.G2 L q) = posVec Tag.G2 L q + vecOf Tag.G2 L (g2NilCol g q) := by
  rw [g2Gen_eq_sum, LinearMap.sum_apply, Finset.sum_range_succ', coeffOp_zero, Module.End.one_apply,
    add_comm, g2NilCol, vecOf_flatMap_range]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [posVec_eq_vecOf_single]
  exact (coeffOp_vecOf (k := k + 1) simpleRow_G2 g2_allValid L _ _
    (by have := Finset.mem_range.1 hk; omega) (validVec_single hq)).1

@[expose] def coefAt (p : ℕ) (v : List (ℕ × ℤ)) : ℤ :=
  (v.map fun rz => if rz.1 = p then rz.2 else 0).sum

@[expose] def g2Form (g p q : ℕ) : List (ℕ × ℤ) :=
  (g2NilCol g q).map (fun rz => (14 * p + rz.1, rz.2)) ++
    (List.range 14).map fun r => (14 * r + q, -coefAt p (g2NilCol g r))

variable {L}

theorem dim_G2 : dim Tag.G2 = 14 :=
  rfl

theorem posCoord_vecOf
    (p : ℕ) {v : List (ℕ × ℤ)} (hv : ValidVec Tag.G2 v) :
    posCoord Tag.G2 L p (vecOf Tag.G2 L v) = (coefAt p v : L) := by
  induction v with
  | nil => simp [coefAt]
  | cons x v ih =>
    rw [vecOf_cons, map_add, map_smul, posCoord_posVec (hv x List.mem_cons_self),
      ih fun y hy => hv y (List.mem_cons_of_mem _ hy)]
    simp only [coefAt, List.map_cons, List.sum_cons, smul_eq_mul]
    split_ifs with h1 h2 h2
    · push_cast; ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · push_cast; ring

theorem map_vecOf
    (M : Module.End L (RootModule Tag.G2 L)) (v : List (ℕ × ℤ)) :
    M (vecOf Tag.G2 L v) = (v.map fun x => (x.2 : L) • M (posVec Tag.G2 L x.1)).sum := by
  induction v with
  | nil => simp
  | cons x v ih => rw [vecOf_cons, map_add, map_smul, ih, List.map_cons, List.sum_cons]

theorem eq_sum_posCoord_smul_posVec
    (w : RootModule Tag.G2 L) :
    w = ∑ p ∈ Finset.range 14, posCoord Tag.G2 L p w • posVec Tag.G2 L p := by
  rw [← dim_G2]
  ext b
  obtain ⟨p0, hp0, rfl⟩ := posLabel_surjective b
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single p0]
  · rw [Finsupp.smul_apply, posVec_eq_single hp0, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    simp only [posCoord, hp0, ↓reduceDIte, Finsupp.lapply_apply]
  · intro p hp hne
    rw [Finsupp.smul_apply, posVec_eq_single (Finset.mem_range.1 hp),
      Finsupp.single_eq_of_ne' fun h => hne (posLabel_injective _ _ h), smul_zero]
  · exact fun h => absurd (Finset.mem_range.2 hp0) h

@[expose] def g2Entries
    (M : Module.End L (RootModule Tag.G2 L)) (u : ℕ) : L :=
  posCoord Tag.G2 L (u / 14) (M (posVec Tag.G2 L (u % 14)))

theorem g2Entries_apply
    (M : Module.End L (RootModule Tag.G2 L)) {a b : ℕ} (hb : b < 14) :
    g2Entries M (14 * a + b) = posCoord Tag.G2 L a (M (posVec Tag.G2 L b)) := by
  have h1 : (14 * a + b) / 14 = a := by omega
  have h2 : (14 * a + b) % 14 = b := by omega
  simp only [g2Entries, h1, h2]

theorem formEval_append (x : ℕ → L) (e e' : List (ℕ × ℤ)) :
    formEval x (e ++ e') = formEval x e + formEval x e' := by
  simp only [formEval, List.map_append, List.sum_append]

theorem sum_range_eq_list_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ r ∈ Finset.range n, f r = ((List.range n).map f).sum :=
  rfl

theorem formEval_g2Form
    (M : Module.End L (RootModule Tag.G2 L)) {g : ℕ}
    (hM : Commute M (g2Gen L g)) {p q : ℕ} (hp : p < 14) (hq : q < 14) :
    formEval (g2Entries M) (g2Form g p q) = 0 := by
  have hq' : q < dim Tag.G2 := hq
  set c : ℕ → L := fun r => posCoord Tag.G2 L r (M (posVec Tag.G2 L q)) with hc
  have hL : posCoord Tag.G2 L p (M (g2Gen L g (posVec Tag.G2 L q))) =
      c p + formEval (g2Entries M) ((g2NilCol g q).map fun rz => (14 * p + rz.1, rz.2)) := by
    rw [g2Gen_posVec L g hq', map_add, map_add, map_vecOf, map_list_sum, formEval, List.map_map,
      List.map_map]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
    simp only [Function.comp_apply, map_smul, smul_eq_mul]
    rw [g2Entries_apply M (validVec_g2NilCol g hq' x hx)]
  have hR : posCoord Tag.G2 L p (g2Gen L g (M (posVec Tag.G2 L q))) =
      c p + ∑ r ∈ Finset.range 14, c r * (coefAt p (g2NilCol g r) : L) := by
    conv_lhs => rw [eq_sum_posCoord_smul_posVec (M (posVec Tag.G2 L q))]
    rw [map_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl fun r hr => by
      rw [g2Gen_posVec L g (Finset.mem_range.1 hr), map_add,
        posCoord_vecOf p (validVec_g2NilCol g (Finset.mem_range.1 hr)),
        posCoord_posVec (Finset.mem_range.1 hr), mul_add],
      Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single p (fun r _ hr => by simp [Ne.symm hr])
      (fun h => absurd (Finset.mem_range.2 hp) h)]
    simp [hc]
  have h2 : formEval (g2Entries M) ((List.range 14).map fun r =>
      (14 * r + q, -coefAt p (g2NilCol g r))) =
      -∑ r ∈ Finset.range 14, c r * (coefAt p (g2NilCol g r) : L) := by
    rw [← Finset.sum_neg_distrib, sum_range_eq_list_sum, formEval, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
    simp only [Function.comp_apply]
    rw [g2Entries_apply M hq]
    push_cast
    ring
  have hcomm := congrArg (fun A : Module.End L (RootModule Tag.G2 L) =>
    posCoord Tag.G2 L p (A (posVec Tag.G2 L q))) hM.eq
  simp only [Module.End.mul_apply] at hcomm
  rw [hL, hR] at hcomm
  rw [g2Form, formEval_append, h2]
  linear_combination hcomm

@[expose] def g2Lam (u : ℕ) : ℤ :=
  if u / 14 = u % 14 then 1 else 0

@[expose] def g2Steps : List (ℕ × ℕ × ℕ × ℕ) :=
  [(57, 0, 0, 1), (58, 0, 0, 2), (62, 0, 0, 6), (63, 0, 0, 7), (64, 0, 0, 8), (65, 0, 0, 9),
    (66, 0, 0, 10), (69, 0, 0, 13), (16, 0, 1, 0), (20, 0, 1, 3), (14, 0, 1, 4), (23, 0, 1, 5),
    (21, 0, 1, 11), (22, 0, 1, 12), (1, 0, 2, 1), (2, 0, 2, 2), (6, 0, 2, 6), (7, 0, 2, 7),
    (8, 0, 2, 8), (9, 0, 2, 9), (10, 0, 2, 10), (13, 0, 2, 13), (44, 0, 3, 0), (48, 0, 3, 3),
    (42, 0, 3, 4), (51, 0, 3, 5), (49, 0, 3, 11), (50, 0, 3, 12), (56, 0, 4, 4), (72, 0, 5, 0),
    (76, 0, 5, 3), (70, 0, 5, 4), (79, 0, 5, 5), (77, 0, 5, 11), (78, 0, 5, 12), (86, 0, 6, 0),
    (43, 0, 6, 1), (52, 0, 6, 10), (55, 0, 6, 13), (155, 0, 7, 1), (156, 0, 7, 2),
    (160, 0, 7, 6), (161, 0, 7, 7), (162, 0, 7, 8), (163, 0, 7, 9), (164, 0, 7, 10),
    (167, 0, 7, 13), (169, 0, 8, 1), (170, 0, 8, 2), (174, 0, 8, 6), (175, 0, 8, 7),
    (176, 0, 8, 8), (177, 0, 8, 9), (178, 0, 8, 10), (181, 0, 8, 13), (128, 0, 9, 0),
    (71, 0, 9, 1), (80, 0, 9, 10), (83, 0, 9, 13), (142, 0, 10, 0), (146, 0, 10, 3),
    (140, 0, 10, 4), (149, 0, 10, 5), (147, 0, 10, 11), (148, 0, 10, 12), (154, 0, 11, 4),
    (168, 0, 12, 4), (184, 0, 13, 0), (188, 0, 13, 3), (182, 0, 13, 4), (191, 0, 13, 5),
    (189, 0, 13, 11), (190, 0, 13, 12), (29, 1, 0, 1), (31, 1, 0, 3), (32, 1, 0, 4),
    (33, 1, 0, 5), (38, 1, 0, 10), (39, 1, 0, 11), (40, 1, 0, 12), (41, 1, 0, 13), (18, 1, 1, 0),
    (17, 1, 1, 6), (25, 1, 1, 7), (26, 1, 1, 8), (19, 1, 1, 9), (28, 1, 2, 2), (85, 1, 3, 1),
    (46, 1, 3, 2), (87, 1, 3, 3), (88, 1, 3, 4), (89, 1, 3, 5), (94, 1, 3, 10), (95, 1, 3, 11),
    (96, 1, 3, 12), (97, 1, 3, 13), (60, 1, 4, 0), (30, 1, 4, 2), (3, 1, 4, 3), (4, 1, 4, 4),
    (5, 1, 4, 5), (11, 1, 4, 11), (12, 1, 4, 12), (127, 1, 5, 1), (74, 1, 5, 2), (129, 1, 5, 3),
    (130, 1, 5, 4), (131, 1, 5, 5), (136, 1, 5, 10), (137, 1, 5, 11), (138, 1, 5, 12),
    (139, 1, 5, 13), (84, 1, 6, 2), (102, 1, 7, 0), (98, 1, 7, 2), (101, 1, 7, 6),
    (109, 1, 7, 7), (110, 1, 7, 8), (103, 1, 7, 9), (116, 1, 8, 0), (112, 1, 8, 2),
    (115, 1, 8, 6), (123, 1, 8, 7), (124, 1, 8, 8), (117, 1, 8, 9), (126, 1, 9, 2),
    (144, 1, 10, 0), (143, 1, 10, 6), (151, 1, 10, 7), (152, 1, 10, 8), (145, 1, 10, 9),
    (158, 1, 11, 0), (99, 1, 11, 1), (100, 1, 11, 2), (108, 1, 11, 10), (111, 1, 11, 13),
    (172, 1, 12, 0), (113, 1, 12, 1), (114, 1, 12, 2), (122, 1, 12, 10), (125, 1, 12, 13),
    (186, 1, 13, 0), (185, 1, 13, 6), (193, 1, 13, 7), (194, 1, 13, 8), (187, 1, 13, 9),
    (24, 2, 1, 2), (104, 2, 1, 6), (107, 2, 1, 9), (34, 2, 2, 2), (45, 2, 3, 0), (15, 2, 3, 1),
    (47, 2, 3, 2), (105, 2, 3, 7), (59, 2, 4, 0), (61, 2, 4, 2), (118, 2, 4, 6), (119, 2, 4, 7),
    (121, 2, 4, 9), (67, 2, 4, 13), (73, 2, 5, 0), (75, 2, 5, 2), (35, 2, 5, 7), (37, 2, 5, 9),
    (81, 2, 5, 13), (90, 2, 6, 2), (36, 2, 6, 8), (132, 2, 9, 2), (150, 2, 10, 2),
    (93, 2, 10, 9), (157, 2, 11, 0), (183, 2, 11, 1), (159, 2, 11, 2), (192, 2, 11, 10),
    (171, 2, 12, 0), (173, 2, 12, 2), (179, 2, 12, 8), (27, 3, 1, 4), (53, 3, 1, 11),
    (54, 3, 1, 12), (82, 3, 2, 12), (91, 3, 6, 0), (141, 3, 6, 1), (92, 3, 6, 4),
    (153, 3, 6, 13), (106, 3, 7, 4), (120, 3, 8, 4), (68, 3, 8, 12), (133, 3, 9, 0),
    (134, 3, 9, 4), (165, 3, 11, 4), (195, 3, 13, 4), (166, 3, 13, 12), (180, 0, 8, 12),
    (135, 0, 9, 5)]

theorem stepsOk_g2Steps : stepsOk g2Lam g2Form 196 [0] g2Steps = true := by
  decide +kernel

theorem eq_smul_one_of_commute_g2Gen
    [CharP L 3] (M : Module.End L (RootModule Tag.G2 L))
    (hM : ∀ g, g < 4 → Commute M (g2Gen L g)) :
    M = g2Entries M 0 • (1 : Module.End L (RootModule Tag.G2 L)) := by
  have hsol := stepsOk_sound (g2Entries M) (fun g p q hg hp hq => formEval_g2Form M (hM g hg) hp hq)
    [0] g2Steps stepsOk_g2Steps (fun v hv => by
      rw [List.mem_singleton.1 hv]
      simp [g2Lam])
  refine ext_posVec fun q hq => ?_
  have hq' : q < 14 := hq
  rw [eq_sum_posCoord_smul_posVec (M (posVec Tag.G2 L q))]
  rw [LinearMap.smul_apply, Module.End.one_apply]
  rw [Finset.sum_eq_single q]
  · have h := hsol (14 * q + q) (by omega)
    rw [g2Entries_apply M hq'] at h
    rw [h]
    simp only [g2Lam, show (14 * q + q) / 14 = q by omega, show (14 * q + q) % 14 = q by omega,
      ↓reduceIte, Int.cast_one, one_mul]
  · intro p hp hpq
    have h := hsol (14 * p + q) (by have := Finset.mem_range.1 hp; omega)
    rw [g2Entries_apply M hq'] at h
    rw [h]
    simp only [g2Lam, show (14 * p + q) / 14 = p by omega, show (14 * p + q) % 14 = q by omega,
      hpq, ↓reduceIte, Int.cast_zero, zero_mul, zero_smul]
  · exact fun h => absurd (Finset.mem_range.2 hq) h

variable (L) in
theorem G2_char_three_commutant
    (hL : ringChar L = 3) (M : Module.End L (RootModule Tag.G2 L)) :
    (Commute M (xOp Tag.G2 L ⟨0, by decide⟩ 1) ∧ Commute M (yOp Tag.G2 L ⟨0, by decide⟩ 1) ∧
        Commute M (xOp Tag.G2 L ⟨1, by decide⟩ 1) ∧ Commute M (yOp Tag.G2 L ⟨1, by decide⟩ 1)) ↔
      ∃ a : L, M = a • (1 : Module.End L (RootModule Tag.G2 L)) := by
  have : CharP L 3 := ringChar.of_eq hL
  refine ⟨fun ⟨hx0, hy0, hx1, hy1⟩ => ⟨_, eq_smul_one_of_commute_g2Gen M fun g hg => ?_⟩, ?_⟩
  · interval_cases g
    exacts [hx0, hy0, hx1, hy1]
  · rintro ⟨a, rfl⟩
    exact ⟨(Commute.one_left _).smul_left a, (Commute.one_left _).smul_left a,
      (Commute.one_left _).smul_left a, (Commute.one_left _).smul_left a⟩

end G2

end CFSG.LieType.Chevalley
