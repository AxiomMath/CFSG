module

public import CFSG.LieType.Chevalley.RootOps.Poly
public import CFSG.LieType.Chevalley.RootOps.CertTools

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

@[expose] def mulE (L L' : List Entry) : List Entry :=
  L'.flatMap fun y => (L.filter fun x => x.1 == y.2.1).map fun x => (y.1, x.2.1, x.2.2 * y.2.2)

@[expose] def smulE (s : ℤ) (L : List Entry) : List Entry :=
  L.map fun e => (e.1, e.2.1, s * e.2.2)

@[expose] def zeroE (L : List Entry) : Bool :=
  (canonE L).isEmpty

variable {τ : Tag} {R : Type*} [CommRing R]

theorem entriesOp_mul_single
    (L : List Entry) (y : Entry) (hy : y.2.1 < dim τ) :
    entriesOp τ R L * entriesOp τ R [y] = entriesOp τ R
      ((L.filter fun x => x.1 == y.2.1).map fun x => (y.1, x.2.1, x.2.2 * y.2.2)) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx : entriesOp τ R (x :: L) = entriesOp τ R [x] + entriesOp τ R L := by
      rw [← entriesOp_append]
      rfl
    rw [hx, add_mul, ih, entriesOp_single_mul_single x y hy, List.filter_cons]
    by_cases h : x.1 = y.2.1
    · simp only [h, beq_self_eq_true, ↓reduceIte, List.map_cons]
      rw [← entriesOp_append]
      rfl
    · have hb : (x.1 == y.2.1) = false := beq_eq_false_iff_ne.2 h
      simp only [h, hb, ↓reduceIte, zero_add, Bool.false_eq_true]

theorem entriesOp_mulE
    (L : List Entry) {L' : List Entry} (hL' : ValidEntries τ L') :
    entriesOp τ R (mulE L L') = entriesOp τ R L * entriesOp τ R L' := by
  induction L' with
  | nil => simp [mulE]
  | cons y L' ih =>
    rw [mulE, List.flatMap_cons, ← mulE, entriesOp_append,
      ih fun e he => hL' e (List.mem_cons_of_mem _ he),
      show y :: L' = [y] ++ L' from rfl, entriesOp_append, mul_add,
      entriesOp_mul_single L y (hL' y (List.mem_cons_self ..)).2]

theorem entriesOp_smulE
    (s : ℤ) (L : List Entry) :
    entriesOp τ R (smulE s L) = (s : R) • entriesOp τ R L :=
  entriesOp_map_smul s L

theorem entriesOp_eq_zero_of_zeroE
    {L : List Entry} (h : zeroE L = true) :
    entriesOp τ R L = 0 := by
  rw [← entriesOp_canonE, List.isEmpty_iff.1 h, entriesOp_nil]

theorem bracket_eq_of_zeroE
    {A B C : List Entry} (hA : ValidEntries τ A) (hB : ValidEntries τ B)
    {s : ℤ} (h : zeroE (mulE A B ++ smulE (-1) (mulE B A) ++ smulE s C) = true) :
    entriesOp τ R A * entriesOp τ R B - entriesOp τ R B * entriesOp τ R A =
      ((-s : ℤ) : R) • entriesOp τ R C := by
  have h0 := entriesOp_eq_zero_of_zeroE (τ := τ) (R := R) h
  rw [entriesOp_append, entriesOp_append, entriesOp_smulE, entriesOp_smulE, entriesOp_mulE _ hB,
    entriesOp_mulE _ hA] at h0
  push_cast at h0 ⊢
  calc entriesOp τ R A * entriesOp τ R B - entriesOp τ R B * entriesOp τ R A =
        (entriesOp τ R A * entriesOp τ R B + (-1 : R) • (entriesOp τ R B * entriesOp τ R A) +
          (s : R) • entriesOp τ R C) + (-(s : R)) • entriesOp τ R C := by module
    _ = (-(s : R)) • entriesOp τ R C := by
      rw [h0]
      exact zero_add _

theorem mul_comm_of_zeroE
    {A B : List Entry} (hA : ValidEntries τ A) (hB : ValidEntries τ B)
    (h : zeroE (mulE A B ++ smulE (-1) (mulE B A)) = true) :
    entriesOp τ R A * entriesOp τ R B = entriesOp τ R B * entriesOp τ R A := by
  have h0 := entriesOp_eq_zero_of_zeroE (τ := τ) (R := R) h
  rw [entriesOp_append, entriesOp_smulE, entriesOp_mulE _ hB, entriesOp_mulE _ hA] at h0
  push_cast at h0
  calc entriesOp τ R A * entriesOp τ R B =
        (entriesOp τ R A * entriesOp τ R B + (-1 : R) • (entriesOp τ R B * entriesOp τ R A)) +
          entriesOp τ R B * entriesOp τ R A := by module
    _ = entriesOp τ R B * entriesOp τ R A := by
      rw [h0]
      exact zero_add _

@[expose] def a2PairCheckAux (Ei Ej Fi Fj G G' : List Entry) (σ σ' : ℤ) : Bool :=
  zeroE (mulE Ei Ej ++ smulE (-1) (mulE Ej Ei) ++ smulE (-σ) G) &&
    zeroE (mulE Fi Fj ++ smulE (-1) (mulE Fj Fi) ++ smulE σ' G') &&
    zeroE (mulE Ei G ++ smulE (-1) (mulE G Ei)) &&
    zeroE (mulE Ej G ++ smulE (-1) (mulE G Ej)) &&
    zeroE (mulE Fi G' ++ smulE (-1) (mulE G' Fi)) &&
    zeroE (mulE Fj G' ++ smulE (-1) (mulE G' Fj))

@[expose] def a2PairCheck (τ : Tag) (i j : Fin τ.rank) : Bool :=
  a2PairCheckAux (entries τ i 1) (entries τ j 1) (entries τ (τ.rootCertificate.image i i) 1)
    (entries τ (τ.rootCertificate.image j j) 1) (entries τ (τ.rootCertificate.image j i) 1)
    (entries τ (τ.rootCertificate.image (τ.rootCertificate.image j j) i) 1) (signOf τ j i)
    (signOf τ (τ.rootCertificate.image j j) i)

@[expose] def a2CheckRow (τ : Tag) (i : Fin τ.rank) : Bool :=
  (List.finRange τ.rank).all fun j =>
    !(τ.cartan i j == -1 && τ.cartan j i == -1) || a2PairCheck τ i j

@[expose] def a2CheckAll (τ : Tag) : Bool :=
  (List.finRange τ.rank).all fun i => a2CheckRow τ i

theorem a2CheckAll_of_rows (h : ∀ i, a2CheckRow τ i = true) : a2CheckAll τ = true := by
  simp only [a2CheckAll, List.all_eq_true, List.mem_finRange, true_implies]
  exact h

theorem a2PairCheck_of_a2CheckAll (h : a2CheckAll τ = true) {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) : a2PairCheck τ i j = true := by
  simp only [a2CheckAll, a2CheckRow, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
  exact (h i j).resolve_left (by rintro (h' | h') <;> contradiction)

theorem val_lt_rootCertificate_length
    (j : Fin τ.rank) :
    (j : ℕ) < τ.rootCertificate.roots.length :=
  lt_of_lt_of_le j.2 rootCertificate_basis_table.1

theorem validEntries_entries_one
    (h : allValid τ = true) {a : ℕ}
    (ha : a < τ.rootCertificate.roots.length) : ValidEntries τ (entries τ a 1) :=
  validEntries_of_validB (validB_of_allValid h ha (by simp))

theorem entriesOp_entries_simple
    (hs : ∀ j, simpleRow τ j = true) (j : Fin τ.rank) :
    entriesOp τ R (entries τ j 1) = infE τ R j := by
  rw [entriesOp_eq_xCoeff (simpleRow_spec (hs j) le_rfl (by norm_num)).1, xCoeff_one]

theorem entriesOp_entries_neg_simple
    (hs : ∀ j, simpleRow τ j = true) (j : Fin τ.rank) :
    entriesOp τ R (entries τ (τ.rootCertificate.image j j) 1) = infF τ R j := by
  rw [entriesOp_eq_yCoeff (simpleRow_spec (hs j) le_rfl (by norm_num)).2, yCoeff_one]

theorem weylElt_mul_entriesOp_mul_inv
    (hd : DataChecks τ) {a : ℕ}
    (ha : a < τ.rootCertificate.roots.length) (i : Fin τ.rank) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * entriesOp τ R (entries τ a 1) *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R)) =
      (signOf τ a i : R) • entriesOp τ R (entries τ (τ.rootCertificate.image a i) 1) := by
  have h := conj_of_fingerCheck (R := R) hd.tab (validB_of_allValid hd.valid ha (by simp))
    (hd.conj a ha i 1 (by simp))
  rw [pow_one] at h
  rw [h, smul_mul_assoc, ← weylElt_inv, Units.mul_inv_cancel_right]

theorem brackets_of_a2PairCheck
    (hd : DataChecks τ) (hs : ∀ j, simpleRow τ j = true)
    {i j : Fin τ.rank} (h : a2PairCheck τ i j = true) :
    infE τ R i * infE τ R j - infE τ R j * infE τ R i =
        (signOf τ j i : R) • entriesOp τ R (entries τ (τ.rootCertificate.image j i) 1) ∧
      infF τ R i * infF τ R j - infF τ R j * infF τ R i =
        ((-signOf τ (τ.rootCertificate.image j j) i : ℤ) : R) • entriesOp τ R
          (entries τ (τ.rootCertificate.image (τ.rootCertificate.image j j) i) 1) ∧
      infE τ R i * entriesOp τ R (entries τ (τ.rootCertificate.image j i) 1) =
        entriesOp τ R (entries τ (τ.rootCertificate.image j i) 1) * infE τ R i ∧
      infE τ R j * entriesOp τ R (entries τ (τ.rootCertificate.image j i) 1) =
        entriesOp τ R (entries τ (τ.rootCertificate.image j i) 1) * infE τ R j ∧
      infF τ R i * entriesOp τ R
          (entries τ (τ.rootCertificate.image (τ.rootCertificate.image j j) i) 1) =
        entriesOp τ R (entries τ (τ.rootCertificate.image (τ.rootCertificate.image j j) i) 1) *
          infF τ R i ∧
      infF τ R j * entriesOp τ R
          (entries τ (τ.rootCertificate.image (τ.rootCertificate.image j j) i) 1) =
        entriesOp τ R (entries τ (τ.rootCertificate.image (τ.rootCertificate.image j j) i) 1) *
          infF τ R j := by
  simp only [a2PairCheck, a2PairCheckAux, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hi := val_lt_rootCertificate_length i
  have hj := val_lt_rootCertificate_length j
  have hi' := rootCertificate_image_lt hi i
  have hj' := rootCertificate_image_lt hj j
  have vEi := validEntries_entries_one hd.valid hi
  have vEj := validEntries_entries_one hd.valid hj
  have vFi := validEntries_entries_one hd.valid hi'
  have vFj := validEntries_entries_one hd.valid hj'
  have vG := validEntries_entries_one hd.valid (rootCertificate_image_lt hj i)
  have vG' := validEntries_entries_one hd.valid (rootCertificate_image_lt hj' i)
  rw [← entriesOp_entries_simple (R := R) hs i, ← entriesOp_entries_simple (R := R) hs j,
    ← entriesOp_entries_neg_simple (R := R) hs i, ← entriesOp_entries_neg_simple (R := R) hs j]
  refine ⟨?_, ?_, mul_comm_of_zeroE vEi vG h3, mul_comm_of_zeroE vEj vG h4,
    mul_comm_of_zeroE vFi vG' h5, mul_comm_of_zeroE vFj vG' h6⟩
  · rw [bracket_eq_of_zeroE vEi vEj h1, neg_neg]
  · exact bracket_eq_of_zeroE vFi vFj h2

end CFSG.LieType.Chevalley.RootOps
