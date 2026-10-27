module

public import CFSG.LieType.Chevalley.A2CommutatorCheck

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.F2Words

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Chevalley.RootWalk

set_option linter.unusedSectionVars false


@[expose] def idE (τ : Tag) : List Entry := (List.range (dim τ)).map fun c => (c, c, 1)

@[expose] def genPos (τ : Tag) (j k : Fin τ.rank) : ℕ → ℕ
  | 0 => j
  | 1 => τ.rootCertificate.image j j
  | 2 => k
  | _ => τ.rootCertificate.image k k

@[expose] def nilE (τ : Tag) (j k : Fin τ.rank) (g : ℕ) : List Entry :=
  entries τ (genPos τ j k g) 1 ++ entries τ (genPos τ j k g) 2 ++ entries τ (genPos τ j k g) 3

@[expose] def wordN (τ : Tag) (j k : Fin τ.rank) (w : List ℕ) : List Entry :=
  w.foldl (fun M g => nilE τ j k g ++ M ++ mulE (nilE τ j k g) M) []

@[expose] def zeroE2 (L : List Entry) : Bool := (canonE L).all fun e => e.2.2 % 2 == 0

@[expose] def wordsData : List (List (List ℕ)) :=
  [
    [[3], [0, 3], [2, 0, 2], [0, 2, 0, 2], [2, 0, 2, 3], [3, 2, 0, 2]],
    [[], [0], [3], [0, 3], [2, 0, 2], [0, 2, 0, 2], [2, 0, 2, 3], [3, 2, 0, 2]],
    [[2], [1, 2], [3, 1, 3], [1, 3, 1, 3], [2, 3, 1, 3], [3, 1, 3, 2]],
    [[], [1], [2], [1, 2], [3, 1, 3], [1, 3, 1, 3], [2, 3, 1, 3], [3, 1, 3, 2]],
    [[1], [1, 2], [0, 2, 0], [0, 2, 0, 1], [0, 2, 0, 2], [1, 0, 2, 0]],
    [[], [1], [2], [1, 2], [0, 2, 0], [0, 2, 0, 1], [0, 2, 0, 2], [1, 0, 2, 0]],
    [[0], [0, 3], [1, 3, 1], [0, 1, 3, 1], [1, 3, 1, 0], [1, 3, 1, 3]],
    [[], [0], [3], [0, 3], [1, 3, 1], [0, 1, 3, 1], [1, 3, 1, 0], [1, 3, 1, 3]]]

@[expose] def certTarget (τ : Tag) (j k : Fin τ.rank) (i : ℕ) : Bool :=
  zeroE2 (entries τ (genPos τ j k (i / 2)) (i % 2 + 1) ++
    (if (wordsData.getD i []).length % 2 == 1 then idE τ else []) ++
    (wordsData.getD i []).flatMap (wordN τ j k))

@[expose] def certZero3 (τ : Tag) (j k : Fin τ.rank) (g : ℕ) : Bool :=
  zeroE2 (entries τ (genPos τ j k g) 3)

@[expose] def certCheck (τ : Tag) (j k : Fin τ.rank) : Bool :=
  (List.range 8).all (certTarget τ j k) && (List.range 4).all (certZero3 τ j k)

theorem certCheck_of_parts {τ : Tag} {j k : Fin τ.rank} (h : ∀ i < 8, certTarget τ j k i = true)
    (h3 : ∀ g < 4, certZero3 τ j k g = true) : certCheck τ j k = true := by
  simp only [certCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  exact ⟨h, h3⟩

section Sound

variable {τ : Tag} {R : Type} [CommRing R]

theorem validEntries_append {L L' : List Entry} (h : ValidEntries τ L) (h' : ValidEntries τ L') :
    ValidEntries τ (L ++ L') := fun e he => by
  rcases List.mem_append.1 he with he | he
  exacts [h e he, h' e he]

theorem validEntries_mulE {N M : List Entry} (hN : ValidEntries τ N) (hM : ValidEntries τ M) :
    ValidEntries τ (mulE N M) := by
  intro e he
  simp only [mulE, List.mem_flatMap, List.mem_map, List.mem_filter] at he
  obtain ⟨y, hy, x, ⟨hx, -⟩, rfl⟩ := he
  exact ⟨(hM y hy).1, (hN x hx).2⟩

theorem genPos_lt (hd : DataChecks τ) (j k : Fin τ.rank) (g : ℕ) :
    genPos τ j k g < τ.rootCertificate.roots.length := by
  have hj := val_lt_rootCertificate_length (τ := τ) j
  have hk := val_lt_rootCertificate_length (τ := τ) k
  unfold genPos
  split
  · exact hj
  · exact rootCertificate_image_lt hj j
  · exact hk
  · exact rootCertificate_image_lt hk k

theorem validEntries_nilE (hd : DataChecks τ) (j k : Fin τ.rank) (g : ℕ) :
    ValidEntries τ (nilE τ j k g) := by
  have ha := genPos_lt hd j k g
  have v := fun d (hd' : d ∈ [1, 2, 3]) =>
    validEntries_of_validB (validB_of_allValid hd.valid ha hd')
  exact validEntries_append (validEntries_append (v 1 (by simp)) (v 2 (by simp))) (v 3 (by simp))

theorem validEntries_wordN (hd : DataChecks τ) (j k : Fin τ.rank) :
    ∀ (w : List ℕ) (M : List Entry), ValidEntries τ M →
      ValidEntries τ (w.foldl (fun M g => nilE τ j k g ++ M ++ mulE (nilE τ j k g) M) M)
  | [], M, hM => hM
  | g :: w, M, hM => by
    rw [List.foldl_cons]
    exact validEntries_wordN hd j k w _
      (validEntries_append (validEntries_append (validEntries_nilE hd j k g) hM)
        (validEntries_mulE (validEntries_nilE hd j k g) hM))

theorem entriesOp_idE_aux (n : ℕ) (p : ℕ) (hp : p < dim τ) :
    entriesOp τ R ((List.range n).map fun c => (c, c, (1 : ℤ))) (posVec τ R p) =
      if p < n then posVec τ R p else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, entriesOp_append, LinearMap.add_apply, ih]
    simp only [List.map_cons, List.map_nil, entriesOp_cons, entriesOp_nil, add_zero,
      Int.cast_one, one_smul, LinearMap.smulRight_apply, LinearMap.add_apply,
      LinearMap.smul_apply]
    rw [posCoord_posVec hp]
    by_cases h1 : p < n
    · have : n ≠ p := by omega
      simp [h1, this, show p < n + 1 by omega]
    · by_cases h2 : n = p
      · subst h2
        simp
      · have : ¬ p < n + 1 := by omega
        simp [h1, h2, this]

theorem entriesOp_idE : entriesOp τ R (idE τ) = 1 := by
  refine ext_posVec fun p hp => ?_
  rw [Module.End.one_apply]
  unfold idE
  rw [entriesOp_idE_aux _ _ hp, if_pos hp]

theorem entriesOp_eq_zero_of_all_even (h2 : (2 : R) = 0) :
    ∀ L : List Entry, (∀ e ∈ L, e.2.2 % 2 = 0) → entriesOp τ R L = 0
  | [], _ => entriesOp_nil
  | e :: L, h => by
    rw [entriesOp_cons, entriesOp_eq_zero_of_all_even h2 L fun e' he' => h e' (List.mem_cons_of_mem _ he')]
    have hc : ((e.2.2 : ℤ) : R) = 0 := by
      obtain ⟨m, hm⟩ : (2 : ℤ) ∣ e.2.2 := Int.dvd_of_emod_eq_zero (h e (List.mem_cons_self ..))
      rw [hm]
      push_cast
      rw [h2, zero_mul]
    rw [hc, zero_smul, add_zero]

theorem entriesOp_eq_zero_of_zeroE2 (h2 : (2 : R) = 0) {L : List Entry} (h : zeroE2 L = true) :
    entriesOp τ R L = 0 := by
  rw [← entriesOp_canonE]
  refine entriesOp_eq_zero_of_all_even h2 _ fun e he => ?_
  simp only [zeroE2, List.all_eq_true, beq_iff_eq] at h
  exact h e he

theorem entriesOp_step {N M : List Entry} (hM : ValidEntries τ M) :
    entriesOp τ R (N ++ M ++ mulE N M) =
      entriesOp τ R N + entriesOp τ R M + entriesOp τ R N * entriesOp τ R M := by
  rw [entriesOp_append, entriesOp_append, entriesOp_mulE _ hM]

theorem commute_wordN (hd : DataChecks τ) (j k : Fin τ.rank) (z : Module.End R (RootModule τ R))
    (hG : ∀ g < 4, Commute z (1 + entriesOp τ R (nilE τ j k g))) :
    ∀ (w : List ℕ), (∀ g ∈ w, g < 4) → ∀ M : List Entry, ValidEntries τ M →
      Commute z (1 + entriesOp τ R M) →
      Commute z (1 + entriesOp τ R
        (w.foldl (fun M g => nilE τ j k g ++ M ++ mulE (nilE τ j k g) M) M))
  | [], _, M, _, hM => hM
  | g :: w, hw, M, hvM, hM => by
    rw [List.foldl_cons]
    refine commute_wordN hd j k z hG w (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg')) _
      (validEntries_append (validEntries_append (validEntries_nilE hd j k g) hvM)
        (validEntries_mulE (validEntries_nilE hd j k g) hvM)) ?_
    rw [entriesOp_step hvM]
    have : 1 + (entriesOp τ R (nilE τ j k g) + entriesOp τ R M +
        entriesOp τ R (nilE τ j k g) * entriesOp τ R M) =
        (1 + entriesOp τ R (nilE τ j k g)) * (1 + entriesOp τ R M) := by noncomm_ring
    rw [this]
    exact (hG g (hw g (List.mem_cons_self ..))).mul_right hM

theorem nat_cast_eq_mod_two (h2 : (2 : R) = 0) (n : ℕ) : ((n : ℕ) : R) = ((n % 2 : ℕ) : R) := by
  conv_lhs => rw [← Nat.mod_add_div n 2]
  push_cast
  rw [h2, zero_mul, add_zero]

theorem sum_one_add (A : List (Module.End R (RootModule τ R))) :
    (A.map fun a => 1 + a).sum = (A.length : R) • (1 : Module.End R (RootModule τ R)) + A.sum := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, List.sum_cons, Nat.cast_succ, add_smul,
      one_smul]
    abel

theorem commute_target (hd : DataChecks τ) (j k : Fin τ.rank) (h2 : (2 : R) = 0)
    (z : Module.End R (RootModule τ R))
    (hG : ∀ g < 4, Commute z (1 + entriesOp τ R (nilE τ j k g)))
    (hw : ∀ i < 8, ∀ w ∈ wordsData.getD i [], ∀ g ∈ w, g < 4) {i : ℕ} (hi : i < 8)
    (h : certTarget τ j k i = true) :
    Commute z (entriesOp τ R (entries τ (genPos τ j k (i / 2)) (i % 2 + 1))) := by
  classical
  set ws := wordsData.getD i [] with hws
  simp only [certTarget] at h
  have h0 := entriesOp_eq_zero_of_zeroE2 (τ := τ) (R := R) h2 h
  rw [entriesOp_append, entriesOp_append, entriesOp_flatMap] at h0
  have hP : entriesOp τ R (if ws.length % 2 == 1 then idE τ else []) =
      ((ws.length : ℕ) : R) • (1 : Module.End R (RootModule τ R)) := by
    rw [nat_cast_eq_mod_two h2 ws.length]
    by_cases hodd : ws.length % 2 = 1
    · simp [hodd, entriesOp_idE]
    · have : ws.length % 2 = 0 := by omega
      simp [this]
  rw [hP] at h0
  set a := fun w => entriesOp τ R (wordN τ j k w) with ha
  have hS : Commute z (ws.map fun w => 1 + a w).sum := by
    refine Commute.list_sum_right _ _ fun x hx => ?_
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 hx
    have := commute_wordN hd j k z hG w (hw i hi w hwm) [] (by intro e he; simp at he) (by
      simp only [entriesOp_nil, add_zero]
      exact Commute.one_right z)
    simpa [wordN, ha] using this
  rw [show (ws.map fun w => 1 + a w) = (ws.map a).map fun x => 1 + x by
    simp [List.map_map, Function.comp_def], sum_one_add, List.length_map] at hS
  have hT : entriesOp τ R (entries τ (genPos τ j k (i / 2)) (i % 2 + 1)) =
      ((ws.length : ℕ) : R) • (1 : Module.End R (RootModule τ R)) + (ws.map a).sum := by
    set X : Module.End R (RootModule τ R) :=
      ((ws.length : ℕ) : R) • (1 : Module.End R (RootModule τ R)) + (ws.map a).sum with hX
    have h1 : entriesOp τ R (entries τ (genPos τ j k (i / 2)) (i % 2 + 1)) + X = 0 := by
      rw [hX, ← add_assoc]
      exact h0
    have h3 : X + X = 0 := by
      rw [← two_smul R X, h2, zero_smul]
    calc entriesOp τ R (entries τ (genPos τ j k (i / 2)) (i % 2 + 1))
        = entriesOp τ R (entries τ (genPos τ j k (i / 2)) (i % 2 + 1)) + (X + X) := by
          rw [h3, add_zero]
      _ = (entriesOp τ R (entries τ (genPos τ j k (i / 2)) (i % 2 + 1)) + X) + X := by
          exact (add_assoc _ _ _).symm
      _ = X := by rw [h1, zero_add]
  rw [hT]
  exact hS

theorem wordsData_lt :
    (List.range 8).all (fun i => (wordsData.getD i []).all fun w => w.all (· < 4)) = true := by
  decide

theorem certCheck_parts {j k : Fin τ.rank} (h : certCheck τ j k = true) :
    (∀ i < 8, certTarget τ j k i = true) ∧ (∀ g < 4, certZero3 τ j k g = true) := by
  simp only [certCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h

theorem gen_zero (hd : DataChecks τ) (j k : Fin τ.rank) :
    1 + entriesOp τ R (nilE τ j k 0) = xOp τ R j 1 := by
  have h1 := hd.simple R j 1 le_rfl (by norm_num)
  have h2 := hd.simple R j 2 (by norm_num) (by norm_num)
  have h3 := hd.simple R j 3 (by norm_num) (by norm_num)
  rw [xOp_eq_sum_xCoeff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, one_pow,
    xCoeff_zero, nilE, genPos, entriesOp_append, h1, h2, h3]
  abel

theorem gen_one (hd : DataChecks τ) (j k : Fin τ.rank) :
    1 + entriesOp τ R (nilE τ j k 1) = yOp τ R j 1 := by
  have h1 := hd.negSimple R j 1 le_rfl (by norm_num)
  have h2 := hd.negSimple R j 2 (by norm_num) (by norm_num)
  have h3 := hd.negSimple R j 3 (by norm_num) (by norm_num)
  rw [yOp_eq_sum_yCoeff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, one_pow,
    yCoeff_zero, nilE, genPos, entriesOp_append, h1, h2, h3]
  abel

theorem gen_two (hd : DataChecks τ) (j k : Fin τ.rank) :
    1 + entriesOp τ R (nilE τ j k 2) = xOp τ R k 1 := by
  have h1 := hd.simple R k 1 le_rfl (by norm_num)
  have h2 := hd.simple R k 2 (by norm_num) (by norm_num)
  have h3 := hd.simple R k 3 (by norm_num) (by norm_num)
  rw [xOp_eq_sum_xCoeff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, one_pow,
    xCoeff_zero, nilE, genPos, entriesOp_append, h1, h2, h3]
  abel

theorem gen_three (hd : DataChecks τ) (j k : Fin τ.rank) :
    1 + entriesOp τ R (nilE τ j k 3) = yOp τ R k 1 := by
  have h1 := hd.negSimple R k 1 le_rfl (by norm_num)
  have h2 := hd.negSimple R k 2 (by norm_num) (by norm_num)
  have h3 := hd.negSimple R k 3 (by norm_num) (by norm_num)
  rw [yOp_eq_sum_yCoeff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, one_pow,
    yCoeff_zero, nilE, genPos, entriesOp_append, h1, h2, h3]
  abel

theorem commute_xOp_yOp_of_certCheck (hd : DataChecks τ) {j k : Fin τ.rank}
    (hc : certCheck τ j k = true) (h2 : (2 : R) = 0) (z : Module.End R (RootModule τ R))
    (hxj : Commute z (xOp τ R j 1)) (hyj : Commute z (yOp τ R j 1))
    (hxk : Commute z (xOp τ R k 1)) (hyk : Commute z (yOp τ R k 1)) (c : R) :
    Commute z (xOp τ R j c) ∧ Commute z (yOp τ R j c) ∧ Commute z (xOp τ R k c) ∧
      Commute z (yOp τ R k c) := by
  obtain ⟨ht, h3⟩ := certCheck_parts hc
  have hG : ∀ g < 4, Commute z (1 + entriesOp τ R (nilE τ j k g)) := by
    intro g hg
    interval_cases g
    · rw [gen_zero hd]; exact hxj
    · rw [gen_one hd]; exact hyj
    · rw [gen_two hd]; exact hxk
    · rw [gen_three hd]; exact hyk
  have hw : ∀ i < 8, ∀ w ∈ wordsData.getD i [], ∀ g ∈ w, g < 4 := by
    have := wordsData_lt
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at this
    intro i hi w hw g hg
    exact this i hi w hw g hg
  have hT : ∀ i < 8, Commute z
      (entriesOp τ R (entries τ (genPos τ j k (i / 2)) (i % 2 + 1))) := fun i hi =>
    commute_target hd j k h2 z hG hw hi (ht i hi)
  have hZ : ∀ g < 4, entriesOp τ R (entries τ (genPos τ j k g) 3) = 0 := fun g hg =>
    entriesOp_eq_zero_of_zeroE2 h2 (h3 g hg)
  have key : ∀ g < 4, Commute z (entriesOp τ R (entries τ (genPos τ j k g) 1)) ∧
      Commute z (entriesOp τ R (entries τ (genPos τ j k g) 2)) ∧
      Commute z (entriesOp τ R (entries τ (genPos τ j k g) 3)) := by
    intro g hg
    refine ⟨?_, ?_, by rw [hZ g hg]; exact Commute.zero_right z⟩
    · have := hT (2 * g) (by omega)
      rwa [show 2 * g / 2 = g by omega, show 2 * g % 2 + 1 = 1 by omega] at this
    · have := hT (2 * g + 1) (by omega)
      rwa [show (2 * g + 1) / 2 = g by omega, show (2 * g + 1) % 2 + 1 = 2 by omega] at this
  have k0 := key 0 (by norm_num)
  have k1 := key 1 (by norm_num)
  have k2 := key 2 (by norm_num)
  have k3 := key 3 (by norm_num)
  simp only [genPos] at k0 k1 k2 k3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [xOp_eq_sum_xCoeff]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, xCoeff_zero, pow_zero,
      one_smul]
    rw [← hd.simple R j 1 le_rfl (by norm_num), ← hd.simple R j 2 (by norm_num) (by norm_num),
      ← hd.simple R j 3 (by norm_num) (by norm_num)]
    exact (((Commute.one_right z).add_right (k0.1.smul_right _)).add_right
      (k0.2.1.smul_right _)).add_right (k0.2.2.smul_right _)
  · rw [yOp_eq_sum_yCoeff]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, yCoeff_zero, pow_zero,
      one_smul]
    rw [← hd.negSimple R j 1 le_rfl (by norm_num), ← hd.negSimple R j 2 (by norm_num) (by norm_num),
      ← hd.negSimple R j 3 (by norm_num) (by norm_num)]
    exact (((Commute.one_right z).add_right (k1.1.smul_right _)).add_right
      (k1.2.1.smul_right _)).add_right (k1.2.2.smul_right _)
  · rw [xOp_eq_sum_xCoeff]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, xCoeff_zero, pow_zero,
      one_smul]
    rw [← hd.simple R k 1 le_rfl (by norm_num), ← hd.simple R k 2 (by norm_num) (by norm_num),
      ← hd.simple R k 3 (by norm_num) (by norm_num)]
    exact (((Commute.one_right z).add_right (k2.1.smul_right _)).add_right
      (k2.2.1.smul_right _)).add_right (k2.2.2.smul_right _)
  · rw [yOp_eq_sum_yCoeff]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, yCoeff_zero, pow_zero,
      one_smul]
    rw [← hd.negSimple R k 1 le_rfl (by norm_num), ← hd.negSimple R k 2 (by norm_num) (by norm_num),
      ← hd.negSimple R k 3 (by norm_num) (by norm_num)]
    exact (((Commute.one_right z).add_right (k3.1.smul_right _)).add_right
      (k3.2.1.smul_right _)).add_right (k3.2.2.smul_right _)

end Sound

end CFSG.HardMathSupport.Timmesfeld.LangTorus.F2Words
