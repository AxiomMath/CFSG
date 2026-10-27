module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.F2Words

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.F2Words

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Chevalley.RootWalk

set_option linter.unusedSectionVars false


@[expose] def wc (N M : List Entry) : List Entry := canonE (N ++ M ++ mulE N M)

@[expose] def wordC (τ : Tag) (j k : Fin τ.rank) (w : List ℕ) : List Entry :=
  w.foldl (fun M g => wc (nilE τ j k g) M) []

@[expose] def ordWord : List ℕ := [0, 1, 3, 2]

@[expose] def ordPowCheck (τ : Tag) (j k : Fin τ.rank) : Bool :=
  zeroE2 (wordC τ j k (List.replicate 7 ordWord).flatten)

@[expose] def oddAt (L : List Entry) (a b : ℕ) : Bool :=
  ((L.filter fun e => e.1 == a && e.2.1 == b).map fun e => e.2.2).sum % 2 == 1

@[expose] def ordNeCheck (τ : Tag) (j k : Fin τ.rank) : Bool :=
  (wordC τ j k ordWord).any fun e => oddAt (wordC τ j k ordWord) e.1 e.2.1

section Sound

variable {τ : Tag} {R : Type} [CommRing R]

theorem mem_combineE (L : List Entry) :
    ∀ x ∈ combineE L, ∃ y ∈ L, x.1 = y.1 ∧ x.2.1 = y.2.1 := by
  induction L with
  | nil => intro x hx; simp [combineE] at hx
  | cons e l ih =>
    intro x hx
    simp only [combineE] at hx
    revert hx ih
    generalize combineE l = M
    intro ih hx
    rcases M with _ | ⟨e', l'⟩
    · have hx' : x ∈ [e] := hx
      have hx'' : x = e := List.mem_singleton.1 hx'
      exact ⟨e, List.mem_cons_self .., by rw [hx''], by rw [hx'']⟩
    · dsimp only at hx
      split_ifs at hx with hk
      · simp only [Bool.and_eq_true] at hk
        have h1 := Nat.eq_of_beq_eq_true hk.1
        have h2 := Nat.eq_of_beq_eq_true hk.2
        rcases List.mem_cons.1 hx with hxe | hx
        · exact ⟨e, List.mem_cons_self .., by rw [hxe], by rw [hxe]⟩
        · obtain ⟨y, hy, h⟩ := ih x (List.mem_cons_of_mem _ hx)
          exact ⟨y, List.mem_cons_of_mem _ hy, h⟩
      · rcases List.mem_cons.1 hx with hxe | hx
        · exact ⟨e, List.mem_cons_self .., by rw [hxe], by rw [hxe]⟩
        · obtain ⟨y, hy, h⟩ := ih x hx
          exact ⟨y, List.mem_cons_of_mem _ hy, h⟩

theorem validEntries_canonE {L : List Entry} (h : ValidEntries τ L) :
    ValidEntries τ (canonE L) := by
  intro x hx
  simp only [canonE, List.mem_filter] at hx
  obtain ⟨y, hy, h1, h2⟩ := mem_combineE _ x hx.1
  have hy' := (msortF_perm 16 L).mem_iff.1 hy
  have := h y hy'
  rw [h1, h2]
  exact this

theorem validEntries_wc {N M : List Entry} (hN : ValidEntries τ N) (hM : ValidEntries τ M) :
    ValidEntries τ (wc N M) :=
  validEntries_canonE (validEntries_append (validEntries_append hN hM) (validEntries_mulE hN hM))

theorem wc_op {N M : List Entry} (hM : ValidEntries τ M) :
    1 + entriesOp τ R (wc N M) = (1 + entriesOp τ R N) * (1 + entriesOp τ R M) := by
  rw [wc, entriesOp_canonE, entriesOp_step hM]
  noncomm_ring

theorem validEntries_wordC (hd : DataChecks τ) (j k : Fin τ.rank) :
    ∀ (w : List ℕ) (M : List Entry), ValidEntries τ M →
      ValidEntries τ (w.foldl (fun M g => wc (nilE τ j k g) M) M)
  | [], M, hM => hM
  | g :: w, M, hM => by
    rw [List.foldl_cons]
    exact validEntries_wordC hd j k w _ (validEntries_wc (validEntries_nilE hd j k g) hM)

@[expose] noncomputable def prodOp (G : ℕ → Module.End R (RootModule τ R)) (w : List ℕ) : Module.End R (RootModule τ R) :=
  w.foldl (fun A g => G g * A) 1

theorem foldl_wc_op (hd : DataChecks τ) (j k : Fin τ.rank) :
    ∀ (w : List ℕ) (M : List Entry), ValidEntries τ M →
      1 + entriesOp τ R (w.foldl (fun M g => wc (nilE τ j k g) M) M) =
        w.foldl (fun A g => (1 + entriesOp τ R (nilE τ j k g)) * A) (1 + entriesOp τ R M)
  | [], M, _ => rfl
  | g :: w, M, hM => by
    rw [List.foldl_cons, List.foldl_cons, ← wc_op hM]
    exact foldl_wc_op hd j k w _ (validEntries_wc (validEntries_nilE hd j k g) hM)

theorem wordC_op (hd : DataChecks τ) (j k : Fin τ.rank) (w : List ℕ) :
    1 + entriesOp τ R (wordC τ j k w) =
      w.foldl (fun A g => (1 + entriesOp τ R (nilE τ j k g)) * A) 1 := by
  have h := foldl_wc_op (R := R) hd j k w [] (fun e he => by simp at he)
  rw [entriesOp_nil, add_zero] at h
  exact h

theorem prodOp_append (G : ℕ → Module.End R (RootModule τ R)) (w w' : List ℕ) :
    prodOp G (w ++ w') = prodOp G w' * prodOp G w := by
  have : ∀ (A : Module.End R (RootModule τ R)) (w w' : List ℕ),
      (w ++ w').foldl (fun A g => G g * A) A = w'.foldl (fun A g => G g * A) (w.foldl (fun A g => G g * A) A) := by
    intro A w w'
    exact List.foldl_append
  have h2 : ∀ (A : Module.End R (RootModule τ R)) (w' : List ℕ),
      w'.foldl (fun A g => G g * A) A = prodOp G w' * A := by
    intro A w'
    induction w' generalizing A with
    | nil => simp [prodOp]
    | cons g w' ih =>
      simp only [prodOp, List.foldl_cons, mul_one] at ih ⊢
      rw [ih (G g * A), ih (G g), mul_assoc]
  show (w ++ w').foldl (fun A g => G g * A) 1 = _
  rw [List.foldl_append, h2]
  rfl

theorem prodOp_replicate (G : ℕ → Module.End R (RootModule τ R)) (w : List ℕ) (n : ℕ) :
    prodOp G (List.replicate n w).flatten = prodOp G w ^ n := by
  induction n with
  | zero => simp [prodOp]
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, prodOp_append, ih, pow_succ]

@[expose] noncomputable def genOp (τ : Tag) (R : Type) [CommRing R] (j k : Fin τ.rank) :
    ℕ → Module.End R (RootModule τ R)
  | 0 => xOp τ R j 1
  | 1 => yOp τ R j 1
  | 2 => xOp τ R k 1
  | _ => yOp τ R k 1

theorem gen_eq (hd : DataChecks τ) (j k : Fin τ.rank) {g : ℕ} (hg : g < 4) :
    1 + entriesOp τ R (nilE τ j k g) = genOp τ R j k g := by
  interval_cases g
  · exact gen_zero hd j k
  · exact gen_one hd j k
  · exact gen_two hd j k
  · exact gen_three hd j k

theorem foldl_gen_eq (hd : DataChecks τ) (j k : Fin τ.rank) :
    ∀ (w : List ℕ), (∀ g ∈ w, g < 4) →
      w.foldl (fun A g => (1 + entriesOp τ R (nilE τ j k g)) * A) 1 = prodOp (genOp τ R j k) w
  | [], _ => rfl
  | g :: w, hw => by
    have hgw : ∀ g' ∈ w, g' < 4 := fun g' hg' => hw g' (List.mem_cons_of_mem _ hg')
    have key : ∀ (A : Module.End R (RootModule τ R)) (w : List ℕ), (∀ g ∈ w, g < 4) →
        w.foldl (fun A g => (1 + entriesOp τ R (nilE τ j k g)) * A) A =
          w.foldl (fun A g => genOp τ R j k g * A) A := by
      intro A w
      induction w generalizing A with
      | nil => intro _; rfl
      | cons g w ih =>
        intro hw
        rw [List.foldl_cons, List.foldl_cons, gen_eq hd j k (hw g (List.mem_cons_self ..))]
        exact ih _ fun g' hg' => hw g' (List.mem_cons_of_mem _ hg')
    exact key 1 (g :: w) hw

theorem wordC_prodOp (hd : DataChecks τ) (j k : Fin τ.rank) (w : List ℕ) (hw : ∀ g ∈ w, g < 4) :
    1 + entriesOp τ R (wordC τ j k w) = prodOp (genOp τ R j k) w := by
  rw [wordC_op hd, foldl_gen_eq hd j k w hw]

theorem ordWord_lt : ∀ g ∈ (List.replicate 7 ordWord).flatten, g < 4 := by decide

theorem ordWord_lt' : ∀ g ∈ ordWord, g < 4 := by decide

theorem prodOp_ord_pow (hd : DataChecks τ) (j k : Fin τ.rank) (h2 : (2 : R) = 0)
    (h : ordPowCheck τ j k = true) : prodOp (genOp τ R j k) ordWord ^ 7 = 1 := by
  rw [← prodOp_replicate, ← wordC_prodOp hd j k _ ordWord_lt,
    entriesOp_eq_zero_of_zeroE2 h2 h, add_zero]

theorem entriesOp_coord (L : List Entry) (hv : ValidEntries τ L) {a b : ℕ} (ha : a < dim τ)
    (hb : b < dim τ) :
    posCoord τ R b (entriesOp τ R L (posVec τ R a)) =
      (((L.filter fun e => e.1 == a && e.2.1 == b).map fun e => e.2.2).sum : ℤ) := by
  induction L with
  | nil => simp
  | cons e L ih =>
    have hvL : ValidEntries τ L := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    have hve := hv e (List.mem_cons_self ..)
    rw [entriesOp_cons, LinearMap.add_apply, map_add, ih hvL]
    simp only [LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul,
      posCoord_posVec ha, posCoord_posVec hve.2]
    rw [List.filter_cons]
    by_cases h1 : e.1 = a
    · by_cases h2 : e.2.1 = b
      · simp [h1, h2]
      · have : ¬ b = e.2.1 := fun h => h2 h.symm
        simp [h1, h2, this]
    · have : ¬ a = e.1 := fun h => h1 h.symm
      simp [h1, this]

theorem entriesOp_ne_zero_of_odd [Nontrivial R] (h2 : (2 : R) = 0) {L : List Entry}
    (hv : ValidEntries τ L) {e : Entry} (he : e ∈ L) (hodd : oddAt L e.1 e.2.1 = true) :
    entriesOp τ R L ≠ 0 := by
  intro h0
  have hc := entriesOp_coord (R := R) L hv (hv e he).1 (hv e he).2
  rw [h0, LinearMap.zero_apply, map_zero] at hc
  simp only [oddAt, beq_iff_eq] at hodd
  generalize (((L.filter fun e' => e'.1 == e.1 && e'.2.1 == e.2.1).map
      fun e => e.2.2).sum) = s at hc hodd
  obtain ⟨m, hm⟩ : ∃ m : ℤ, s = 2 * m + 1 := ⟨s / 2, by omega⟩
  rw [hm] at hc
  push_cast at hc
  rw [h2, zero_mul, zero_add] at hc
  exact one_ne_zero hc.symm

theorem prodOp_ord_ne [Nontrivial R] (hd : DataChecks τ) (j k : Fin τ.rank) (h2 : (2 : R) = 0)
    (h : ordNeCheck τ j k = true) : prodOp (genOp τ R j k) ordWord ≠ 1 := by
  intro h1
  rw [← wordC_prodOp hd j k _ ordWord_lt'] at h1
  have h0 : entriesOp τ R (wordC τ j k ordWord) = 0 := by
    refine ext_posVec fun p hp => ?_
    have := LinearMap.congr_fun h1 (posVec τ R p)
    simpa using this
  simp only [ordNeCheck, List.any_eq_true] at h
  obtain ⟨e, he, hodd⟩ := h
  exact entriesOp_ne_zero_of_odd h2
    (validEntries_wordC hd j k ordWord [] (fun e he => by simp at he)) he hodd h0

end Sound

set_option maxRecDepth 200000 in
theorem ordPowCheck_E6 : ordPowCheck .E6 ⟨0, by decide⟩ ⟨2, by decide⟩ = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem ordPowCheck_E7 : ordPowCheck .E7 ⟨0, by decide⟩ ⟨2, by decide⟩ = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem ordPowCheck_E8 : ordPowCheck .E8 ⟨0, by decide⟩ ⟨2, by decide⟩ = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem ordNeCheck_E6 : ordNeCheck .E6 ⟨0, by decide⟩ ⟨2, by decide⟩ = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem ordNeCheck_E7 : ordNeCheck .E7 ⟨0, by decide⟩ ⟨2, by decide⟩ = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem ordNeCheck_E8 : ordNeCheck .E8 ⟨0, by decide⟩ ⟨2, by decide⟩ = true := by decide +kernel

end CFSG.HardMathSupport.Timmesfeld.LangTorus.F2Words
