module

public import CFSG.YGroups.Defs
public import CFSG.Certificates.Kernel.B433Alt.OmSoundCol

public section

namespace CFSG.KC.B433Alt

open CFSG.YGroups CFSG.Certificates.CosetEnumeration CFSG.KC.B4A CFSG.KC.Y333

open CFSG.KC.Benes (swp ValidIn Rep iterF compF iterF_snoc testBit_iterF testBit_dsw validIn_disj
  validIn_of_dsw swp_lt compF_lt andB_true repU_eq rep_mul_div
  rep_disj lt_of_validIn net_rep idPlane_testBit lt_two_pow_mono)
open CFSG.KC.MonsterConv.Perm (stageShift idPlane idP repU dswValid)

private theorem omS_OW : OW = 2 ^ 19 := by decide

private theorem omS_evalWord_congr {G : Type*} [Group G] {g g' : ℕ → G} {w : List ℕ}
    (h : ∀ c ∈ w, g c = g' c) : evalWord g w = evalWord g' w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [evalWord_cons, evalWord_cons, h c (by simp), ih (fun c' hc' => h c' (by simp [hc']))]

private theorem omS_lift_wordFG {G : Type*} [Group G] {n : ℕ} (f : Fin n → G) (w : List ℕ) :
    FreeGroup.lift f (wordFG n w) = evalWord (fun c => if h : c < n then f ⟨c, h⟩ else 1) w := by
  induction w with
  | nil => simp [wordFG, evalWord]
  | cons c w ih =>
    simp only [wordFG, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih, evalWord_cons]
    congr 1
    by_cases hc : c < n <;> simp [hc]

private theorem omS_lt_of_mem_yRels {w : List ℕ} (hw : w ∈ yRels 4 3 2) : ∀ c ∈ w, c < 10 := by
  intro c hc
  simp only [yRels, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_filter] at hw
  have h10 : ngen 4 3 2 = 10 := rfl
  rcases hw with (⟨s, hs, rfl⟩ | ⟨s, hs, t, ⟨ht, -⟩, rfl⟩) | hsp
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl <;> omega
  · simp only [pairWord, List.mem_flatten, List.mem_replicate] at hc
    obtain ⟨l, ⟨-, rfl⟩, hcl⟩ := hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcl
    rcases hcl with rfl | rfl <;> omega
  · rw [if_pos (by omega)] at hsp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsp
    subst hsp
    simp only [spiderWord, List.mem_flatten, List.mem_replicate] at hc
    obtain ⟨l, ⟨-, rfl⟩, hcl⟩ := hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcl
    omega

private theorem omS_letters {w : List ℕ}
    (hw : w ∈ yRels 4 3 2 ++ [(List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten]) :
    ∀ c ∈ w, c < 10 := by
  rcases List.mem_append.1 hw with hw | hw
  · exact omS_lt_of_mem_yRels hw
  · rw [List.mem_singleton] at hw
    subst hw
    decide

variable {MS : ℕ → ℕ}

private noncomputable def omS_tau (MS : ℕ → ℕ) (c t : ℕ) : ℕ → ℕ :=
  swp (stageShift 19 t) (MS (37 * c + t))

private noncomputable def omS_pi (MS : ℕ → ℕ) (c : ℕ) : ℕ → ℕ := compF (omS_tau MS c) 0 37

private theorem omS_masks_aux (MS : ℕ → ℕ) : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun i acc => CFSG.KC.B4A.andB acc
      (dswValid OW (stageShift (nat_lit 19) (Nat.mod i (nat_lit 37))) (MS i)))
      n = true → ∀ i < n, dswValid OW (stageShift 19 (i % 37)) (MS i) = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact omS_masks_aux MS n h1 i hi
    · exact h2

private theorem omS_validOW (hm : masksOK19 MS = true) {c t : ℕ} (hc : c < 10) (ht : t < 37) :
    ValidIn OW (stageShift 19 t) (MS (37 * c + t)) := by
  have h := omS_masks_aux MS (nat_lit 370) hm (37 * c + t) (show 37 * c + t < 370 by omega)
  have e : (37 * c + t) % 37 = t := by omega
  simp only [e] at h
  obtain ⟨h4, h5⟩ := andB_true h
  simp only [Nat.beq_eq] at h4 h5
  exact validIn_of_dsw h4 h5

private theorem omS_valid (hm : masksOK19 MS = true) {c t : ℕ} (hc : c < 10) (ht : t < 37) :
    ValidIn (2 ^ 19) (stageShift 19 t) (MS (37 * c + t)) := by
  rw [← omS_OW]
  exact omS_validOW hm hc ht

private theorem omS_netRec (MS : ℕ → ℕ) (c x : ℕ) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) x (fun t acc => sN acc (fun a => CFSG.KC.MonsterConv.Perm.dsw
      (stageShift (nat_lit 19) t) (MS (Nat.add (Nat.mul (nat_lit 37) c) t)) a)) n =
    iterF (fun t a => CFSG.KC.MonsterConv.Perm.dsw (stageShift 19 t) (MS (37 * c + t)) a) 0 n x
  | 0 => rfl
  | n + 1 => by
    rw [iterF_snoc, Nat.zero_add, ← omS_netRec MS c x n]
    exact omS_sN _ _

private theorem omS_netRecP (MS : ℕ → ℕ) (c x : ℕ) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) x (fun t acc => sN acc (fun a => CFSG.KC.MonsterConv.Perm.dsw
      (stageShift (nat_lit 19) t)
      (Nat.mul (MS (Nat.add (Nat.mul (nat_lit 37) c) t)) (repU OW (nat_lit 19))) a)) n =
    iterF (fun t a => CFSG.KC.MonsterConv.Perm.dsw (stageShift 19 t)
      (MS (37 * c + t) * repU OW 19) a) 0 n x
  | 0 => rfl
  | n + 1 => by
    rw [iterF_snoc, Nat.zero_add, ← omS_netRecP MS c x n]
    exact omS_sN _ _

private theorem omS_testBit_netApp19 (hm : masksOK19 MS = true) {c : ℕ} (hc : c < 10)
    (x q : ℕ) : (netApp19 MS c x).testBit q = x.testBit (omS_pi MS c q) := by
  have e : netApp19 MS c x = iterF (fun t a => CFSG.KC.MonsterConv.Perm.dsw (stageShift 19 t)
      (MS (37 * c + t)) a) 0 37 x := omS_netRec MS c x (nat_lit 37)
  rw [e]
  exact testBit_iterF (c := 37) (τ := omS_tau MS c)
    (fun i hi y q => testBit_dsw (validIn_disj (omS_valid hm hc hi)) y q) 0 37 le_rfl x q

private theorem omS_pi_lt (hm : masksOK19 MS = true) {c : ℕ} (hc : c < 10) {r : ℕ}
    (hr : r < 2 ^ 19) : omS_pi MS c r < 2 ^ 19 :=
  compF_lt (c := 37) (fun _ hi _ hr => swp_lt (omS_valid hm hc hi) hr) 0 37 le_rfl r hr

private def omS_Acts (f : ℕ → ℕ) (F : ℕ → ℕ) : Prop :=
  (∀ r < 2 ^ 19, f r < 2 ^ 19) ∧
    ∀ X, ∀ u < 19, ∀ r < 2 ^ 19, (F X).testBit (2 ^ 19 * u + r) = X.testBit (2 ^ 19 * u + f r)

private theorem omS_Acts.comp {f g F G : ℕ → ℕ} (hF : omS_Acts f F) (hG : omS_Acts g G) :
    omS_Acts (fun r => f (g r)) (fun X => G (F X)) :=
  ⟨fun r hr => hF.1 _ (hG.1 r hr), fun X u hu r hr => by
    rw [hG.2 (F X) u hu r hr, hF.2 X u hu _ (hG.1 r hr)]⟩

private theorem omS_acts_netAppP (hm : masksOK19 MS = true) {c : ℕ} (hc : c < 10) :
    omS_Acts (omS_pi MS c) (netAppP MS c) := by
  refine ⟨fun r hr => omS_pi_lt hm hc hr, fun X u hu r hr => ?_⟩
  have e : netAppP MS c X = iterF (fun t a => CFSG.KC.MonsterConv.Perm.dsw (stageShift 19 t)
      (MS (37 * c + t) * repU OW 19) a) 0 37 X := omS_netRecP MS c X (nat_lit 37)
  have hR : ∀ i < 37, Rep OW 19 (MS (37 * c + i) * repU OW 19) (MS (37 * c + i)) := by
    intro i hi
    rw [repU_eq]
    exact rep_mul_div (S := OW) (by rw [omS_OW]; positivity)
      (lt_of_validIn (omS_validOW hm hc hi))
  have := (net_rep (d := fun i => stageShift 19 i) (m := fun i => MS (37 * c + i))
    (fun i hi y q => testBit_dsw (rep_disj (hR i hi) (omS_validOW hm hc hi)) y q) hR
    (fun i hi => omS_validOW hm hc hi) X).1 u hu r (by rw [omS_OW]; exact hr)
  rw [e]
  rw [omS_OW] at this
  exact this

private def omS_wpi (π : ℕ → ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [] => fun r => r
  | c :: w => fun r => π c (omS_wpi π w r)

private theorem omS_acts_wordOn19 (hm : masksOK19 MS = true) : ∀ w : List ℕ, (∀ c ∈ w, c < 10) →
    omS_Acts (omS_wpi (omS_pi MS) w) (wordOn19 MS w)
  | [], _ => ⟨fun _ h => h, fun _ _ _ _ _ => rfl⟩
  | c :: w, h => by
    have h1 := omS_acts_netAppP hm (h c List.mem_cons_self)
    have h2 := omS_acts_wordOn19 hm w (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    have h3 := h1.comp h2
    refine ⟨h3.1, fun X u hu r hr => ?_⟩
    have e : wordOn19 MS (c :: w) X = wordOn19 MS w (netAppP MS c X) := omS_sN _ _
    rw [e]
    exact h3.2 X u hu r hr

private theorem omS_testBit_idPRec : ∀ n, n ≤ 19 → ∀ u, ∀ r < 2 ^ 19,
    (Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc
      (Nat.shiftLeft (idPlane (2 ^ 19) b) (Nat.mul b (2 ^ 19)))) n).testBit (2 ^ 19 * u + r) =
      (decide (u < n) && r.testBit u)
  | 0, _, u, r, _ => by simp
  | n + 1, hn, u, r, hr => by
    show (Nat.lor (Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc
      (Nat.shiftLeft (idPlane (2 ^ 19) b) (Nat.mul b (2 ^ 19)))) n)
      (Nat.shiftLeft (idPlane (2 ^ 19) n) (Nat.mul n (2 ^ 19)))).testBit (2 ^ 19 * u + r) = _
    rw [Benes.nlor, Benes.nshl, Benes.nmul, Nat.testBit_or, Nat.testBit_shiftLeft,
      omS_testBit_idPRec n (by omega) u r hr, idPlane_testBit (by omega)]
    rcases Nat.lt_trichotomy u n with h | rfl | h
    · have h1 : ¬ (2 ^ 19 * u + r ≥ n * 2 ^ 19) := by
        have : 2 ^ 19 * (u + 1) ≤ 2 ^ 19 * n := Nat.mul_le_mul_left _ h
        rw [Nat.mul_succ] at this
        rw [Nat.mul_comm n]
        omega
      rw [decide_eq_false h1, decide_eq_true h, decide_eq_true (show u < n + 1 by omega)]
      simp
    · rw [decide_eq_true (show 2 ^ 19 * u + r ≥ u * 2 ^ 19 by rw [Nat.mul_comm u]; omega),
        show 2 ^ 19 * u + r - u * 2 ^ 19 = r by rw [Nat.mul_comm u]; omega,
        decide_eq_true hr, decide_eq_false (show ¬ u < u by omega),
        decide_eq_true (show u < u + 1 by omega)]
      simp
    · have h2 : ¬ (2 ^ 19 * u + r - n * 2 ^ 19 < 2 ^ 19) := by
        have : 2 ^ 19 * (n + 1) ≤ 2 ^ 19 * u := Nat.mul_le_mul_left _ h
        rw [Nat.mul_succ] at this
        rw [Nat.mul_comm n]
        omega
      rw [decide_eq_false h2, decide_eq_false (show ¬ u < n by omega),
        decide_eq_false (show ¬ u < n + 1 by omega)]
      simp

private theorem omS_testBit_idP {u r : ℕ} (hu : u < 19) (hr : r < 2 ^ 19) :
    (idP 19).testBit (2 ^ 19 * u + r) = r.testBit u := by
  have e : idP 19 = Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc
      (Nat.shiftLeft (idPlane (2 ^ 19) b) (Nat.mul b (2 ^ 19)))) 19 := by
    unfold idP
    rw [Benes.nshl, Nat.one_shiftLeft]
  rw [e, omS_testBit_idPRec 19 le_rfl u r hr, decide_eq_true hu, Bool.true_and]

private theorem omS_eq_of_idP {f F : ℕ → ℕ} (hF : omS_Acts f F) (h : F (idP 19) = idP 19) :
    ∀ r < 2 ^ 19, f r = r := by
  intro r hr
  have hfr := hF.1 r hr
  apply Nat.eq_of_testBit_eq
  intro u
  by_cases hu : u < 19
  · rw [← omS_testBit_idP hu hfr, ← hF.2 _ u hu r hr, h, omS_testBit_idP hu hr]
  · rw [Nat.testBit_lt_two_pow (lt_two_pow_mono hfr (by omega)),
      Nat.testBit_lt_two_pow (lt_two_pow_mono hr (by omega))]

private theorem omS_relOK (hm : masksOK19 MS = true) {w : List ℕ} (hw : ∀ c ∈ w, c < 10)
    (h : relOK MS w = true) : ∀ r < 2 ^ 19, omS_wpi (omS_pi MS) w r = r :=
  omS_eq_of_idP (omS_acts_wordOn19 hm w hw)
    (Nat.eq_of_beq_eq_true (n := wordOn19 MS w (idP 19)) (m := idP 19) h)

private theorem omS_testBit_omStepRec (MS : ℕ → ℕ) (X q : ℕ) : ∀ n,
    (Nat.rec (motive := fun _ => ℕ) X (fun c acc => Nat.lor acc (netApp19 MS c X)) n).testBit q =
      true ↔ X.testBit q = true ∨ ∃ c < n, (netApp19 MS c X).testBit q = true
  | 0 => by simp
  | n + 1 => by
    show (Nat.lor (Nat.rec (motive := fun _ => ℕ) X (fun c acc => Nat.lor acc (netApp19 MS c X)) n)
      (netApp19 MS n X)).testBit q = true ↔ _
    rw [Benes.nlor, Nat.testBit_or, Bool.or_eq_true, omS_testBit_omStepRec MS X q n]
    constructor
    · rintro ((h | ⟨c, hc, h⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨c, by omega, h⟩
      · exact Or.inr ⟨n, by omega, h⟩
    · rintro (h | ⟨c, hc, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
        · exact Or.inl (Or.inr ⟨c, hc, h⟩)
        · exact Or.inr h

private theorem omS_testBit_omStep (MS : ℕ → ℕ) (X q : ℕ) :
    (omStep MS X).testBit q = true ↔
      X.testBit q = true ∨ ∃ c < 10, (netApp19 MS c X).testBit q = true :=
  omS_testBit_omStepRec MS X q 10

private theorem omS_testBit_omAll (q : ℕ) : omAll.testBit q = decide (q < 412896) := by
  have h : ∀ n, (Nat.sub (Nat.shiftLeft 1 n) 1).testBit q = decide (q < n) := by
    intro n
    rw [Benes.nsub, Benes.nshl, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
  exact h 412896

private theorem omS_closed {R : ℕ} (hm : masksOK19 MS = true) (horb : omOrbitOK MS R = true)
    {c : ℕ} (hc : c < 10) {q : ℕ} (h : omS_pi MS c q < 412896) : q < 412896 := by
  obtain ⟨h1, -⟩ := andB_true horb
  have e : omStep MS omAll = omAll := Nat.eq_of_beq_eq_true h1
  have h2 : (netApp19 MS c omAll).testBit q = true := by
    rw [omS_testBit_netApp19 hm hc, omS_testBit_omAll, decide_eq_true h]
  have h3 := (omS_testBit_omStep MS omAll q).2 (Or.inr ⟨c, hc, h2⟩)
  rw [e, omS_testBit_omAll] at h3
  simpa using h3

private theorem omS_invol (hm : masksOK19 MS = true)
    (hrel : ∀ w ∈ yRels 4 3 2 ++ [(List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten],
      relOK MS w = true) {c : ℕ} (hc : c < 10) {r : ℕ} (hr : r < 2 ^ 19) :
    omS_pi MS c (omS_pi MS c r) = r := by
  have hmem : [c, c] ∈ yRels 4 3 2 ++ [(List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten] :=
    List.mem_append_left _ (square_mem_yRels (show c < ngen 4 3 2 from hc))
  exact omS_relOK hm (omS_letters hmem) (hrel _ hmem) r hr

private theorem omS_pi_omega {R : ℕ} (hm : masksOK19 MS = true)
    (hrel : ∀ w ∈ yRels 4 3 2 ++ [(List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten],
      relOK MS w = true) (horb : omOrbitOK MS R = true) {c : ℕ} (hc : c < 10) {q : ℕ} :
    omS_pi MS c q < 412896 ↔ q < 412896 := by
  constructor
  · exact omS_closed hm horb hc
  · intro hq
    exact omS_closed hm horb hc (q := omS_pi MS c q)
      (by rw [omS_invol hm hrel hc (by omega)]; exact hq)

private theorem omS_perms {N : ℕ} (π : ℕ → ℕ → ℕ)
    (hπ : ∀ c < 10, ∀ x < N, π c x < N ∧ π c (π c x) = x) :
    ∃ σ : ℕ → Equiv.Perm (Fin N), ∀ c < 10, ∀ x : Fin N, (σ c x : ℕ) = π c x := by
  refine ⟨fun c => if hc : c < 10 then
    { toFun := fun x => ⟨π c x, (hπ c hc x x.2).1⟩
      invFun := fun x => ⟨π c x, (hπ c hc x x.2).1⟩
      left_inv := fun x => Fin.ext (hπ c hc x x.2).2
      right_inv := fun x => Fin.ext (hπ c hc x x.2).2 } else 1, fun c hc x => ?_⟩
  simp only [dif_pos hc]
  rfl

private theorem omS_evalWord_apply {N : ℕ} {σ : ℕ → Equiv.Perm (Fin N)} {π : ℕ → ℕ → ℕ}
    (hσ : ∀ c < 10, ∀ x : Fin N, (σ c x : ℕ) = π c x) :
    ∀ w : List ℕ, (∀ c ∈ w, c < 10) → ∀ x : Fin N, (evalWord σ w x : ℕ) = omS_wpi π w x
  | [], _, x => rfl
  | c :: w, h, x => by
    rw [evalWord_cons, Equiv.Perm.mul_apply, hσ c (h c List.mem_cons_self),
      omS_evalWord_apply hσ w (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) x]
    rfl

private theorem omS_evalWord_eq_one {N : ℕ} (hN : N ≤ 2 ^ 19) {σ : ℕ → Equiv.Perm (Fin N)}
    {π : ℕ → ℕ → ℕ} (hσ : ∀ c < 10, ∀ x : Fin N, (σ c x : ℕ) = π c x) {w : List ℕ}
    (hw : ∀ c ∈ w, c < 10) (h : ∀ r < 2 ^ 19, omS_wpi π w r = r) : evalWord σ w = 1 := by
  ext x
  rw [omS_evalWord_apply hσ w hw x, h x (by omega)]
  rfl

private theorem omS_hom {N : ℕ} {σ : ℕ → Equiv.Perm (Fin N)}
    (hrels : ∀ w ∈ yRels 4 3 2, evalWord σ w = 1) :
    ∃ ρ : YGroup 4 3 2 →* Equiv.Perm (Fin N), ∀ c < 10, ρ (yGen 4 3 2 c) = σ c := by
  refine ⟨PresentedGroup.toGroup (f := fun c : Fin (ngen 4 3 2) => σ c) ?_, fun c hc => ?_⟩
  · rintro x ⟨w, hw, rfl⟩
    rw [omS_lift_wordFG, omS_evalWord_congr (g' := σ)]
    · exact hrels w hw
    · intro c hc
      simp [show c < ngen 4 3 2 from omS_lt_of_mem_yRels hw c hc]
  · rw [yGen_of_lt (show c < ngen 4 3 2 from hc), PresentedGroup.toGroup.of]

private theorem omS_map_evalWord {G H : Type*} [Group G] [Group H] (f : G →* H) (g : ℕ → G)
    (w : List ℕ) : f (evalWord g w) = evalWord (fun c => f (g c)) w := by
  induction w with
  | nil => simp
  | cons c w ih => rw [evalWord_cons, map_mul, ih, evalWord_cons]

private theorem omS_idPlane_testBit {b : ℕ} (hb : b < 19) (p : ℕ) :
    (idPlane OW b).testBit p = (decide (p < 2 ^ 19) && p.testBit b) := by
  rw [omS_OW]
  exact idPlane_testBit hb p

private theorem omS_col {CB : ℕ → ℕ} (hm : masksOK19 MS = true)
    (hnc : ∀ c < 10, ∀ b < 19, netColOK MS CB c b = true)
    (htag : ∀ c < 10, ∀ b < 128, CB (256 * c + b) >>> 81920 = b) {c : ℕ} (hc : c < 10) {x : ℕ}
    (hx : x < 412896) : omS_pi MS c x = colAt CB c x := by
  have hx' : x < 2 ^ 19 := by omega
  rw [omS_colAt_eq hx' (htag c hc (x / 4096) (by omega))]
  have hlt := omS_pi_lt hm hc hx'
  apply Nat.eq_of_testBit_eq
  intro j
  rw [omS_testBit_bsum (by decide)]
  simp only [Nat.one_mul, Nat.mod_one, Nat.div_one, and_true]
  by_cases hj : j < 19
  · obtain ⟨h1, -⟩ := andB_true (hnc c hc j hj)
    rw [← Nat.eq_of_beq_eq_true h1, omS_testBit_netApp19 hm hc, omS_idPlane_testBit hj,
      decide_eq_true hlt, decide_eq_true (show j < 20 by omega), Bool.true_and, Bool.true_and]
  · by_cases hj20 : j < 20
    · obtain rfl : j = 19 := by omega
      obtain ⟨-, h2⟩ := andB_true (hnc c hc 0 (by omega))
      rw [Nat.eq_of_beq_eq_true h2, Nat.zero_testBit, Bool.and_false, Nat.testBit_lt_two_pow hlt]
    · rw [decide_eq_false hj20, Bool.false_and,
        Nat.testBit_lt_two_pow (lt_two_pow_mono hlt (by omega))]

private theorem omS_netApp_lt {R : ℕ} (hm : masksOK19 MS = true) (horb : omOrbitOK MS R = true)
    {c : ℕ} (hc : c < 10) {n E : ℕ} (hn : n = 412896) (hE : E < 2 ^ n) :
    netApp19 MS c E < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [omS_testBit_netApp19 hm hc]
  apply Nat.testBit_lt_two_pow
  apply lt_of_lt_of_le hE
  apply Nat.pow_le_pow_right (by norm_num)
  by_cases h : omS_pi MS c i < 412896
  · have := omS_closed hm horb hc h
    omega
  · omega

private theorem omS_orbit {R : ℕ} (hm : masksOK19 MS = true)
    (hrel : ∀ w ∈ yRels 4 3 2 ++ [(List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten],
      relOK MS w = true) (horb : omOrbitOK MS R = true) {σ : ℕ → Equiv.Perm (Fin 412896)}
    (hσ : ∀ c < 10, ∀ x : Fin 412896, (σ c x : ℕ) = omS_pi MS c x)
    {ρ : YGroup 4 3 2 →* Equiv.Perm (Fin 412896)} (hgen : ∀ c < 10, ρ (yGen 4 3 2 c) = σ c) :
    ∀ x : Fin 412896, x ∈ MulAction.orbit ρ.range (0 : Fin 412896) := by
  obtain ⟨-, h2⟩ := andB_true horb
  have eR := Nat.eq_of_beq_eq_true h2
  have key : ∀ n q, (Nat.rec (motive := fun _ => ℕ) 1
      (fun _ X => sN (omStep MS X) (fun Y => Y)) n).testBit q = true →
      ∃ h : q < 412896, (⟨q, h⟩ : Fin 412896) ∈ MulAction.orbit ρ.range (0 : Fin 412896) := by
    intro n
    induction n with
    | zero =>
      intro q hq
      obtain rfl : q = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.1 hq
      exact ⟨by norm_num, MulAction.mem_orbit_self _⟩
    | succ n ih =>
      intro q hq
      have e : Nat.rec (motive := fun _ => ℕ) 1 (fun _ X => sN (omStep MS X) (fun Y => Y)) (n + 1) =
          omStep MS (Nat.rec (motive := fun _ => ℕ) 1
            (fun _ X => sN (omStep MS X) (fun Y => Y)) n) := omS_sN _ _
      rw [e, omS_testBit_omStep] at hq
      rcases hq with hq | ⟨c, hc, hq⟩
      · exact ih q hq
      · rw [omS_testBit_netApp19 hm hc] at hq
        obtain ⟨h1, hmem⟩ := ih _ hq
        have hq' : q < 412896 := omS_closed hm horb hc h1
        refine ⟨hq', ?_⟩
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hmem
        refine MulAction.mem_orbit_iff.2
          ⟨⟨ρ (yGen 4 3 2 c), MonoidHom.mem_range.2 ⟨_, rfl⟩⟩ * g, ?_⟩
        rw [mul_smul, hg]
        apply Fin.ext
        show (ρ (yGen 4 3 2 c) ⟨omS_pi MS c q, h1⟩ : ℕ) = q
        rw [hgen c hc, hσ c hc, omS_invol hm hrel hc (by omega)]
  intro x
  have hx : (Nat.rec (motive := fun _ => ℕ) 1
      (fun _ X => sN (omStep MS X) (fun Y => Y)) R).testBit x = true := by
    rw [eR, omS_testBit_omAll, decide_eq_true x.2]
  obtain ⟨_, hmem⟩ := key R x hx
  exact hmem

theorem om_sound_aux {MS CB : ℕ → ℕ} {R : ℕ} (hm : masksOK19 MS = true)
    (hnc : ∀ c < 10, ∀ b < 19, netColOK MS CB c b = true)
    (htag : ∀ c < 10, ∀ b < 128, CB (256 * c + b) >>> 81920 = b)
    (hrel : ∀ w ∈ yRels 4 3 2 ++ [(List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten], relOK MS w = true)
    (horb : omOrbitOK MS R = true) :
    ∃ ρΩ : YGroup 4 3 2 →* Equiv.Perm (Fin 412896),
      (∀ c < 10, ∀ x : Fin 412896, (ρΩ (yGen 4 3 2 c) x : ℕ) = colAt CB c x) ∧
      evalWord (yGen 4 3 2) (List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten ∈ ρΩ.ker ∧
      (∀ c < 10, ∀ E < 2 ^ 412896, netApp19 MS c E < 2 ^ 412896 ∧
        {x : Fin 412896 | (netApp19 MS c E).testBit x = true} =
          ρΩ (yGen 4 3 2 c) '' {x : Fin 412896 | E.testBit x = true}) ∧
      ∀ x : Fin 412896, x ∈ MulAction.orbit ρΩ.range (0 : Fin 412896) := by
  obtain ⟨σ, hσ⟩ := omS_perms (N := 412896) (omS_pi MS) fun c hc x hx =>
    ⟨(omS_pi_omega hm hrel horb hc).2 hx, omS_invol hm hrel hc (by omega)⟩
  have hrels : ∀ w ∈ yRels 4 3 2 ++ [(List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten],
      evalWord σ w = 1 := fun w hw =>
    omS_evalWord_eq_one (by norm_num) hσ (omS_letters hw)
      (omS_relOK hm (omS_letters hw) (hrel w hw))
  obtain ⟨ρ, hgen⟩ := omS_hom (σ := σ) fun w hw => hrels w (List.mem_append_left _ hw)
  refine ⟨ρ, fun c hc x => ?_, ?_, fun c hc E hE => ⟨omS_netApp_lt hm horb hc rfl hE, ?_⟩,
    omS_orbit hm hrel horb hσ hgen⟩
  · rw [hgen c hc, hσ c hc, omS_col hm hnc htag hc x.2]
  · have hF : (List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten ∈
        yRels 4 3 2 ++ [(List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten] :=
      List.mem_append_right _ (List.mem_singleton_self _)
    rw [MonoidHom.mem_ker, omS_map_evalWord,
      omS_evalWord_congr (g' := σ) fun c hc => hgen c (omS_letters hF c hc)]
    exact hrels _ hF
  · ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    rw [omS_testBit_netApp19 hm hc, hgen c hc]
    constructor
    · intro h
      refine ⟨σ c y, by rw [hσ c hc]; exact h, Fin.ext ?_⟩
      rw [hσ c hc, hσ c hc, omS_invol hm hrel hc (by omega)]
    · rintro ⟨z, hz, rfl⟩
      rw [hσ c hc, omS_invol hm hrel hc (by omega)]
      exact hz

end CFSG.KC.B433Alt

end
