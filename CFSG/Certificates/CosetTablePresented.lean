module

public import CFSG.Certificates.CosetTable
public import CFSG.Certificates.PresentationLetters
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

section Words

variable {G : Type*} [Group G] {gen : ℕ → G}

theorem mem_dedup {w : List ℕ} : ∀ {ws : List (List ℕ)}, w ∈ dedup ws → w ∈ ws
  | [], h => by simp [dedup] at h
  | v :: ws, h => by
    simp only [dedup] at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_dedup h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_dedup h)

theorem evalWord_rotation {w v : List ℕ} (hv : v ∈ rotations w) (hw : evalWord gen w = 1) :
    evalWord gen v = 1 := by
  simp only [rotations, List.mem_map, List.mem_range] at hv
  obtain ⟨k, -, rfl⟩ := hv
  have h := hw
  rw [← List.take_append_drop k w, evalWord_append'] at h
  rw [evalWord_append', eq_inv_of_mul_eq_one_right h, inv_mul_cancel]

theorem letters_rotation {w v : List ℕ} {L : ℕ} (hv : v ∈ rotations w) (hw : ∀ y ∈ w, y < L) :
    ∀ y ∈ v, y < L := by
  simp only [rotations, List.mem_map, List.mem_range] at hv
  obtain ⟨k, -, rfl⟩ := hv
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hw y (List.mem_of_mem_drop hy)
  · exact hw y (List.mem_of_mem_take hy)

theorem evalWord_invWord {inv : Array ℕ} {w : List ℕ}
    (hinv : ∀ y ∈ w, gen (inv.getD y 0) = (gen y)⁻¹) :
    evalWord gen (invWord inv w) = (evalWord gen w)⁻¹ := by
  induction w with
  | nil => simp [invWord, evalWord]
  | cons y w ih =>
    rw [invWord, List.reverse_cons, List.map_append, evalWord_append', ← invWord,
      ih (fun y' hy' => hinv y' (by simp [hy'])), List.map_cons, List.map_nil, evalWord_cons,
      evalWord_nil, mul_one, hinv y (by simp), evalWord_cons, mul_inv_rev]

end Words

@[expose] def invArr (m : ℕ) : Array ℕ := (Array.range (2 * m)).map invCode

theorem invArr_getD {m x : ℕ} (hx : x < 2 * m) : (invArr m).getD x 0 = invCode x := by
  rw [invArr, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range,
    ite_eq_left hx]
  rfl

abbrev PG (m : ℕ) (ws : List (List (Fin m × Bool))) : Type :=
  PresentedGroup {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}

@[expose] def presParams {m : ℕ} (ws subs : List (List (Fin m × Bool))) : Params :=
  mkParams (2 * m) (invArr m) (codes ws) (codes subs)


theorem mem_scans {L : ℕ} {inv : Array ℕ} {rels subs : List (List ℕ)} {x : ℕ}
    {p : List ℕ × List ℕ} (hp : p ∈ (mkParams L inv rels subs).scans.getD x []) :
    p.2 = invWord inv p.1 ∧ ∃ r ∈ rels ++ rels.map (invWord inv), p.1 ∈ rotations r := by
  simp only [mkParams, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
    at hp
  split at hp
  · simp only [Option.map_some, Option.getD_some, List.mem_map, List.mem_filter] at hp
    obtain ⟨w, ⟨hw, -⟩, rfl⟩ := hp
    refine ⟨rfl, ?_⟩
    have hw' := mem_dedup ((List.mergeSort_perm _ _).mem_iff.mp hw)
    simpa only [List.mem_flatMap] using hw'
  · simp at hp

theorem mem_subs {L : ℕ} {inv : Array ℕ} {rels subs : List (List ℕ)}
    {p : List ℕ × List ℕ} (hp : p ∈ (mkParams L inv rels subs).subs) :
    p.2 = invWord inv p.1 ∧ p.1 ∈ subs := by
  simp only [mkParams, List.mem_map] at hp
  obtain ⟨w, hw, rfl⟩ := hp
  exact ⟨rfl, hw⟩

theorem letters_codes {m : ℕ} {ws : List (List (Fin m × Bool))} {w : List ℕ}
    (hw : w ∈ codes ws) : ∀ y ∈ w, y < 2 * m := by
  have := lettersOK_codes ws
  simp only [lettersOK, List.all_eq_true, Nat.blt_eq] at this
  exact this w hw

theorem goodParams {m : ℕ} (ws subs : List (List (Fin m × Bool)))
    (H : Subgroup (PG m ws))
    (hsubs : ∀ w ∈ subs, PresentedGroup.mk _ (FreeGroup.mk w) ∈ H) :
    Good (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) H (presParams ws subs) := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  have hinvL : ∀ x < 2 * m, (invArr m).getD x 0 < 2 * m := fun x hx => by
    rw [invArr_getD hx]; exact invCode_lt hx
  have hginv : ∀ x < 2 * m, presLetter rels ((invArr m).getD x 0) = (presLetter rels x)⁻¹ :=
    fun x hx => by rw [invArr_getD hx]; exact presLetter_invCode rels hx
  have hrel : ∀ r ∈ codes ws, evalWord (presLetter rels) r = 1 := by
    intro r hr
    simp only [codes, List.mem_map] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    rw [evalWord_presLetter]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hv)
  have hall : ∀ r ∈ codes ws ++ (codes ws).map (invWord (invArr m)),
      (∀ y ∈ r, y < 2 * m) ∧ evalWord (presLetter rels) r = 1 := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨letters_codes hr, hrel r hr⟩
    · simp only [List.mem_map] at hr
      obtain ⟨r0, hr0, rfl⟩ := hr
      have hl := letters_codes hr0
      refine ⟨?_, ?_⟩
      · intro y hy
        simp only [invWord, List.mem_map, List.mem_reverse] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact hinvL z (hl z hz)
      · rw [evalWord_invWord (fun y hy => hginv y (hl y hy)), hrel r0 hr0, inv_one]
  refine ⟨hinvL, hginv, ?_, ?_, ?_⟩
  · intro x p hp
    obtain ⟨h1, r, hr, hpr⟩ := mem_scans hp
    obtain ⟨hl, he⟩ := hall r hr
    exact ⟨h1, letters_rotation hpr hl, evalWord_rotation hpr he⟩
  · intro p hp
    obtain ⟨h1, hp1⟩ := mem_subs hp
    refine ⟨h1, letters_codes hp1, ?_⟩
    simp only [codes, List.mem_map] at hp1
    obtain ⟨v, hv, hpv⟩ := hp1
    rw [← hpv, evalWord_presLetter]
    exact hsubs v hv
  · intro p hp
    simp only [presParams, mkParams, List.mem_map] at hp
    obtain ⟨w, hw, rfl⟩ := hp
    exact ⟨rfl, letters_codes hw, hrel w hw⟩

theorem index_le_presented {m : ℕ} (ws subs : List (List (Fin m × Bool))) (H : Subgroup (PG m ws))
    (hsubs : ∀ w ∈ subs, PresentedGroup.mk _ (FreeGroup.mk w) ∈ H) {cap n : ℕ}
    (h : check (presParams ws subs) cap n = true) : H.FiniteIndex ∧ H.index ≤ n :=
  index_le_of_check (goodParams ws subs H hsubs) (by
    have := closure_presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
    simpa [presParams, mkParams] using this) h


@[expose] def renumber {m : ℕ} (S : List (Fin m)) :
    List (Fin m × Bool) → Option (List (Fin S.length × Bool))
  | [] => some []
  | l :: w =>
    match S.finIdxOf? l.1, renumber S w with
    | some i, some w' => some ((i, l.2) :: w')
    | _, _ => none

@[expose] def restrictWords {m : ℕ} (S : List (Fin m)) (ws : List (List (Fin m × Bool))) :
    List (List (Fin S.length × Bool)) :=
  ws.filterMap (renumber S)

theorem map_renumber {m : ℕ} (S : List (Fin m)) :
    ∀ (w : List (Fin m × Bool)) (w' : List (Fin S.length × Bool)), renumber S w = some w' →
      w'.map (fun l => (S.get l.1, l.2)) = w := by
  intro w
  induction w with
  | nil => intro w' h; simp [renumber] at h; subst h; rfl
  | cons l w ih =>
    intro w' h
    simp only [renumber] at h
    split at h
    · rename_i i v hi hv
      simp only [Option.some.injEq] at h
      subst h
      rw [List.map_cons, ih v hv]
      have := (List.finIdxOf?_eq_some_iff.mp hi).1
      simp only [Fin.getElem_fin] at this
      simp only [List.get_eq_getElem, this]
    · simp at h

noncomputable abbrev genSub {m : ℕ} (rels : Set (FreeGroup (Fin m))) (S : List (Fin m)) :
    Subgroup (PresentedGroup rels) :=
  Subgroup.closure ((fun x => PresentedGroup.of x) '' {x | x ∈ S})

theorem card_genSub_le {m : ℕ} (ws : List (List (Fin m × Bool))) (S : List (Fin m))
    [Finite (PG S.length (restrictWords S ws))] :
    Finite (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S) ∧
    Nat.card (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S) ≤
      Nat.card (PG S.length (restrictWords S ws)) := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  have hrel : ∀ r ∈ {r : FreeGroup (Fin S.length) | r ∈ (restrictWords S ws).map FreeGroup.mk},
      FreeGroup.lift (fun j => (PresentedGroup.of (S.get j) : PresentedGroup rels)) r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map, restrictWords, List.mem_filterMap] at hr
    obtain ⟨w', ⟨w, hw, hren⟩, rfl⟩ := hr
    have hmap : FreeGroup.lift (fun j => (PresentedGroup.of (S.get j) : PresentedGroup rels))
        (FreeGroup.mk w') = PresentedGroup.mk rels (FreeGroup.mk w) := by
      rw [← map_renumber S w w' hren]
      clear hren hw
      induction w' with
      | nil => rfl
      | cons l w' ih =>
        rw [show FreeGroup.mk (l :: w') = FreeGroup.mk [l] * FreeGroup.mk w' from rfl, map_mul,
          ih, List.map_cons, show FreeGroup.mk ((S.get l.1, l.2) :: List.map
            (fun l => (S.get l.1, l.2)) w') = FreeGroup.mk [(S.get l.1, l.2)] *
            FreeGroup.mk (List.map (fun l => (S.get l.1, l.2)) w') from rfl, map_mul]
        congr 1
        obtain ⟨j, b⟩ := l
        cases b
        · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv,
            FreeGroup.lift_apply_of]
          rfl
        · rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from rfl, FreeGroup.lift_apply_of]
          rfl
    rw [hmap]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)
  set φ := PresentedGroup.toGroup hrel
  have hrange : φ.range = genSub rels S := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨S.get j, List.get_mem _ _, by simp [φ]⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨j, hj⟩ := List.get_of_mem hx
      exact ⟨j, by rw [← hj]; simp [φ]⟩
  rw [← hrange]
  have hs : Function.Surjective (fun g => (⟨φ g, g, rfl⟩ : φ.range)) :=
    fun ⟨_, g, hg⟩ => ⟨g, Subtype.ext hg⟩
  exact ⟨Finite.of_surjective _ hs, Nat.card_le_card_of_surjective _ hs⟩

theorem card_le_of_check {m : ℕ} (ws : List (List (Fin m × Bool))) (S : List (Fin m))
    {cap n : ℕ} (h : check (presParams ws (S.map fun x => [(x, true)])) cap n = true)
    [Finite (PG S.length (restrictWords S ws))] :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * Nat.card (PG S.length (restrictWords S ws)) := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  obtain ⟨hfi, hidx⟩ := index_le_presented ws (S.map fun x => [(x, true)]) (genSub rels S)
    (by
      intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact Subgroup.subset_closure ⟨x, hx, rfl⟩) h
  obtain ⟨hfinH, hsub⟩ := card_genSub_le ws S
  have hfin : Finite (PG m ws) := by
    have : Finite (PG m ws ⧸ genSub rels S) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient (genSub rels S)
  refine ⟨hfin, ?_⟩
  rw [← (genSub rels S).index_mul_card]
  exact Nat.mul_le_mul hidx hsub


instance (ws : List (List (Fin 0 × Bool))) : Subsingleton (PG 0 ws) := by
  constructor
  intro a b
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y => rw [Subsingleton.elim x y]

instance (ws : List (List (Fin 0 × Bool))) : Finite (PG 0 ws) := Finite.of_subsingleton

theorem card_PG_zero (ws : List (List (Fin 0 × Bool))) : Nat.card (PG 0 ws) = 1 :=
  Nat.card_unique

theorem card_le_of_check_trivial {m : ℕ} (ws : List (List (Fin m × Bool))) {cap n : ℕ}
    (h : check (presParams ws (([] : List (Fin m)).map fun x => [(x, true)])) cap n = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  have : Finite (PG ([] : List (Fin m)).length (restrictWords [] ws)) :=
    (inferInstance : Finite (PG 0 _))
  have hc : Nat.card (PG ([] : List (Fin m)).length (restrictWords [] ws)) = 1 :=
    card_PG_zero (restrictWords [] ws)
  have := card_le_of_check ws [] h
  rwa [hc, mul_one] at this


theorem mk_flatten_replicate {α : Type*} (u : List (α × Bool)) :
    ∀ k : ℕ, FreeGroup.mk (List.replicate k u).flatten = FreeGroup.mk u ^ k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, ih, pow_succ']

theorem card_le_of_check_cyclic {m : ℕ} (ws : List (List (Fin m × Bool))) (u : List (Fin m × Bool))
    {k : ℕ} (hk0 : 0 < k) (hk : (List.replicate k u).flatten ∈ ws) {cap n : ℕ}
    (h : check (presParams ws [u]) cap n = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * k := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set g : PG m ws := PresentedGroup.mk rels (FreeGroup.mk u)
  obtain ⟨hfi, hidx⟩ := index_le_presented ws [u] (Subgroup.zpowers g)
    (by intro w hw; simp at hw; subst hw; exact Subgroup.mem_zpowers g) h
  have hg : g ^ k = 1 := by
    rw [show g ^ k = PresentedGroup.mk rels (FreeGroup.mk u ^ k) from (map_pow _ _ _).symm,
      ← mk_flatten_replicate]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hk)
  have hord : orderOf g ∣ k := orderOf_dvd_of_pow_eq_one hg
  have hpos : 0 < orderOf g := Nat.pos_of_dvd_of_pos hord hk0
  have hfinz : Finite (Subgroup.zpowers g) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
  have hcard : Nat.card (Subgroup.zpowers g) ≤ k := by
    rw [Nat.card_zpowers]; exact Nat.le_of_dvd hk0 hord
  have hG : Finite (PG m ws) := by
    have : Finite (PG m ws ⧸ Subgroup.zpowers g) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient (Subgroup.zpowers g)
  refine ⟨hG, ?_⟩
  rw [← (Subgroup.zpowers g).index_mul_card]
  exact Nat.mul_le_mul hidx hcard


@[expose] def subsetOf (m : ℕ) (S : List ℕ) : List (Fin m) :=
  (List.finRange m).filter fun i => S.contains i.val

@[expose] def subsetCheck {m : ℕ} (ws : List (List (Fin m × Bool))) (S : List ℕ) (cap n : ℕ) :
    Bool :=
  check (presParams ws ((subsetOf m S).map fun x => [(x, true)])) cap n

theorem card_le_of_subsetCheck {m : ℕ} (ws : List (List (Fin m × Bool))) (S : List ℕ)
    {cap n : ℕ} (h : subsetCheck ws S cap n = true)
    [Finite (PG (subsetOf m S).length (restrictWords (subsetOf m S) ws))] :
    Finite (PG m ws) ∧
      Nat.card (PG m ws) ≤ n * Nat.card (PG (subsetOf m S).length (restrictWords (subsetOf m S) ws)) :=
  card_le_of_check ws (subsetOf m S) h

@[expose] def cyclicCheck {m : ℕ} (ws : List (List (Fin m × Bool))) (u : List ℕ) (k cap n : ℕ) :
    Bool :=
  u.all (fun c => decide (c < 2 * m)) && (codes ws).contains (List.replicate k u).flatten &&
    check (mkParams (2 * m) (invArr m) (codes ws) [u]) cap n

theorem evalWord_flatten_replicate {G : Type*} [Group G] (gen : ℕ → G) (u : List ℕ) :
    ∀ k : ℕ, evalWord gen (List.replicate k u).flatten = evalWord gen u ^ k := by
  intro k
  induction k with
  | zero => simp [evalWord]
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, evalWord_append', ih, pow_succ']

theorem card_le_of_cyclicCheck {m : ℕ} (ws : List (List (Fin m × Bool))) (u : List ℕ)
    {k cap n : ℕ} (hk0 : 0 < k) (h : cyclicCheck ws u k cap n = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * k := by
  unfold cyclicCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨⟨hu, hk⟩, hc⟩ := h
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set g : PG m ws := evalWord (presLetter rels) u
  have hrel : ∀ r ∈ codes ws, evalWord (presLetter rels) r = 1 := by
    intro r hr
    simp only [codes, List.mem_map] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    rw [evalWord_presLetter]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hv)
  have hgood : Good (presLetter rels) (Subgroup.zpowers g) (mkParams (2 * m) (invArr m) (codes ws) [u]) := by
    have := goodParams ws [] (⊥ : Subgroup (PG m ws)) (by simp)
    refine ⟨this.inv_lt, this.gen_inv, ?_, ?_, ?_⟩
    · intro x p hp
      have hp' : p ∈ (presParams ws []).scans.getD x [] := by
        simpa [presParams, mkParams] using hp
      exact this.scans x p hp'
    · intro p hp
      obtain ⟨h1, hp1⟩ := mem_subs hp
      simp only [List.mem_singleton] at hp1
      exact ⟨h1, by rw [hp1]; exact hu, by rw [hp1]; exact Subgroup.mem_zpowers g⟩
    · intro p hp
      exact this.rels p (by simpa [presParams, mkParams] using hp)
  obtain ⟨hfi, hidx⟩ := index_le_of_check hgood (by
    have := closure_presLetter rels
    simpa [mkParams] using this) hc
  have hg : g ^ k = 1 := by
    rw [← hrel _ hk, evalWord_flatten_replicate]
  have hord : orderOf g ∣ k := orderOf_dvd_of_pow_eq_one hg
  have hpos : 0 < orderOf g := Nat.pos_of_dvd_of_pos hord hk0
  have hfinz : Finite (Subgroup.zpowers g) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
  have hcard : Nat.card (Subgroup.zpowers g) ≤ k := by
    rw [Nat.card_zpowers]; exact Nat.le_of_dvd hk0 hord
  have hG : Finite (PG m ws) := by
    have : Finite (PG m ws ⧸ Subgroup.zpowers g) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient (Subgroup.zpowers g)
  refine ⟨hG, ?_⟩
  rw [← (Subgroup.zpowers g).index_mul_card]
  exact Nat.mul_le_mul hidx hcard


theorem card_le_of_subsetCheck_nil {m : ℕ} (ws : List (List (Fin m × Bool))) {cap n : ℕ}
    (h : subsetCheck ws [] cap n = true) : Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  have hS : subsetOf m [] = [] := by simp [subsetOf]
  unfold subsetCheck at h
  rw [hS] at h
  exact card_le_of_check_trivial ws h

end CFSG.CosetTable
