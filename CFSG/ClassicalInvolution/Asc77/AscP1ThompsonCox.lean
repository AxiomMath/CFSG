module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ClassicalInvolution.Asc77.Cox

variable {G : Type*} [Group G] {n : ℕ}

@[expose] def wp (s : Fin n → G) (w : List (Fin n)) : G := (w.map s).prod

structure IsRel (M : Fin n → Fin n → ℕ) (s : Fin n → G) : Prop where
  sq : ∀ i, s i * s i = 1
  comm : ∀ i j, M i j = 2 → s i * s j = s j * s i
  braid : ∀ i j, M i j = 3 → s i * s j * s i = s j * s i * s j

@[expose] def applyStep (M : Fin n → Fin n → ℕ) (w : List (Fin n))
    (st : ℕ × ℕ × Fin n × Fin n) : List (Fin n) :=
  if st.2.1 = 0 then
    (if (w.drop st.1).take 2 = [st.2.2.1, st.2.2.1] then w.take st.1 ++ w.drop (st.1 + 2) else w)
  else if st.2.1 = 1 then w.take st.1 ++ [st.2.2.1, st.2.2.1] ++ w.drop st.1
  else if st.2.1 = 2 then
    (if M st.2.2.1 st.2.2.2 = 2 ∧ (w.drop st.1).take 2 = [st.2.2.1, st.2.2.2] then
      w.take st.1 ++ [st.2.2.2, st.2.2.1] ++ w.drop (st.1 + 2) else w)
  else
    (if M st.2.2.1 st.2.2.2 = 3 ∧ (w.drop st.1).take 3 = [st.2.2.1, st.2.2.2, st.2.2.1] then
      w.take st.1 ++ [st.2.2.2, st.2.2.1, st.2.2.2] ++ w.drop (st.1 + 3) else w)

@[expose] def follow (M : Fin n → Fin n → ℕ) (w : List (Fin n))
    (cert : List (ℕ × ℕ × Fin n × Fin n)) : List (Fin n) :=
  cert.foldl (applyStep M) w

theorem wp_append (s : Fin n → G) (u v : List (Fin n)) : wp s (u ++ v) = wp s u * wp s v := by
  simp [wp, List.map_append, List.prod_append]

theorem wp_nil (s : Fin n → G) : wp s [] = 1 := rfl

theorem wp_splice (s : Fin n → G) (w r r' : List (Fin n)) (p k : ℕ)
    (hr : (w.drop p).take k = r) (hrr : wp s r' = wp s r) :
    wp s (w.take p ++ r' ++ w.drop (p + k)) = wp s w := by
  have hw : w = w.take p ++ r ++ w.drop (p + k) := by
    conv_lhs => rw [← List.take_append_drop p w, ← List.take_append_drop k (w.drop p), hr,
      List.drop_drop]
    simp
  conv_rhs => rw [hw]
  rw [wp_append, wp_append, wp_append, wp_append, hrr]

theorem wp_pair {M : Fin n → Fin n → ℕ} {s : Fin n → G} (hR : IsRel M s) (i : Fin n) :
    wp s [i, i] = 1 := by
  simp [wp, hR.sq i]

theorem wp_comm_pair {M : Fin n → Fin n → ℕ} {s : Fin n → G} (hR : IsRel M s) {i j : Fin n}
    (h : M i j = 2) : wp s [j, i] = wp s [i, j] := by
  simp only [wp, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact (hR.comm i j h).symm

theorem wp_braid_triple {M : Fin n → Fin n → ℕ} {s : Fin n → G} (hR : IsRel M s) {i j : Fin n}
    (h : M i j = 3) : wp s [j, i, j] = wp s [i, j, i] := by
  have := hR.braid i j h
  simp only [wp, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc, ← mul_assoc]
  exact this.symm

theorem wp_applyStep {M : Fin n → Fin n → ℕ} {s : Fin n → G} (hR : IsRel M s) (w : List (Fin n))
    (st : ℕ × ℕ × Fin n × Fin n) : wp s (applyStep M w st) = wp s w := by
  obtain ⟨p, k, i, j⟩ := st
  simp only [applyStep]
  split_ifs with h0 h1 h2 h3 h4 h5
  · simpa using wp_splice s w [i, i] [] p 2 h1 (by rw [wp_nil, wp_pair hR])
  · rfl
  · rw [wp_append, wp_append, wp_pair hR, mul_one, ← wp_append, List.take_append_drop]
  · exact wp_splice s w [i, j] [j, i] p 2 h4.2 (wp_comm_pair hR h4.1)
  · rfl
  · exact wp_splice s w [i, j, i] [j, i, j] p 3 h5.2 (wp_braid_triple hR h5.1)
  · rfl

theorem wp_follow {M : Fin n → Fin n → ℕ} {s : Fin n → G} (hR : IsRel M s) :
    ∀ (cert : List (ℕ × ℕ × Fin n × Fin n)) (w : List (Fin n)),
      wp s (follow M w cert) = wp s w := by
  intro cert
  induction cert with
  | nil => intro w; rfl
  | cons st c ih =>
    intro w
    show wp s (follow M (applyStep M w st) c) = wp s w
    rw [ih, wp_applyStep hR]

structure Entry (n : ℕ) where
  x : List (Fin n)
  g : Fin n
  h : List (Fin n)
  y : List (Fin n)
  cert : List (ℕ × ℕ × Fin n × Fin n)

@[expose] def entryOk (M : Fin n → Fin n → ℕ) (Hl : List (Fin n)) (T : List (List (Fin n)))
    (e : Entry n) : Bool :=
  e.h.all (fun i => Hl.contains i) && T.contains e.y &&
    decide (follow M (e.x ++ [e.g]) e.cert = e.h ++ e.y)

@[expose] def tableOk (M : Fin n → Fin n → ℕ) (Hl : List (Fin n)) (T : List (List (Fin n)))
    (E : List (Entry n)) : Bool :=
  T.contains [] && T.all (fun x => (List.finRange n).all (fun g =>
    E.any (fun e => decide (e.x = x) && decide (e.g = g) && entryOk M Hl T e)))

theorem tableOk_spec {M : Fin n → Fin n → ℕ} {Hl : List (Fin n)} {T : List (List (Fin n))}
    {E : List (Entry n)} (h : tableOk M Hl T E = true) :
    [] ∈ T ∧ ∀ x ∈ T, ∀ g : Fin n, ∃ e ∈ E, e.x = x ∧ e.g = g ∧ (∀ i ∈ e.h, i ∈ Hl) ∧ e.y ∈ T ∧
      follow M (x ++ [g]) e.cert = e.h ++ e.y := by
  simp only [tableOk, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true,
    List.mem_finRange, forall_const, List.any_eq_true, decide_eq_true_eq, entryOk] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun x hx g => ?_⟩
  obtain ⟨e, he, ⟨hxe, hge⟩, ⟨hh, hy⟩, hf⟩ := h2 x hx g
  subst hxe hge
  exact ⟨e, he, rfl, rfl, hh, hy, hf⟩

theorem wp_mem {s : Fin n → G} {H : Subgroup G} {Hl : List (Fin n)} (hH : ∀ i ∈ Hl, s i ∈ H)
    {w : List (Fin n)} (hw : ∀ i ∈ w, i ∈ Hl) : wp s w ∈ H := by
  unfold wp
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact hH i (hw i hi)

theorem exists_mul_of_mem_closure {M : Fin n → Fin n → ℕ} {s : Fin n → G} (hR : IsRel M s)
    {H : Subgroup G} {Hl : List (Fin n)} (hH : ∀ i ∈ Hl, s i ∈ H) {T : List (List (Fin n))}
    {E : List (Entry n)} (h : tableOk M Hl T E = true) :
    ∀ x ∈ Subgroup.closure (Set.range s), ∃ h ∈ H, ∃ w ∈ T, x = h * wp s w := by
  obtain ⟨hnil, hspec⟩ := tableOk_spec h
  have key : ∀ y ∈ T, ∀ g : Fin n, ∃ h ∈ H, ∃ w ∈ T, wp s y * s g = h * wp s w := by
    intro y hy g
    obtain ⟨e, -, -, -, hHl, hyT, hf⟩ := hspec y hy g
    refine ⟨wp s e.h, wp_mem hH hHl, e.y, hyT, ?_⟩
    have h1 := wp_follow hR e.cert (y ++ [g])
    rw [hf, wp_append, wp_append] at h1
    have h2 : wp s [g] = s g := by simp [wp]
    rw [h2] at h1
    exact h1.symm
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨1, H.one_mem, [], hnil, by simp [wp_nil]⟩
  | mul_right x hx y hy ih =>
    obtain ⟨h0, hh0, w, hw, rfl⟩ := ih
    obtain ⟨g, rfl⟩ := hy
    obtain ⟨h1, hh1, w', hw', e⟩ := key w hw g
    exact ⟨h0 * h1, H.mul_mem hh0 hh1, w', hw', by rw [mul_assoc, e, mul_assoc]⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨h0, hh0, w, hw, rfl⟩ := ih
    obtain ⟨g, rfl⟩ := hy
    obtain ⟨h1, hh1, w', hw', e⟩ := key w hw g
    have hinv : (s g)⁻¹ = s g := inv_eq_of_mul_eq_one_left (hR.sq g)
    exact ⟨h0 * h1, H.mul_mem hh0 hh1, w', hw', by rw [hinv, mul_assoc, e, mul_assoc]⟩

theorem card_closure_le {M : Fin n → Fin n → ℕ} {s : Fin n → G} (hR : IsRel M s)
    {H : Subgroup G} [Finite H] (hHP : H ≤ Subgroup.closure (Set.range s)) {Hl : List (Fin n)}
    (hH : ∀ i ∈ Hl, s i ∈ H) {T : List (List (Fin n))} {E : List (Entry n)}
    (h : tableOk M Hl T E = true) :
    Finite (Subgroup.closure (Set.range s)) ∧
      Nat.card (Subgroup.closure (Set.range s)) ≤ T.length * Nat.card H := by
  have hwT : ∀ w : List (Fin n), wp s w ∈ Subgroup.closure (Set.range s) := fun w =>
    wp_mem (H := Subgroup.closure (Set.range s)) (Hl := List.finRange n)
      (fun i _ => Subgroup.subset_closure ⟨i, rfl⟩) (fun i _ => List.mem_finRange i)
  let Φ : H × Fin T.length → Subgroup.closure (Set.range s) := fun p =>
    ⟨(p.1 : G) * wp s (T.get p.2), (Subgroup.closure (Set.range s)).mul_mem (hHP p.1.2) (hwT _)⟩
  have hΦ : Function.Surjective Φ := by
    rintro ⟨x, hx⟩
    obtain ⟨h0, hh0, w, hw, rfl⟩ := exists_mul_of_mem_closure hR hH h x hx
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hw
    exact ⟨(⟨h0, hh0⟩, j), Subtype.ext (by
    show h0 * wp s (T.get j) = h0 * wp s w
    rw [hj])⟩
  have : Finite (H × Fin T.length) := inferInstance
  refine ⟨Finite.of_surjective Φ hΦ, ?_⟩
  calc Nat.card (Subgroup.closure (Set.range s)) ≤ Nat.card (H × Fin T.length) :=
      Nat.card_le_card_of_surjective Φ hΦ
    _ = T.length * Nat.card H := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin T.length), Fintype.card_fin, mul_comm]

@[expose] def MA2 : Fin 2 → Fin 2 → ℕ := ![![1, 3], ![3, 1]]

@[expose] def MA3 : Fin 3 → Fin 3 → ℕ := ![![1, 3, 2], ![3, 1, 3], ![2, 3, 1]]

@[expose] def MD4 : Fin 4 → Fin 4 → ℕ :=
  ![![1, 3, 2, 2], ![3, 1, 3, 3], ![2, 3, 1, 2], ![2, 3, 2, 1]]

@[expose] def repsA2 : List (List (Fin 2)) :=
  [[], [0], [1], [0, 1], [1, 0], [0, 1, 0]]

@[expose] def tabA2 : List (Entry 2) :=
  [⟨[], 0, [], [0], []⟩,
   ⟨[], 1, [], [1], []⟩,
   ⟨[0], 0, [], [], [(0, 0, 0, 0)]⟩,
   ⟨[0], 1, [], [0, 1], []⟩,
   ⟨[1], 0, [], [1, 0], []⟩,
   ⟨[1], 1, [], [], [(0, 0, 1, 1)]⟩,
   ⟨[0, 1], 0, [], [0, 1, 0], []⟩,
   ⟨[0, 1], 1, [], [0], [(1, 0, 1, 1)]⟩,
   ⟨[1, 0], 0, [], [1], [(1, 0, 0, 0)]⟩,
   ⟨[1, 0], 1, [], [0, 1, 0], [(0, 3, 1, 0)]⟩,
   ⟨[0, 1, 0], 0, [], [0, 1], [(2, 0, 0, 0)]⟩,
   ⟨[0, 1, 0], 1, [], [1, 0], [(0, 3, 0, 1), (2, 0, 1, 1)]⟩]

@[expose] def repsA3 : List (List (Fin 3)) :=
  [[], [2], [2, 1], [2, 1, 0]]

@[expose] def tabA3 : List (Entry 3) :=
  [⟨[], 0, [0], [], []⟩,
   ⟨[], 1, [1], [], []⟩,
   ⟨[], 2, [], [2], []⟩,
   ⟨[2], 0, [0], [2], [(0, 2, 2, 0)]⟩,
   ⟨[2], 1, [], [2, 1], []⟩,
   ⟨[2], 2, [], [], [(0, 0, 2, 2)]⟩,
   ⟨[2, 1], 0, [], [2, 1, 0], []⟩,
   ⟨[2, 1], 1, [], [2], [(1, 0, 1, 1)]⟩,
   ⟨[2, 1], 2, [1], [2, 1], [(0, 3, 2, 1)]⟩,
   ⟨[2, 1, 0], 0, [], [2, 1], [(2, 0, 0, 0)]⟩,
   ⟨[2, 1, 0], 1, [0], [2, 1, 0], [(1, 3, 1, 0), (0, 2, 2, 0)]⟩,
   ⟨[2, 1, 0], 2, [1], [2, 1, 0], [(2, 2, 0, 2), (0, 3, 2, 1)]⟩]

@[expose] def repsD4 : List (List (Fin 4)) :=
  [[], [3], [3, 1], [3, 1, 0], [3, 1, 2], [3, 1, 0, 2], [3, 1, 0, 2, 1], [3, 1, 0, 2, 1, 3]]

@[expose] def tabD4 : List (Entry 4) :=
  [⟨[], 0, [0], [], []⟩,
   ⟨[], 1, [1], [], []⟩,
   ⟨[], 2, [2], [], []⟩,
   ⟨[], 3, [], [3], []⟩,
   ⟨[3], 0, [0], [3], [(0, 2, 3, 0)]⟩,
   ⟨[3], 1, [], [3, 1], []⟩,
   ⟨[3], 2, [2], [3], [(0, 2, 3, 2)]⟩,
   ⟨[3], 3, [], [], [(0, 0, 3, 3)]⟩,
   ⟨[3, 1], 0, [], [3, 1, 0], []⟩,
   ⟨[3, 1], 1, [], [3], [(1, 0, 1, 1)]⟩,
   ⟨[3, 1], 2, [], [3, 1, 2], []⟩,
   ⟨[3, 1], 3, [1], [3, 1], [(0, 3, 3, 1)]⟩,
   ⟨[3, 1, 0], 0, [], [3, 1], [(2, 0, 0, 0)]⟩,
   ⟨[3, 1, 0], 1, [0], [3, 1, 0], [(1, 3, 1, 0), (0, 2, 3, 0)]⟩,
   ⟨[3, 1, 0], 2, [], [3, 1, 0, 2], []⟩,
   ⟨[3, 1, 0], 3, [1], [3, 1, 0], [(2, 2, 0, 3), (0, 3, 3, 1)]⟩,
   ⟨[3, 1, 2], 0, [], [3, 1, 0, 2], [(2, 2, 2, 0)]⟩,
   ⟨[3, 1, 2], 1, [2], [3, 1, 2], [(1, 3, 1, 2), (0, 2, 3, 2)]⟩,
   ⟨[3, 1, 2], 2, [], [3, 1], [(2, 0, 2, 2)]⟩,
   ⟨[3, 1, 2], 3, [1], [3, 1, 2], [(2, 2, 2, 3), (0, 3, 3, 1)]⟩,
   ⟨[3, 1, 0, 2], 0, [], [3, 1, 2], [(2, 2, 0, 2), (3, 0, 0, 0)]⟩,
   ⟨[3, 1, 0, 2], 1, [], [3, 1, 0, 2, 1], []⟩,
   ⟨[3, 1, 0, 2], 2, [], [3, 1, 0], [(3, 0, 2, 2)]⟩,
   ⟨[3, 1, 0, 2], 3, [1], [3, 1, 0, 2], [(3, 2, 2, 3), (2, 2, 0, 3), (0, 3, 3, 1)]⟩,
   ⟨[3, 1, 0, 2, 1], 0, [2], [3, 1, 0, 2, 1], [(2, 2, 0, 2), (3, 3, 0, 1), (1, 3, 1, 2),
      (3, 2, 2, 0), (0, 2, 3, 2)]⟩,
   ⟨[3, 1, 0, 2, 1], 1, [], [3, 1, 0, 2], [(4, 0, 1, 1)]⟩,
   ⟨[3, 1, 0, 2, 1], 2, [0], [3, 1, 0, 2, 1], [(3, 3, 2, 1), (1, 3, 1, 0), (0, 2, 3, 0)]⟩,
   ⟨[3, 1, 0, 2, 1], 3, [], [3, 1, 0, 2, 1, 3], []⟩,
   ⟨[3, 1, 0, 2, 1, 3], 0, [2], [3, 1, 0, 2, 1, 3], [(5, 2, 3, 0), (2, 2, 0, 2), (3, 3, 0, 1),
      (1, 3, 1, 2), (3, 2, 2, 0), (0, 2, 3, 2)]⟩,
   ⟨[3, 1, 0, 2, 1, 3], 1, [1], [3, 1, 0, 2, 1, 3], [(4, 3, 1, 3), (3, 2, 2, 3), (2, 2, 0, 3),
      (0, 3, 3, 1)]⟩,
   ⟨[3, 1, 0, 2, 1, 3], 2, [0], [3, 1, 0, 2, 1, 3], [(5, 2, 3, 2), (3, 3, 2, 1), (1, 3, 1, 0),
      (0, 2, 3, 0)]⟩,
   ⟨[3, 1, 0, 2, 1, 3], 3, [], [3, 1, 0, 2, 1], [(5, 0, 3, 3)]⟩]


theorem tableOk_A2 : tableOk MA2 [] repsA2 tabA2 = true := by decide +kernel

theorem tableOk_A3 : tableOk MA3 [0, 1] repsA3 tabA3 = true := by decide +kernel

theorem tableOk_D4 : tableOk MD4 [0, 1, 2] repsD4 tabD4 = true := by decide +kernel

theorem IsRel.comp {m : ℕ} {M : Fin n → Fin n → ℕ} {s : Fin n → G} (hR : IsRel M s)
    {M' : Fin m → Fin m → ℕ} (e : Fin m → Fin n) (hM : ∀ i j, M' i j = M (e i) (e j)) :
    IsRel M' (s ∘ e) where
  sq i := hR.sq (e i)
  comm i j h := hR.comm (e i) (e j) (by rw [← hM]; exact h)
  braid i j h := hR.braid (e i) (e j) (by rw [← hM]; exact h)

theorem card_closure_A2 {s : Fin 2 → G} (hR : IsRel MA2 s) :
    Finite (Subgroup.closure (Set.range s)) ∧ Nat.card (Subgroup.closure (Set.range s)) ≤ 6 := by
  obtain ⟨hf, hc⟩ := card_closure_le (H := ⊥) hR bot_le (Hl := []) (by simp) tableOk_A2
  refine ⟨hf, ?_⟩
  have : repsA2.length = 6 := rfl
  rw [this, Subgroup.card_bot] at hc
  omega

theorem card_closure_A3 {s : Fin 3 → G} (hR : IsRel MA3 s) :
    Finite (Subgroup.closure (Set.range s)) ∧ Nat.card (Subgroup.closure (Set.range s)) ≤ 24 := by
  have hR' : IsRel MA2 (s ∘ Fin.castSucc) := hR.comp Fin.castSucc (by decide)
  obtain ⟨hf', hc'⟩ := card_closure_A2 hR'
  have hHP : Subgroup.closure (Set.range (s ∘ Fin.castSucc)) ≤ Subgroup.closure (Set.range s) :=
    Subgroup.closure_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.castSucc, rfl⟩)
  have hH : ∀ i ∈ [(0 : Fin 3), 1], s i ∈ Subgroup.closure (Set.range (s ∘ Fin.castSucc)) := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.subset_closure ⟨1, rfl⟩
  obtain ⟨hf, hc⟩ := card_closure_le hR hHP hH tableOk_A3
  refine ⟨hf, ?_⟩
  have : repsA3.length = 4 := rfl
  rw [this] at hc
  omega

theorem card_closure_D4 {s : Fin 4 → G} (hR : IsRel MD4 s) :
    Finite (Subgroup.closure (Set.range s)) ∧ Nat.card (Subgroup.closure (Set.range s)) ≤ 192 := by
  have hR' : IsRel MA3 (s ∘ Fin.castSucc) := hR.comp Fin.castSucc (by decide)
  obtain ⟨hf', hc'⟩ := card_closure_A3 hR'
  have hHP : Subgroup.closure (Set.range (s ∘ Fin.castSucc)) ≤ Subgroup.closure (Set.range s) :=
    Subgroup.closure_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.castSucc, rfl⟩)
  have hH : ∀ i ∈ [(0 : Fin 4), 1, 2], s i ∈ Subgroup.closure (Set.range (s ∘ Fin.castSucc)) := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.subset_closure ⟨1, rfl⟩
    · exact Subgroup.subset_closure ⟨2, rfl⟩
  obtain ⟨hf, hc⟩ := card_closure_le hR hHP hH tableOk_D4
  refine ⟨hf, ?_⟩
  have : repsD4.length = 8 := rfl
  rw [this] at hc
  omega

theorem comm_of_sq_eq_one {a b : G} (ha : a * a = 1) (hb : b * b = 1) (h : (a * b) ^ 2 = 1) :
    a * b = b * a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have h2 : a * b * (a * b) = 1 := by rw [← pow_two]; exact h
  have := eq_inv_of_mul_eq_one_left h2
  rw [mul_inv_rev, hai, hbi] at this
  exact this

theorem braid_of_cube_eq_one {a b : G} (ha : a * a = 1) (hb : b * b = 1) (h : (a * b) ^ 3 = 1) :
    a * b * a = b * a * b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have h6 : a * b * a * (b * a * b) = 1 := by
    have : (a * b) ^ 3 = a * b * a * (b * a * b) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← this]
    exact h
  have h7 := eq_inv_of_mul_eq_one_left h6
  rw [h7]
  simp only [mul_inv_rev, hai, hbi, mul_assoc]

theorem IsRel.of_pow {M : Fin n → Fin n → ℕ} {s : Fin n → G} (hdiag : ∀ i, M i i = 1)
    (h : ∀ i j, (s i * s j) ^ M i j = 1) : IsRel M s := by
  have hsq : ∀ i, s i * s i = 1 := fun i => by
    have := h i i
    rwa [hdiag i, pow_one] at this
  refine ⟨hsq, fun i j hij => comm_of_sq_eq_one (hsq i) (hsq j) ?_, fun i j hij =>
    braid_of_cube_eq_one (hsq i) (hsq j) ?_⟩
  · have := h i j
    rwa [hij] at this
  · have := h i j
    rwa [hij] at this

theorem IsRel.pow_eq_one {M : Fin n → Fin n → ℕ} {s : Fin n → G} (hR : IsRel M s)
    (hM1 : ∀ i j, M i j = 1 → i = j) (hM : ∀ i j, M i j = 1 ∨ M i j = 2 ∨ M i j = 3) (i j : Fin n) :
    (s i * s j) ^ M i j = 1 := by
  rcases hM i j with h1 | h2 | h3
  · rw [h1, pow_one, ← hM1 i j h1]
    exact hR.sq i
  · rw [h2, pow_two]
    calc s i * s j * (s i * s j) = s i * (s j * s i) * s j := by simp only [mul_assoc]
      _ = s i * (s i * s j) * s j := by rw [← hR.comm i j h2]
      _ = (s i * s i) * (s j * s j) := by simp only [mul_assoc]
      _ = 1 := by rw [hR.sq i, hR.sq j, one_mul]
  · rw [h3]
    have hb := hR.braid i j h3
    have hii : ∀ w, s i * (s i * w) = w := fun w => by rw [← mul_assoc, hR.sq i, one_mul]
    have hjj : ∀ w, s j * (s j * w) = w := fun w => by rw [← mul_assoc, hR.sq j, one_mul]
    calc (s i * s j) ^ 3 = s i * s j * s i * (s j * s i * s j) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = s i * s j * s i * (s i * s j * s i) := by rw [hb]
      _ = 1 := by simp only [mul_assoc, hii, hjj, hR.sq i]

theorem isRel_simple {M : CoxeterMatrix (Fin n)} {W : Type*} [Group W]
    (cs : CoxeterSystem M W) : IsRel M.M cs.simple :=
  IsRel.of_pow (fun i => M.diagonal i) (fun i j => cs.simple_mul_simple_pow i j)

theorem finite_card_le_of_closure_eq_top {s : Fin n → G}
    (hc : Subgroup.closure (Set.range s) = ⊤) {N : ℕ}
    (h : Finite (Subgroup.closure (Set.range s)) ∧ Nat.card (Subgroup.closure (Set.range s)) ≤ N) :
    Finite G ∧ Nat.card G ≤ N := by
  rw [hc] at h
  obtain ⟨hf, hb⟩ := h
  refine ⟨Finite.of_equiv _ (Subgroup.topEquiv (G := G)).toEquiv, ?_⟩
  rwa [Subgroup.card_top] at hb

theorem card_le_of_cs {M : CoxeterMatrix (Fin n)} {M' : Fin n → Fin n → ℕ}
    (hM : ∀ i j, M.M i j = M' i j) {W : Type*} [Group W] (cs : CoxeterSystem M W) {N : ℕ}
    (h : ∀ {s : Fin n → W}, IsRel M' s →
      Finite (Subgroup.closure (Set.range s)) ∧ Nat.card (Subgroup.closure (Set.range s)) ≤ N) :
    Finite W ∧ Nat.card W ≤ N := by
  have hR : IsRel M' cs.simple := by
    have := isRel_simple cs
    exact ⟨this.sq, fun i j hij => this.comm i j (by rw [hM]; exact hij),
      fun i j hij => this.braid i j (by rw [hM]; exact hij)⟩
  exact finite_card_le_of_closure_eq_top cs.subgroup_closure_range_simple (h hR)

theorem exists_mulEquiv_of_card_le {M : CoxeterMatrix (Fin n)} {W : Type*} [Group W]
    (cs : CoxeterSystem M W) [Finite W] {Q : Type*} [Group Q] [Finite Q] (f : Fin n → Q)
    (hf : M.IsLiftable f) (hgen : Subgroup.closure (Set.range f) = ⊤)
    (hcard : Nat.card W ≤ Nat.card Q) : ∃ e : W ≃* Q, ∀ i, e (cs.simple i) = f i := by
  let φ : W →* Q := cs.lift ⟨f, hf⟩
  have hφ : ∀ i, φ (cs.simple i) = f i := fun i => cs.lift_apply_simple hf i
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cs.simple i, hφ i⟩
  exact ⟨MulEquiv.ofBijective φ (hsurj.bijective_of_nat_card_le hcard), hφ⟩

theorem IsRel.of_eq {M M' : Fin n → Fin n → ℕ} {s : Fin n → G} (hM : ∀ i j, M i j = M' i j)
    (h : IsRel M' s) : IsRel M s where
  sq := h.sq
  comm i j hij := h.comm i j (by rw [← hM]; exact hij)
  braid i j hij := h.braid i j (by rw [← hM]; exact hij)

theorem IsRel.isLiftable {M : CoxeterMatrix (Fin n)} {f : Fin n → G} (hR : IsRel M.M f)
    (h123 : ∀ i j, M.M i j = 1 ∨ M.M i j = 2 ∨ M.M i j = 3) : M.IsLiftable f := fun i j =>
  hR.pow_eq_one (fun i j h => by
    by_contra hij
    exact M.off_diagonal i j hij h) h123 i j

theorem finite_card_A2 {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A 2) W) :
    Finite W ∧ Nat.card W ≤ 6 :=
  card_le_of_cs (M' := MA2) (fun i j => by fin_cases i <;> fin_cases j <;> rfl) cs
    fun hR => card_closure_A2 hR

theorem finite_card_A3 {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A 3) W) :
    Finite W ∧ Nat.card W ≤ 24 :=
  card_le_of_cs (M' := MA3) (fun i j => by fin_cases i <;> fin_cases j <;> rfl) cs
    fun hR => card_closure_A3 hR

theorem finite_card_D4 {M : CoxeterMatrix (Fin 4)} (hM : ∀ i j, M.M i j = MD4 i j) {W : Type*}
    [Group W] (cs : CoxeterSystem M W) : Finite W ∧ Nat.card W ≤ 192 :=
  card_le_of_cs hM cs fun hR => card_closure_D4 hR

theorem exists_mulEquiv_perm_A2 {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A 2) W) :
    ∃ e : W ≃* Equiv.Perm (Fin 3), ∀ i : Fin 2, e (cs.simple i) = Equiv.swap i.castSucc i.succ := by
  obtain ⟨hfin, hcard⟩ := finite_card_A2 cs
  have : Finite W := hfin
  refine exists_mulEquiv_of_card_le cs (fun i : Fin 2 => Equiv.swap i.castSucc i.succ)
    (by unfold CoxeterMatrix.IsLiftable; decide)
    (Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 2)) ?_
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]; rfl
  show Nat.card W ≤ Nat.card (Equiv.Perm (Fin 3))
  omega

theorem exists_mulEquiv_perm_A3 {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A 3) W) :
    ∃ e : W ≃* Equiv.Perm (Fin 4), ∀ i : Fin 3, e (cs.simple i) = Equiv.swap i.castSucc i.succ := by
  obtain ⟨hfin, hcard⟩ := finite_card_A3 cs
  have : Finite W := hfin
  refine exists_mulEquiv_of_card_le cs (fun i : Fin 3 => Equiv.swap i.castSucc i.succ)
    (by unfold CoxeterMatrix.IsLiftable; decide)
    (Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 3)) ?_
  have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]; rfl
  show Nat.card W ≤ Nat.card (Equiv.Perm (Fin 4))
  omega

end CFSG.ClassicalInvolution.Asc77.Cox
