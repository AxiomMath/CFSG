module

public import Certificates.Data.Kernel.F48Small.Pack
public import CFSG.Milestones.ASVolI.F48.Small.Eng
public import CFSG.Certificates.Kernel.LocalQTBfsKSound

public section

namespace CFSG.KC.F48S

open CFSG.KC.Ord CFSG.KC.LQT.L CFSG.Quasithin CFSG.ASVolI

def Small (l : List ℕ) : Prop := ∀ e ∈ l, e < 64

theorem andB_eq (a b : Bool) : CFSG.KC.Ord.andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : CFSG.KC.Ord.orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : CFSG.KC.Ord.notB a = !a := by cases a <;> rfl

theorem allA_eq {α : Type} (l : List α) (f : α → Bool) : allA l f = l.all f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change CFSG.KC.Ord.andB (f x) (allA l f) = _
    rw [andB_eq, ih, List.all_cons]

theorem anyA_eq {α : Type} (l : List α) (f : α → Bool) : anyA l f = l.any f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change CFSG.KC.Ord.orB (f x) (anyA l f) = _
    rw [orB_eq, ih, List.any_cons]

theorem encL_nil : encL [] = 0 := rfl

theorem encL_cons (a : ℕ) (l : List ℕ) : encL (a :: l) = a + encL l * 64 := by
  change a + (encL l <<< 6) = _
  rw [Nat.shiftLeft_eq]

theorem land63 (x : ℕ) : Nat.land x 63 = x % 64 := Nat.and_two_pow_sub_one_eq_mod x 6

theorem pget_eq (p j : ℕ) : pget p j = p / 64 ^ j % 64 := by
  change Nat.land (Nat.shiftRight p (Nat.mul 6 j)) 63 = _
  rw [land63]
  change (p >>> (6 * j)) % 64 = _
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem enc_mod (a e : ℕ) (ha : a < 64) : (a + e * 64) % 64 = a := by omega

theorem enc_div (a e : ℕ) (ha : a < 64) : (a + e * 64) / 64 = e := by omega

theorem pget_encL : ∀ (a : List ℕ), Small a → ∀ j, pget (encL a) j = a.getD j 0
  | [], _, j => by rw [pget_eq, encL_nil]; simp
  | x :: a, h, j => by
    have hx : x < 64 := h x (by simp)
    have ha : Small a := fun e he => h e (by simp [he])
    cases j with
    | zero => rw [pget_eq, encL_cons, pow_zero, Nat.div_one, enc_mod _ _ hx]; rfl
    | succ j =>
      rw [List.getD_cons_succ, ← pget_encL a ha j, pget_eq, pget_eq, encL_cons, pow_succ',
        ← Nat.div_div_eq_div_mul, enc_div _ _ hx]

theorem pcomp_succ (p k q : ℕ) :
    pcomp p (k + 1) q = pget p (q % 64) + pcomp p k (q / 64) * 64 := by
  change pget p (Nat.land q 63) + (pcomp p k (q >>> 6) <<< 6) = _
  rw [land63, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

theorem pcomp_encL (p : ℕ) : ∀ (b : List ℕ), Small b →
    pcomp p b.length (encL b) = encL (b.map (pget p))
  | [], _ => rfl
  | x :: b, h => by
    have hx : x < 64 := h x (by simp)
    have hb : Small b := fun e he => h e (by simp [he])
    rw [List.length_cons, pcomp_succ, encL_cons, enc_mod _ _ hx, enc_div _ _ hx,
      pcomp_encL p b hb, List.map_cons, encL_cons]

theorem small_compL {a : List ℕ} (ha : Small a) (b : List ℕ) : Small (compL a b) := by
  intro e he
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
  rw [List.getD_eq_getElem?_getD]
  cases h : a[j]? with
  | none => simp
  | some v => exact ha v (List.mem_of_getElem? h)

theorem encL_compL {a b : List ℕ} (ha : Small a) (hb : Small b) :
    encL (compL a b) = pcomp (encL a) b.length (encL b) := by
  rw [pcomp_encL _ b hb]
  congr 1
  apply List.map_congr_left
  intro j _
  rw [pget_encL a ha]

theorem encL_inj : ∀ {a b : List ℕ}, a.length = b.length → Small a → Small b →
    encL a = encL b → a = b
  | [], [], _, _, _, _ => rfl
  | x :: a, y :: b, hl, ha, hb, he => by
    have hx : x < 64 := ha x (by simp)
    have hy : y < 64 := hb y (by simp)
    rw [encL_cons, encL_cons] at he
    have e1 : x = y := by rw [← enc_mod x (encL a) hx, he, enc_mod _ _ hy]
    have e2 : encL a = encL b := by rw [← enc_div x (encL a) hx, he, enc_div _ _ hy]
    rw [e1, encL_inj (by simpa using hl) (fun e h => ha e (by simp [h]))
      (fun e h => hb e (by simp [h])) e2]

theorem eqAt_iff (p q r s : ℕ) :
    ∀ n, eqAt p q r s n = true ↔ ∀ i < n, pget p (pget q i) = pget r (pget s i)
  | 0 => by simp [eqAt]
  | n + 1 => by
    change CFSG.KC.Ord.andB (Nat.beq (pget p (pget q n)) (pget r (pget s n))) (eqAt p q r s n) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, Nat.beq_eq, eqAt_iff p q r s n]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

theorem compL_getD {a b : List ℕ} {i : ℕ} (hi : i < b.length) :
    (compL a b).getD i 0 = a.getD (b.getD i 0) 0 := by
  simp only [compL, List.getD_eq_getElem _ _ hi,
    List.getD_eq_getElem _ _ (by simpa using hi : i < (b.map _).length), List.getElem_map]

theorem beq_compL {N : ℕ} {a b c d : List ℕ} (hb : b.length = N) (hd : d.length = N)
    (ha : Small a) (hb' : Small b) (hc : Small c) (hd' : Small d) :
    (compL a b == compL c d) = eqAt (encL a) (encL b) (encL c) (encL d) N := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, eqAt_iff]
  have hl1 : (compL a b).length = N := by simp [compL, hb]
  have hl2 : (compL c d).length = N := by simp [compL, hd]
  constructor
  · intro h i hi
    have := congrArg (fun l => l.getD i 0) h
    rw [compL_getD (by omega), compL_getD (by omega)] at this
    rw [pget_encL b hb', pget_encL d hd', pget_encL a ha, pget_encL c hc]
    exact this
  · intro h
    apply List.ext_getElem (hl1.trans hl2.symm)
    intro i h1 h2
    have e := h i (by omega)
    rw [pget_encL b hb', pget_encL d hd', pget_encL a ha, pget_encL c hc,
      ← compL_getD (by omega), ← compL_getD (by omega)] at e
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at e

theorem getK_eq : ∀ (l : List ℕ) (i : ℕ), getK l i = l.getD i 0
  | [], _ => rfl
  | x :: l, i => by
    change Bool.rec (motive := fun _ => ℕ) (getK l (Nat.sub i 1)) x (Nat.beq i 0) = _
    cases i with
    | zero => rfl
    | succ i =>
      change getK l i = _
      rw [getK_eq l i, List.getD_cons_succ]

theorem getK_map_encL (L : List (List ℕ)) (i : ℕ) : getK (L.map encL) i = encL (L.getD i []) := by
  rw [getK_eq, ← encL_nil, List.getD_map]

theorem setT_spec : ∀ (l : List ℕ), OrdN (setT l) ∧ ∀ y, memN (setT l) y ↔ y ∈ l
  | [] => ⟨trivial, fun y => by simp [setT, memN]⟩
  | x :: l => by
    have e : setT (x :: l) = insT (setT l) x := rfl
    obtain ⟨ho, hm⟩ := setT_spec l
    refine ⟨e ▸ ord_insT x ho, fun y => ?_⟩
    rw [e, mem_insT, hm, List.mem_cons]

theorem memT_setT (l : List ℕ) (x : ℕ) : memT (setT l) x = l.contains x := by
  apply Bool.eq_iff_iff.2
  rw [memT_iff (setT_spec l).1, (setT_spec l).2, List.contains_iff_mem]

section Words

variable {N n : ℕ} {LS LSi : List (List ℕ)}

structure LetOK (N n : ℕ) (LS LSi : List (List ℕ)) : Prop where
  hN : N ≤ 64
  hS : n ≤ LS.length
  hSi : n ≤ LSi.length
  hv : ∀ l ∈ LS ++ LSi, l.length = N ∧ ∀ e ∈ l, e < 64

def Val (N : ℕ) (l : List ℕ) : Prop := l.length = N ∧ Small l

theorem val_letL (h : LetOK N n LS LSi) (l : Fin n × Bool) :
    Val N (burnsideF48s_eLetL LS LSi l) := by
  obtain ⟨i, b⟩ := l
  cases b
  · have hi : (i : ℕ) < LSi.length := lt_of_lt_of_le i.2 h.hSi
    have hm : LSi.getD i [] ∈ LS ++ LSi := List.mem_append_right _ (burnsideF48s_e_getD_mem _ hi _)
    exact h.hv _ hm
  · have hi : (i : ℕ) < LS.length := lt_of_lt_of_le i.2 h.hS
    have hm : LS.getD i [] ∈ LS ++ LSi := List.mem_append_left _ (burnsideF48s_e_getD_mem _ hi _)
    exact h.hv _ hm

theorem encL_letL (l : Fin n × Bool) :
    encL (burnsideF48s_eLetL LS LSi l) = letK (LS.map encL) (LSi.map encL) l := by
  obtain ⟨i, b⟩ := l
  cases b <;> simp only [letK, burnsideF48s_eLetL] <;> rw [getK_map_encL] <;> rfl

theorem ev_from (h : LetOK N n LS LSi) : ∀ (w : List (Fin n × Bool)) (acc : List ℕ), Val N acc →
    Val N (w.foldl (fun acc l => compL acc (burnsideF48s_eLetL LS LSi l)) acc) ∧
      encL (w.foldl (fun acc l => compL acc (burnsideF48s_eLetL LS LSi l)) acc) =
        evFrom N (LS.map encL) (LSi.map encL) w (encL acc)
  | [], _, hacc => ⟨hacc, rfl⟩
  | l :: w, acc, hacc => by
    have hL := val_letL h l
    have hv : Val N (compL acc (burnsideF48s_eLetL LS LSi l)) :=
      ⟨by simp [compL, hL.1], small_compL hacc.2 _⟩
    obtain ⟨h1, h2⟩ := ev_from h w _ hv
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, encL_compL hacc.2 hL.2, hL.1, encL_letL]
    rfl

theorem val_range (h : LetOK N n LS LSi) : Val N (List.range N) :=
  ⟨List.length_range, fun e he => lt_of_lt_of_le (List.mem_range.1 he) h.hN⟩

theorem val_ev (h : LetOK N n LS LSi) (w : List (Fin n × Bool)) :
    Val N (burnsideF48s_eEvL N LS LSi w) :=
  (ev_from h w _ (val_range h)).1

theorem encL_ev (h : LetOK N n LS LSi) (w : List (Fin n × Bool)) :
    encL (burnsideF48s_eEvL N LS LSi w) = evK N (LS.map encL) (LSi.map encL) w :=
  (ev_from h w _ (val_range h)).2

theorem contains_val (h : LetOK N n LS LSi) (W : List (List (Fin n × Bool))) {x : List ℕ}
    (hx : Val N x) : (W.map (burnsideF48s_eEvL N LS LSi)).contains x =
      memT (setT (W.map (evK N (LS.map encL) (LSi.map encL)))) (encL x) := by
  rw [memT_setT]
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.contains_iff_mem, List.mem_map, List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (encL_ev h w).symm⟩
  · rintro ⟨w, hw, e⟩
    refine ⟨w, hw, encL_inj ((val_ev h w).1.trans hx.1.symm) (val_ev h w).2 hx.2 ?_⟩
    rw [encL_ev h w, e]

theorem contains_ev (h : LetOK N n LS LSi) (W : List (List (Fin n × Bool)))
    (w : List (Fin n × Bool)) : (W.map (burnsideF48s_eEvL N LS LSi)).contains
      (burnsideF48s_eEvL N LS LSi w) =
      memT (setT (W.map (evK N (LS.map encL) (LSi.map encL)))) (evK N (LS.map encL) (LSi.map encL) w) := by
  rw [contains_val h W (val_ev h w), encL_ev h w]

theorem encL_compL_ev (h : LetOK N n LS LSi) (a b : List (Fin n × Bool)) :
    encL (compL (burnsideF48s_eEvL N LS LSi a) (burnsideF48s_eEvL N LS LSi b)) =
      pcomp (evK N (LS.map encL) (LSi.map encL) a) N (evK N (LS.map encL) (LSi.map encL) b) := by
  rw [encL_compL (val_ev h a).2 (val_ev h b).2, (val_ev h b).1, encL_ev h, encL_ev h]

theorem contains_compL_ev (h : LetOK N n LS LSi) (W : List (List (Fin n × Bool)))
    (a b : List (Fin n × Bool)) : (W.map (burnsideF48s_eEvL N LS LSi)).contains
      (compL (burnsideF48s_eEvL N LS LSi a) (burnsideF48s_eEvL N LS LSi b)) =
      memT (setT (W.map (evK N (LS.map encL) (LSi.map encL))))
        (pcomp (evK N (LS.map encL) (LSi.map encL) a) N (evK N (LS.map encL) (LSi.map encL) b)) := by
  have hv : Val N (compL (burnsideF48s_eEvL N LS LSi a) (burnsideF48s_eEvL N LS LSi b)) :=
    ⟨by simp [compL, (val_ev h b).1], small_compL (val_ev h a).2 _⟩
  rw [contains_val h W hv, encL_compL_ev h]

theorem beq_ev (h : LetOK N n LS LSi) (a b c d : List (Fin n × Bool)) :
    (compL (burnsideF48s_eEvL N LS LSi a) (burnsideF48s_eEvL N LS LSi b) ==
      compL (burnsideF48s_eEvL N LS LSi c) (burnsideF48s_eEvL N LS LSi d)) =
      eqAt (evK N (LS.map encL) (LSi.map encL) a) (evK N (LS.map encL) (LSi.map encL) b)
        (evK N (LS.map encL) (LSi.map encL) c) (evK N (LS.map encL) (LSi.map encL) d) N := by
  rw [beq_compL (val_ev h b).1 (val_ev h d).1 (val_ev h a).2 (val_ev h b).2 (val_ev h c).2
    (val_ev h d).2, encL_ev h, encL_ev h, encL_ev h, encL_ev h]

theorem small_getD_ev (h : LetOK N n LS LSi) (U : List (List (Fin n × Bool))) (k : ℕ) :
    Small ((U.map (burnsideF48s_eEvL N LS LSi)).getD k []) := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : (U.map (burnsideF48s_eEvL N LS LSi))[k]? with
  | none => intro e he; simp at he
  | some v =>
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hk)
    exact (val_ev h w).2

theorem beq_getD_ev (h : LetOK N n LS LSi) (U : List (List (Fin n × Bool))) (k : ℕ)
    (a b d : List (Fin n × Bool)) :
    (compL (burnsideF48s_eEvL N LS LSi a) (burnsideF48s_eEvL N LS LSi b) ==
      compL ((U.map (burnsideF48s_eEvL N LS LSi)).getD k []) (burnsideF48s_eEvL N LS LSi d)) =
      eqAt (evK N (LS.map encL) (LSi.map encL) a) (evK N (LS.map encL) (LSi.map encL) b)
        (getK (U.map (evK N (LS.map encL) (LSi.map encL))) k)
        (evK N (LS.map encL) (LSi.map encL) d) N := by
  rw [beq_compL (val_ev h b).1 (val_ev h d).1 (val_ev h a).2 (val_ev h b).2 (small_getD_ev h U k)
    (val_ev h d).2, encL_ev h, encL_ev h, encL_ev h]
  congr 1
  rw [getK_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_map]
  cases U[k]? with
  | none => rfl
  | some w => exact encL_ev h w

theorem eNorm_ev (h : LetOK N n LS LSi) (K : List (List (Fin n × Bool))) (w : List (Fin n × Bool)) :
    burnsideF48s_eNorm (K.map (burnsideF48s_eEvL N LS LSi)) (burnsideF48s_eEvL N LS LSi w) =
      normK N (K.map (evK N (LS.map encL) (LSi.map encL))) (evK N (LS.map encL) (LSi.map encL) w) := by
  simp only [burnsideF48s_eNorm, normK, allA_eq, anyA_eq, List.all_map, List.any_map,
    Function.comp_def, beq_ev h]

theorem eClosedW_ev (h : LetOK N n LS LSi) (W G : List (List (Fin n × Bool))) :
    burnsideF48s_eClosedW (W.map (burnsideF48s_eEvL N LS LSi)) (G.map (burnsideF48s_eEvL N LS LSi)) =
      closedK N (setT (W.map (evK N (LS.map encL) (LSi.map encL))))
        (W.map (evK N (LS.map encL) (LSi.map encL))) (G.map (evK N (LS.map encL) (LSi.map encL))) := by
  simp only [burnsideF48s_eClosedW, closedK, allA_eq, List.all_map, Function.comp_def,
    contains_compL_ev h]

theorem eClosed_ev (h : LetOK N n LS LSi) (W : List (List (Fin n × Bool))) (gs : List ℕ)
    (hg : ∀ g ∈ gs, g < n) :
    burnsideF48s_eClosed (W.map (burnsideF48s_eEvL N LS LSi)) LS gs =
      closedK N (setT (W.map (evK N (LS.map encL) (LSi.map encL))))
        (W.map (evK N (LS.map encL) (LSi.map encL))) (gs.map (getK (LS.map encL))) := by
  simp only [burnsideF48s_eClosed, closedK, allA_eq, List.all_map, Function.comp_def]
  apply List.all_congr rfl
  intro w
  have key : ∀ g ∈ gs, (W.map (burnsideF48s_eEvL N LS LSi)).contains
      (compL (burnsideF48s_eEvL N LS LSi w) (LS.getD g [])) =
      memT (setT (W.map (evK N (LS.map encL) (LSi.map encL))))
        (pcomp (evK N (LS.map encL) (LSi.map encL) w) N (getK (LS.map encL) g)) := by
    intro g hgm
    have hgl : g < LS.length := lt_of_lt_of_le (hg g hgm) h.hS
    have hL : Val N (LS.getD g []) :=
      h.hv _ (List.mem_append_left _ (burnsideF48s_e_getD_mem _ hgl _))
    have hv : Val N (compL (burnsideF48s_eEvL N LS LSi w) (LS.getD g [])) :=
      ⟨by simp only [compL, List.length_map]; exact hL.1, small_compL (val_ev h w).2 _⟩
    rw [contains_val h W hv, encL_compL (val_ev h w).2 hL.2, hL.1, encL_ev h, getK_map_encL]
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  exact ⟨fun H g hg => by rw [← key g hg]; exact H g hg,
    fun H g hg => by rw [key g hg]; exact H g hg⟩

theorem eCandOK_ev (h : LetOK N n LS LSi) (P1 P2 K T U V W : List (List (Fin n × Bool))) :
    burnsideF48s_eCandOK (P1.map (burnsideF48s_eEvL N LS LSi)) (P2.map (burnsideF48s_eEvL N LS LSi))
      (K.map (burnsideF48s_eEvL N LS LSi)) (T.map (burnsideF48s_eEvL N LS LSi))
      (U.map (burnsideF48s_eEvL N LS LSi)) (V.map (burnsideF48s_eEvL N LS LSi))
      (W.map (burnsideF48s_eEvL N LS LSi)) =
      candK N (setT (P1.map (evK N (LS.map encL) (LSi.map encL))))
        (setT (P2.map (evK N (LS.map encL) (LSi.map encL))))
        (P1.map (evK N (LS.map encL) (LSi.map encL))) (P2.map (evK N (LS.map encL) (LSi.map encL)))
        (K.map (evK N (LS.map encL) (LSi.map encL))) (T.map (evK N (LS.map encL) (LSi.map encL)))
        (uvwK (U.map (evK N (LS.map encL) (LSi.map encL))) (V.map (evK N (LS.map encL) (LSi.map encL)))
          (W.map (evK N (LS.map encL) (LSi.map encL))) U.length) := by
  simp only [burnsideF48s_eCandOK, candK, uvwK, allA_eq, anyA_eq, orB_eq, notB_eq, andB_eq,
    List.all_map, List.any_map, Function.comp_def, List.length_map, eNorm_ev h, Bool.or_assoc,
    Bool.and_assoc,
    contains_compL_ev h, contains_ev h, beq_ev h, beq_getD_ev h]

end Words

end CFSG.KC.F48S
