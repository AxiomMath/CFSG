module

public import Certificates.Data.Kernel.Cert690.SqA8T
public import CFSG.Certificates.Kernel.Cert690.SqA8Sound

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62 CFSG.KC.Enum

theorem fB_spec (g : ℕ) : ∀ n v, v < 64 → v ≤ n → fB g n v = (fTable g 0)[v]!
  | 0, v, _, hv => by
    obtain rfl : v = 0 := by omega
    rw [fTable_getElem!_zero]
    rfl
  | n + 1, v, h64, hv => by
    have e : fB g (n + 1) v = if v = 0 then false else
        (fB g n (v ^^^ (1 <<< lowIdx v)) ^^
          b0n (Code.act g (v ^^^ (1 <<< lowIdx v))) (Code.act g (1 <<< lowIdx v)) ^^
          b0n (v ^^^ (1 <<< lowIdx v)) (1 <<< lowIdx v)) := rfl
    rw [e]
    by_cases h0 : v = 0
    · subst h0
      rw [if_pos rfl, fTable_getElem!_zero]
    · have hlt := lowIdx_xor_lt h0 h64
      rw [if_neg h0, fB_spec g n _ (by omega) (by omega), fTable_getElem!_succ h64 h0,
        Nat.zero_testBit, Bool.xor_false]

theorem fTable_eq_fB (g f : ℕ) {v : ℕ} (hv : v < 64) :
    (fTable g f)[v]! = (fB g 64 v ^^ dotN f v) := by
  rw [fTable_twist g f v hv, fB_spec g 64 v hv hv.le]
  rfl

theorem liftTab_eqF (g f : ℕ) {x : ℕ} (hx : x < 128) : (liftTab g f)[x]! = liftF g f x := by
  rw [liftTab_getElem! hx, fTable_eq_fB g f (by omega : x / 2 < 64)]
  rfl

theorem ite_lt2 (b : Bool) : (if b then 1 else 0) < 2 := by cases b <;> decide

theorem liftF_lt (g f x : ℕ) : liftF g f x < 128 := by
  unfold liftF
  have h1 := xor_lt2 (Nat.mod_lt x (by norm_num : 0 < 2))
    (ite_lt2 (fB g 64 (x / 2) ^^ dotN f (x / 2)))
  have h2 := Code.act_lt g (x / 2)
  omega

theorem invF_lt (g g' f y : ℕ) : invF g g' f y < 128 := by
  unfold invF
  have h1 := xor_lt2 (Nat.mod_lt y (by norm_num : 0 < 2))
    (ite_lt2 (fB g 64 (Code.act g' (y / 2)) ^^ dotN f (Code.act g' (y / 2))))
  have h2 := Code.act_lt g' (y / 2)
  omega

theorem liftF_invF {g g' : ℕ} (f : ℕ) (h : ∀ u < 64, Code.act g (Code.act g' u) = u) {y : ℕ}
    (hy : y < 128) : liftF g f (invF g g' f y) = y := by
  unfold liftF invF
  generalize hc : (y % 2 ^^^ (if (fB g 64 (Code.act g' (y / 2)) ^^ dotN f (Code.act g' (y / 2)))
    then 1 else 0)) = c
  have hc2 : c < 2 := by
    rw [← hc]
    exact xor_lt2 (Nat.mod_lt y (by norm_num)) (ite_lt2 _)
  rw [mk_mod hc2, mk_div hc2, h _ (by omega), ← hc, xor_xor_cancel]
  omega

theorem invF_liftF {g g' : ℕ} (f : ℕ) (h : ∀ u < 64, Code.act g' (Code.act g u) = u) {x : ℕ}
    (hx : x < 128) : invF g g' f (liftF g f x) = x := by
  unfold liftF invF
  generalize hc : (x % 2 ^^^ (if (fB g 64 (x / 2) ^^ dotN f (x / 2)) then 1 else 0)) = c
  have hc2 : c < 2 := by
    rw [← hc]
    exact xor_lt2 (Nat.mod_lt x (by norm_num)) (ite_lt2 _)
  rw [mk_mod hc2, mk_div hc2, h _ (by omega), ← hc, xor_xor_cancel]
  omega

theorem invTab_fn {t : Array ℕ} (hs : t.size = 128) {φ ψ : ℕ → ℕ}
    (ht : ∀ x < 128, t[x]! = φ x) (hφ : ∀ x < 128, φ x < 128) (hψ : ∀ y < 128, ψ y < 128)
    (hφψ : ∀ y < 128, φ (ψ y) = y) (hψφ : ∀ x < 128, ψ (φ x) = x) {y : ℕ} (hy : y < 128) :
    (invTab t)[y]! = ψ y := by
  have hinj : ∀ i < 128, ∀ j < 128, t[i]! = t[j]! → i = j := by
    intro i hi j hj e
    rw [ht i hi, ht j hj] at e
    rw [← hψφ i hi, e, hψφ j hj]
  have hlt : ∀ i < 128, t[i]! < 128 := by
    intro i hi
    rw [ht i hi]
    exact hφ i hi
  have h := invTab_getElem! hs hlt hinj (hψ y hy)
  rwa [ht _ (hψ y hy), hφψ y hy] at h

theorem compTab_size (s t : Array ℕ) : (compTab s t).size = 128 := by simp [compTab]

section Wit

variable {k k' r : ℕ} (hk : ∀ u < 64, Code.act k (Code.act k' u) = u)
  (hk' : ∀ u < 64, Code.act k' (Code.act k u) = u) (hr : ∀ u < 64, Code.act r (Code.act r u) = u)

include hk hk' in
theorem ipsi_eq {y : ℕ} (hy : y < 128) : (invTab (liftTab k 0))[y]! = invF k k' 0 y :=
  invTab_fn (liftTab_size k 0) (fun _ hx => liftTab_eqF k 0 hx) (fun x _ => liftF_lt k 0 x)
    (fun y _ => invF_lt k k' 0 y) (fun _ hy => liftF_invF 0 hk hy)
    (fun _ hx => invF_liftF 0 hk' hx) hy

include hk hk' in
theorem tp_eq {x : ℕ} (hx : x < 128) :
    (compTab (compTab (liftTab k 0) (liftTab r 0)) (invTab (liftTab k 0)))[x]! =
      liftF k 0 (liftF r 0 (invF k k' 0 x)) := by
  rw [compTab_getElem! _ _ hx, ipsi_eq hk hk' hx, compTab_getElem! _ _ (invF_lt _ _ _ _),
    liftTab_eqF r 0 (invF_lt _ _ _ _), liftTab_eqF k 0 (liftF_lt _ _ _)]

include hk hk' hr in
theorem itp_eq {y : ℕ} (hy : y < 128) :
    (invTab (compTab (compTab (liftTab k 0) (liftTab r 0)) (invTab (liftTab k 0))))[y]! =
      liftF k 0 (invF r r 0 (invF k k' 0 y)) := by
  refine invTab_fn (φ := fun x => liftF k 0 (liftF r 0 (invF k k' 0 x)))
    (ψ := fun y => liftF k 0 (invF r r 0 (invF k k' 0 y))) (compTab_size _ _)
    (fun _ hx => tp_eq hk hk' hx) (fun x _ => liftF_lt _ _ _)
    (fun y _ => liftF_lt _ _ _) (fun y hy => ?_) (fun x hx => ?_) hy
  · rw [invF_liftF 0 hk' (invF_lt _ _ _ _), liftF_invF 0 hr (invF_lt _ _ _ _),
      liftF_invF 0 hk hy]
  · rw [invF_liftF 0 hk' (liftF_lt _ _ _), invF_liftF 0 hr (invF_lt _ _ _ _),
      liftF_invF 0 hk hx]

end Wit

theorem all_range_congr {n : ℕ} {p q : ℕ → Bool} (h : ∀ x < n, p x = q x) :
    (List.range n).all p = (List.range n).all q := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro hp x hx
    rw [← h x (List.mem_range.1 hx)]
    exact hp x hx
  · intro hq x hx
    rw [h x (List.mem_range.1 hx)]
    exact hq x hx

theorem beq_arr {a b : Array ℕ} (ha : a.size = 128) (hb : b.size = 128) :
    (a == b) = (List.range 128).all fun x => a[x]! == b[x]! := by
  rw [Bool.eq_iff_iff, beq_iff_eq, List.all_eq_true]
  constructor
  · rintro rfl x _
    exact beq_self_eq_true _
  · intro h
    apply array_eq_of_getElem!_eq ha hb
    intro i hi
    exact beq_iff_eq.1 (h i (List.mem_range.2 hi))

theorem innW_eqF {X : Array ℕ} {φ : ℕ → ℕ} (hX : ∀ x < 128, X[x]! = φ x) :
    innW X = innWF φ := by
  unfold innW innWF
  rw [hX 2 (by norm_num), hX 4 (by norm_num), hX 8 (by norm_num), hX 16 (by norm_num),
    hX 32 (by norm_num), hX 64 (by norm_num)]

theorem innGuess_eqF {X : Array ℕ} (hs : X.size = 128) (φ : ℕ → ℕ)
    (hX : ∀ x < 128, X[x]! = φ x) : innGuess X = guessF φ := by
  unfold innGuess guessF
  rw [innW_eqF hX, beq_arr (innTab_size _) hs]
  have hc : ((List.range 128).all fun x => (innTab (2 * innWF φ))[x]! == X[x]!) =
      (List.range 128).all fun x => qmulN (qmulN (qinvN (2 * innWF φ)) x) (2 * innWF φ) == φ x :=
    all_range_congr fun x hx => by rw [innTab_getElem! _ hx, hX x hx]
  rw [hc]

theorem candValOne_eq (f : ℕ) : candValOne (innTabs ()) (liftTab Code.one f) = candOneT f := by
  unfold candValOne candOneT
  rw [findInn_eq_innGuess, innGuess_eqF (liftTab_size _ _) (liftF Code.one f)
    (fun _ hx => liftTab_eqF _ _ hx)]
  cases guessF (liftF Code.one f) <;> rfl

theorem candVal_eqT (r₁ r₂ : ℕ) (w : ℕ × ℕ × ℕ × ℕ) (f : ℕ) (b : Bool × Bool)
    (hk : ∀ u < 64, Code.act w.2.2.1 (Code.act w.2.2.2 u) = u)
    (hk' : ∀ u < 64, Code.act w.2.2.2 (Code.act w.2.2.1 u) = u)
    (hr : ∀ u < 64, Code.act (if w.2.1 = 0 then r₁ else r₂)
      (Code.act (if w.2.1 = 0 then r₁ else r₂) u) = u)
    (hs : sOf #[rootF r₁, rootF r₂] b.1 b.2 w.2.1 < 128) :
    candVal (innTabs ()) (liftTab w.1 f) (liftTab w.2.2.1 0)
      (compTab (compTab (liftTab w.2.2.1 0) (liftTab (if w.2.1 = 0 then r₁ else r₂) 0))
        (invTab (liftTab w.2.2.1 0)))
      (invTab (compTab (compTab (liftTab w.2.2.1 0) (liftTab (if w.2.1 = 0 then r₁ else r₂) 0))
        (invTab (liftTab w.2.2.1 0))))
      (sOf #[rootF r₁, rootF r₂] b.1 b.2 w.2.1) = candT r₁ r₂ w f b := by
  unfold candVal candT
  rw [findInn_eq_innGuess, innGuess_eqF (compTab_size _ _)
    (fun x => liftF w.1 f (liftF w.2.2.1 0 (invF (if w.2.1 = 0 then r₁ else r₂)
      (if w.2.1 = 0 then r₁ else r₂) 0 (invF w.2.2.1 w.2.2.2 0 x))))
    (fun x hx => by rw [compTab_getElem! _ _ hx, itp_eq hk hk' hr hx, liftTab_eqF _ _ (liftF_lt _ _ _)])]
  rcases guessF (fun x => liftF w.1 f (liftF w.2.2.1 0 (invF (if w.2.1 = 0 then r₁ else r₂)
      (if w.2.1 = 0 then r₁ else r₂) 0 (invF w.2.2.1 w.2.2.2 0 x)))) with _ | e
  · rfl
  · dsimp only
    by_cases he : e < 128
    · rw [if_pos he, if_pos he, liftTab_eqF _ _ hs, tp_eq hk hk' he]
    · rw [if_neg he, if_neg he]

theorem innWF_lt (φ : ℕ → ℕ) : innWF φ < 64 := by
  unfold innWF
  have := Nat.mod_lt (φ 2) (by norm_num : 0 < 2)
  have := Nat.mod_lt (φ 4) (by norm_num : 0 < 2)
  have := Nat.mod_lt (φ 8) (by norm_num : 0 < 2)
  have := Nat.mod_lt (φ 16) (by norm_num : 0 < 2)
  have := Nat.mod_lt (φ 32) (by norm_num : 0 < 2)
  have := Nat.mod_lt (φ 64) (by norm_num : 0 < 2)
  omega

theorem qmulN_lt {x y : ℕ} (hx : x < 128) (hy : y < 128) : qmulN x y < 128 := by
  simp only [qmulN]
  have h1 := xor_lt2 (xor_lt2 (Nat.mod_lt x (by norm_num : 0 < 2))
    (Nat.mod_lt y (by norm_num : 0 < 2))) (ite_lt2 (b0n (x / 2) (y / 2)))
  have h2 := xor_lt64 (by omega : x / 2 < 64) (by omega : y / 2 < 64)
  omega

theorem sOf_lt (r₁ r₂ : ℕ) (b₀ b₁ : Bool) {i : ℕ} (hi : i < 2) :
    sOf #[rootF r₁, rootF r₂] b₀ b₁ i < 128 := by
  have h1 : rootF r₁ < 128 := by have := innWF_lt fun x => liftF r₁ 0 (liftF r₁ 0 x); unfold rootF; omega
  have h2 : rootF r₂ < 128 := by have := innWF_lt fun x => liftF r₂ 0 (liftF r₂ 0 x); unfold rootF; omega
  have hz : z0N < 128 := by decide
  have g0 : (#[rootF r₁, rootF r₂] : Array ℕ)[0]! = rootF r₁ := rfl
  have g1 : (#[rootF r₁, rootF r₂] : Array ℕ)[1]! = rootF r₂ := rfl
  interval_cases i <;> cases b₀ <;> cases b₁ <;>
    simp [sOf, g0, g1, qmulN_lt h1 hz, qmulN_lt h2 hz, h1, h2]

theorem flatMap_filter_eq {α : Type} {p : ℕ → Bool} {G : ℕ → List α} :
    ∀ (l : List ℕ), (∀ g ∈ l, p g = false → G g = []) → l.flatMap G = (l.filter p).flatMap G
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.filter_cons,
      flatMap_filter_eq l (fun g hg => h g (List.mem_cons_of_mem a hg))]
    by_cases ha : p a = true
    · rw [if_pos ha, List.flatMap_cons]
    · rw [if_neg ha, h a List.mem_cons_self (by simpa using ha), List.nil_append]

theorem foldl_push_gens (gens : Array ℕ) (P : ℕ → ℕ → Bool) (F : ℕ → ℕ → Option ℕ) :
    gens.foldl (fun acc g => (List.range 64).foldl (fun acc f =>
        if P g f then acc.push (F g f) else acc) acc) #[] =
      (gens.toList.flatMap fun g => ((List.range 64).filter (P g)).map (F g)).toArray := by
  have key : ∀ (l : List ℕ) (acc : Array (Option ℕ)),
      (l.foldl (fun acc g => (List.range 64).foldl (fun acc f =>
        if P g f then acc.push (F g f) else acc) acc) acc).toList =
      acc.toList ++ l.flatMap fun g => ((List.range 64).filter (P g)).map (F g) := by
    have inner : ∀ (g : ℕ) (m : List ℕ) (acc : Array (Option ℕ)),
        (m.foldl (fun acc f => if P g f then acc.push (F g f) else acc) acc).toList =
          acc.toList ++ (m.filter (P g)).map (F g) := by
      intro g m
      induction m with
      | nil => intro acc; simp
      | cons a m ih =>
        intro acc
        rw [List.foldl_cons, List.filter_cons]
        by_cases h : P g a = true
        · rw [if_pos h, ih, if_pos h, Array.toList_push]
          simp [List.append_assoc]
        · rw [if_neg h, ih, if_neg h]
    intro l
    induction l with
    | nil => intro acc; simp
    | cons g l ih =>
      intro acc
      rw [List.foldl_cons, ih, inner, List.flatMap_cons, List.append_assoc]
  apply Array.toList_inj.mp
  rw [← Array.foldl_toList, key]
  simp

theorem witMap_foldl_get? {R : ℕ → Option SqWit} (hR : ∀ g w, R g = some w → w.g = g)
    {g : ℕ} {w : SqWit} (hg : R g = some w) : ∀ (l : List ℕ) (m : Std.HashMap ℕ SqWit),
    (g ∈ l ∨ m.get? g = some w) →
    ((l.map R).foldl (fun m o => match o with
      | some w => m.insert w.g w
      | none => m) m).get? g = some w
  | [], m, h => by
    rcases h with h | h
    · simp at h
    · exact h
  | a :: l, m, h => by
    rw [List.map_cons, List.foldl_cons]
    apply witMap_foldl_get? hR hg l
    by_cases hl : g ∈ l
    · exact Or.inl hl
    · right
      by_cases hga : g = a
      · subst hga
        rw [hg]
        dsimp only
        rw [Std.HashMap.get?_insert, hR g w hg, if_pos (beq_self_eq_true g)]
      · have hm : m.get? g = some w := by
          rcases h with h | h
          · rcases List.mem_cons.1 h with h | h
            · exact absurd h hga
            · exact absurd h hl
          · exact h
        cases ha : R a with
        | none => exact hm
        | some w' =>
          dsimp only
          rw [Std.HashMap.get?_insert, hR a w' ha, if_neg (by
            rw [beq_iff_eq]
            exact fun e => hga e.symm)]
          exact hm

theorem flatMap_map_congr {α β : Type} {G : ℕ → List β} {H : α → List β} {p : α → ℕ} :
    ∀ (l : List α), (∀ a ∈ l, G (p a) = H a) → (l.map p).flatMap G = l.flatMap H
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_map_congr l (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem liftTab_a0 (g f : ℕ) :
    ((liftTab g f)[a0N]! == a0N) = (Code.act g 1 == 1 && !f.testBit 0) := by
  have e1 : (fTable g f)[1]! = f.testBit 0 := by
    have := fTable_two_pow (g := g) (f := f) (j := 0) (by norm_num)
    simpa using this
  rw [a0N, liftTab_getElem! (by norm_num : 2 < 128)]
  simp only [Nat.reduceMod, Nat.reduceDiv, e1, Nat.zero_xor]
  cases f.testBit 0 <;> simp <;> omega

theorem a0_filter (g : ℕ) : ((List.range 64).filter fun f => (liftTab g f)[a0N]! == a0N) =
    if Code.act g 1 = 1 then evensF else [] := by
  simp only [liftTab_a0]
  split
  · next hg =>
    unfold evensF
    simp [hg]
  · next hg =>
    simp [hg]

theorem act_one_one : Code.act Code.one 1 = 1 := by decide

theorem theta_get {r₁ r₂ i : ℕ} (hi : i < 2) :
    (#[liftTab r₁ 0, liftTab r₂ 0] : Array (Array ℕ))[i]! =
      liftTab (if i = 0 then r₁ else r₂) 0 := by
  rw [getElem!_pos _ i (by simpa using hi)]
  interval_cases i <;> simp

theorem root_eqF {r : ℕ} (h : (innTab (2 * innW (compTab (liftTab r 0) (liftTab r 0))) ==
    compTab (liftTab r 0) (liftTab r 0)) = true) :
    (innRoots (innTabs ()) (compTab (liftTab r 0) (liftTab r 0))).head?.getD 0 = rootF r := by
  rw [innRoots_eq, if_pos h]
  simp only [List.head?_cons, Option.getD_some]
  unfold rootF
  rw [innW_eqF (φ := fun x => liftF r 0 (liftF r 0 x)) (fun x hx => by
    rw [compTab_getElem! _ _ hx, liftTab_eqF r 0 hx, liftTab_eqF r 0 (liftF_lt _ _ _)])]

theorem invPair_spec {a b : ℕ} (h : invPair a b = true) :
    (∀ u < 64, Code.act a (Code.act b u) = u) ∧ (∀ u < 64, Code.act b (Code.act a u) = u) := by
  unfold invPair at h
  rw [List.all_eq_true] at h
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have e := h u (List.mem_range.2 hu)
    simp only [Bool.and_eq_true, beq_iff_eq] at e
    exact e.1
  · have e := h u (List.mem_range.2 hu)
    simp only [Bool.and_eq_true, beq_iff_eq] at e
    exact e.2

section

variable {L : List ℕ} {P : List (ℕ × ℕ)} (hE : enumData a8Gens = (L.toArray, P.toArray))
include hE

theorem a8_root : (a8Data ()).root =
    repRoot (innTabs ()) (repThetas (twoClassReps L.toArray (invsL L).toArray)) := by
  simp only [a8Data, hE, invArr_eq]

theorem a8_witMap : (a8Data ()).witMap = witMapOf
    (sqWitData (classMapOfReps L.toArray (invsL L).toArray (twoClassReps L.toArray (invsL L).toArray))
      (repThetas (twoClassReps L.toArray (invsL L).toArray)) (involL L).toArray) := by
  simp only [a8Data, hE, invArr_eq, invsOf, involL, List.filter_toArray, isInvCode_eq]

end

namespace A8Hyp

variable {L : List ℕ} {P : List (ℕ × ℕ)} {T W1 W2 : IT} {M1 M2 r1 r2 : ℕ}
  (h : A8Hyp L P T W1 W2 M1 M2 r1 r2)
include h

theorem root_eq : (a8Data ()).root = #[rootF r1, rootF r2] := by
  rw [a8_root h.enum, h.reps, h.theta_eq]
  unfold repRoot
  simp only [List.map_toArray, List.map_cons, List.map_nil]
  rw [root_eqF h.root1, root_eqF h.root2]

theorem cm_get_of {w : ℕ × ℕ × ℕ × ℕ} (hw : cmK T W1 W2 L.length M1 M2 w = true) :
    (classMapOfReps L.toArray (invsL L).toArray #[r1, r2]).get? w.1 = some (w.2.1, w.2.2.1) ∧
      w.2.1 < 2 := by
  unfold cmK at hw
  rw [Bool.and_eq_true, Nat.blt_eq] at hw
  obtain ⟨hq, hw⟩ := hw
  have hkL : L[T.find w.2.2.1 L.length]! = w.2.2.1 := by
    rw [h.ix] at hq ⊢
    rw [getElem!_pos L _ hq]
    exact List.getElem_idxOf hq
  rw [classMapOfReps_two_get?, h.fc1, h.fc2]
  split at hw
  · next hi =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    rw [if_pos hw.1, hw.2, hkL]
    simp [hi]
  · next hi =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hw
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hw
    rw [if_neg (by simp [h2]), if_pos h3, h4, hkL]
    simp [h1]

variable {Ws : List (ℕ × ℕ × ℕ × ℕ)}
  (hsel : ((involL L).filter fun g => Code.act g 1 == 1) = Ws.map Prod.fst)
include hsel

omit h in
theorem mem_sel {w : ℕ × ℕ × ℕ × ℕ} (hw : w ∈ Ws) : w.1 ∈ involL L ∧ Code.act w.1 1 = 1 := by
  have e : w.1 ∈ (involL L).filter fun g => Code.act g 1 == 1 := by
    rw [hsel]
    exact List.mem_map_of_mem hw
  rw [List.mem_filter, beq_iff_eq] at e
  exact e

theorem wit_get (hcm : ∀ w ∈ Ws, cmK T W1 W2 L.length M1 M2 w = true) {w : ℕ × ℕ × ℕ × ℕ}
    (hw : w ∈ Ws) : (a8Data ()).witMap.get? w.1 = some
      { g := w.1, repIdx := w.2.1, k := w.2.2.1, psi := liftTab w.2.2.1 0,
        tp := compTab (compTab (liftTab w.2.2.1 0)
          ((#[liftTab r1 0, liftTab r2 0] : Array (Array ℕ))[w.2.1]!)) (invTab (liftTab w.2.2.1 0)),
        itp := invTab (compTab (compTab (liftTab w.2.2.1 0)
          ((#[liftTab r1 0, liftTab r2 0] : Array (Array ℕ))[w.2.1]!))
          (invTab (liftTab w.2.2.1 0))) } := by
  obtain ⟨hcmw, hi⟩ := h.cm_get_of (hcm w hw)
  rw [a8_witMap h.enum, h.reps, h.theta_eq]
  unfold witMapOf sqWitData
  rw [List.map_toArray, List.foldl_toArray]
  refine witMap_foldl_get? ?_ ?_ _ _ (Or.inl (mem_sel hsel hw).1)
  · intro g w' e
    split at e
    · split at e
      · cases e
        rfl
      · cases e
    · cases e
  · rw [hcmw]
    dsimp only
    rw [if_pos (by simpa using hi)]

theorem s5 (hcm : Ws.all (cmK T W1 W2 L.length M1 M2) = true) (hT : a8T r1 r2 Ws = true) :
    a8S5Of (a8Data ()) = true := by
  unfold a8T at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨⟨⟨hr1, hr2⟩, hinv⟩, hcnt⟩ := hT
  rw [List.all_eq_true] at hinv hcnt hcm
  have hvals : ∀ (b : Bool × Bool) (F : ℕ → ℕ → Option ℕ),
      (∀ f ∈ evensF, F Code.one f = candOneT f) →
      (∀ w ∈ Ws, ∀ f ∈ evensF, F w.1 f = candT r1 r2 w f b) →
      ((#[Code.one] ++ (a8Data ()).involutions).toList.flatMap fun g =>
        ((List.range 64).filter fun f => (liftTab g f)[a0N]! == a0N).map (F g)) =
        valsT r1 r2 Ws b := by
    intro b F hone hrec
    rw [a8_involutions h.enum, Array.toList_append, List.toList_toArray, List.toList_toArray,
      List.singleton_append, List.flatMap_cons]
    simp only [a0_filter]
    rw [if_pos act_one_one,
      flatMap_filter_eq (p := fun g => Code.act g 1 == 1) (involL L) (fun g _ hg => by
        rw [if_neg (by simpa using hg)]
        rfl), hsel]
    unfold valsT
    rw [List.map_congr_left hone]
    congr 1
    apply flatMap_map_congr
    intro w hw
    rw [if_pos (mem_sel hsel hw).2]
    exact List.map_congr_left (hrec w hw)
  unfold a8S5Of
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨h.invOK, ?_⟩, h.witOK_ok⟩, ?_⟩
  · rw [a8_innTabs h.enum, a8_theta h.enum, h.reps, h.theta_eq]
    exact rootsOK_of h.root1 h.root2
  rw [List.all_eq_true]
  intro b hb
  rw [foldl_push_gens, hvals b _ (fun f _ => ?_) (fun w hw f _ => ?_)]
  · have e := hcnt b hb
    simp only [List.all_toArray]
    simp only [List.size_toArray, List.toList_toArray]
    exact e
  · rw [if_pos (beq_self_eq_true _), a8_innTabs h.enum, candValOne_eq]
  · obtain ⟨hg, _⟩ := mem_sel hsel hw
    have hne : (w.1 == Code.one) = false := by
      rw [beq_eq_false_iff_ne]
      intro e
      have hi := (h.mem_involL.1 hg).2
      rw [e, ← oneF_eq] at hi
      simp [isInvF] at hi
    obtain ⟨_, hi⟩ := h.cm_get_of (hcm w hw)
    obtain ⟨hk, hk'⟩ := invPair_spec (hinv w hw)
    have hr : ∀ u < 64, Code.act (if w.2.1 = 0 then r1 else r2)
        (Code.act (if w.2.1 = 0 then r1 else r2) u) = u := by
      split
      · exact (invPair_spec hr1).1
      · exact (invPair_spec hr2).1
    rw [if_neg (by simp [hne]), h.wit_get hsel hcm hw]
    dsimp only
    rw [if_pos (beq_self_eq_true _), a8_innTabs h.enum, h.root_eq, theta_get hi]
    exact candVal_eqT r1 r2 w f b hk hk' hr (sOf_lt r1 r2 b.1 b.2 hi)

end A8Hyp

end CFSG.KC.C690

end
