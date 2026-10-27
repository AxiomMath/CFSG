module

public import CFSG.Certificates.Kernel.LinRep.Sound
public import CFSG.Sporadic.SuzI301.Inputs

public section

namespace CFSG.KC.SuzI301Lin

open CFSG.PSL3Four.Native CFSG.KS.BfsReplay CFSG.KC.LinRepSound
open CFSG.Sporadic.SuzI301 CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2.Native

theorem comp_get {n : Nat} {p q : Tab} {x : Nat} (hx : x < n) : (comp n p q)[x]! = p[q[x]!]! := by
  unfold comp
  rw [getElem!_pos _ x (by simpa using hx)]
  simp

theorem idTab_get {n x : Nat} (hx : x < n) : (idTab n)[x]! = x := by
  unfold idTab
  rw [getElem!_pos _ x (by simpa using hx)]
  simp

theorem beq_false_of_get {s t : Tab} {x : Nat} (h : s[x]! ≠ t[x]!) : (s == t) = false := by
  cases e : (s == t)
  · rfl
  · rw [beq_iff_eq.1 e] at h
    exact absurd rfl h

theorem anyBelow_true {m k : Nat} {f : Nat → Bool} (hk : k < m) (h : f k = true) :
    anyBelow m f = true := by
  unfold anyBelow
  rw [List.any_eq_true]
  exact ⟨k, List.mem_range.2 hk, h⟩

theorem allBelow_true {m : Nat} {f : Nat → Bool} (h : ∀ k < m, f k = true) :
    allBelow m f = true := by
  unfold allBelow
  rw [List.all_eq_true]
  intro k hk
  exact h k (List.mem_range.1 hk)

theorem mat64_eq (c : Array Nat) :
    mat64 c = linTab (fun i => qIdx c (invCand 1782 c) i / 2) := by
  unfold mat64 linTab
  dsimp only
  congr 1
  funext v
  rw [foldl_eq_ev]
  refine ev_congr (fun i hi => ?_) _
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem matTab_eq (k : Nat) : matTab k = linTab (fun i => (act k i).1) := by
  unfold matTab linTab
  congr 1
  funext v
  exact foldl_eq_ev _ _

theorem act_lt : ∀ k < 10, ∀ i < 6, (act k i).1 < 64 := by decide

@[expose] def genCols (m : Nat → Nat) (j : Nat) : Nat → Nat :=
  if j < 10 then fun i => (act j i).1 else m

theorem gens_size (t : Tab) : (matTabs.push t).size = 11 := by simp [matTabs]

theorem gens_lin {m : Nat → Nat} (hm : ∀ i < 6, m i < 64) :
    ∀ j < (matTabs.push (linTab m)).size,
      (∀ i < 6, genCols m j i < 64) ∧ (matTabs.push (linTab m))[j]! = linTab (genCols m j) := by
  intro j hj
  rw [gens_size] at hj
  have hs : matTabs.size = 10 := by simp [matTabs]
  by_cases h10 : j < 10
  · refine ⟨fun i hi => by simpa [genCols, h10] using act_lt j h10 i hi, ?_⟩
    rw [push_lt (by omega), getElem!_pos _ j (by omega)]
    simp [matTabs, genCols, h10, matTab_eq]
  · have e : j = matTabs.size := by omega
    refine ⟨fun i hi => by simpa [genCols, h10] using hm i hi, ?_⟩
    rw [e, push_eq]
    simp [genCols, hs]

theorem comm64_false {t u : Tab} {x : Nat} (hx : x < 64) (h : t[u[x]!]! ≠ u[t[x]!]!) :
    comm64 t u = false := by
  have e : (comp 64 t u)[x]! ≠ (comp 64 u t)[x]! := by
    rw [comp_get hx, comp_get hx]
    exact h
  unfold comm64
  exact beq_false_of_get e

theorem invTest_of_sq {HL : Array Tab} {t : Tab} {x : Nat} (hx : x < 64) (h : t[t[x]!]! ≠ x) :
    invTest HL t = true := by
  have e : (comp 64 t t == idTab 64) = false :=
    beq_false_of_get (x := x) (by rw [comp_get hx, idTab_get hx]; exact h)
  unfold invTest
  rw [e]
  rfl

theorem invTest_of_id {HL : Array Tab} {t : Tab} (h : t = idTab 64) : invTest HL t = true := by
  subst h
  unfold invTest
  simp

theorem invTest_of_comm {HL : Array Tab} {t : Tab} {k x : Nat} (hk : k < HL.size) (hx : x < 64)
    (h : t[(comp 64 HL[k]! (comp 64 t (comp 64 HL[k]! HL[k]!)))[x]!]! ≠
      (comp 64 HL[k]! (comp 64 t (comp 64 HL[k]! HL[k]!)))[t[x]!]!) :
    invTest HL t = true := by
  have e : anyBelow HL.size (fun k =>
      !(comm64 t (comp 64 HL[k]! (comp 64 t (comp 64 HL[k]! HL[k]!))))) = true := by
    refine anyBelow_true hk ?_
    rw [comm64_false hx h]
    rfl
  unfold invTest
  rw [e]
  simp

theorem invTest_lin_sq {HL : Array Tab} {g : Nat → Nat} (hg : ∀ i < 6, g i < 64) {c : Nat}
    (hc : c < 6) (h : ev g (g c) ≠ 2 ^ c) : invTest HL (linTab g) = true :=
  invTest_of_sq (two_pow_lt hc) (by rw [linTab_get_two_pow g hc, linTab_get g (hg c hc)]; exact h)

theorem invTest_lin_id {HL : Array Tab} {g : Nat → Nat} (h : ∀ i < 6, g i = 2 ^ i) :
    invTest HL (linTab g) = true :=
  invTest_of_id (linTab_eq_id h)

theorem invTest_lin_comm {HL : Array Tab} {g y : Nat → Nat} (hg : ∀ i < 6, g i < 64)
    (hy : ∀ i < 6, y i < 64) {k : Nat} (hk : k < HL.size) (hY : HL[k]! = linTab y) {c : Nat}
    (hc : c < 6)
    (h : ev g (ev y (ev g (ev y (y c)))) ≠ ev (fun i => ev y (ev g (ev y (y i)))) (g c)) :
    invTest HL (linTab g) = true := by
  refine invTest_of_comm hk (two_pow_lt hc) ?_
  rw [hY, comp3_linTab hg hy, linTab_get_two_pow _ hc, linTab_get_two_pow _ hc,
    linTab_get _ (ev_lt hy _), linTab_get _ (hg c hc)]
  exact h

theorem pow12_get {t : Tab} (ht : ∀ y < 64, t[y]! < 64) {x : Nat} (hx : x < 64) :
    (pow12 t)[x]! = (fun y => t[y]!)^[12] x := by
  have h2 : ∀ y < 64, (comp 64 t t)[y]! = (fun y => t[y]!)^[2] y ∧ (comp 64 t t)[y]! < 64 :=
    fun y hy => by
      rw [comp_get hy]
      exact ⟨rfl, ht _ (ht y hy)⟩
  have h4 : ∀ y < 64, (comp 64 (comp 64 t t) (comp 64 t t))[y]! = (fun y => t[y]!)^[4] y ∧
      (comp 64 (comp 64 t t) (comp 64 t t))[y]! < 64 := fun y hy => by
    rw [comp_get hy]
    obtain ⟨a1, a2⟩ := h2 y hy
    obtain ⟨b1, b2⟩ := h2 _ a2
    refine ⟨?_, b2⟩
    rw [b1, a1, ← Function.iterate_add_apply]
  unfold pow12
  dsimp only
  rw [comp_get hx, comp_get hx]
  obtain ⟨a1, a2⟩ := h4 x hx
  obtain ⟨b1, b2⟩ := h4 _ a2
  obtain ⟨c1, -⟩ := h4 _ b2
  rw [c1, b1, a1, ← Function.iterate_add_apply, ← Function.iterate_add_apply]

theorem pow12_size (t : Tab) : (pow12 t).size = 64 := by
  unfold pow12 comp
  exact Array.size_ofFn

theorem idTab_size64 : (idTab 64).size = 64 := by
  unfold idTab
  exact Array.size_ofFn

theorem ext64 {a b : Tab} (ha : a.size = 64) (hb : b.size = 64) (h : ∀ x < 64, a[x]! = b[x]!) :
    a = b := by
  refine Array.ext (by rw [ha, hb]) fun x h1 h2 => ?_
  rw [← getElem!_pos a x h1, ← getElem!_pos b x h2]
  exact h x (by omega)

theorem pow12_eq_id {t : Tab} (ht : ∀ y < 64, t[y]! < 64)
    (h : ∀ x < 64, (fun y => t[y]!)^[12] x = x) : pow12 t = idTab 64 :=
  ext64 (pow12_size t) idTab_size64 fun x hx => by rw [pow12_get ht hx, h x hx, idTab_get hx]

theorem centPow12 {A : Array Tab} {md : Tab}
    (h : ∀ k < A.size, (∃ x < 64, (A[k]!)[md[x]!]! ≠ md[(A[k]!)[x]!]!) ∨
      ((∀ y < 64, (A[k]!)[y]! < 64) ∧ ∀ x < 64, (fun y => (A[k]!)[y]!)^[12] x = x)) :
    allBelow A.size (fun k => !(comm64 A[k]! md) || pow12 A[k]! == idTab 64) = true := by
  refine allBelow_true fun k hk => ?_
  rcases h k hk with ⟨x, hx, hne⟩ | ⟨hlt, hfix⟩
  · rw [comm64_false hx hne]
    rfl
  · rw [pow12_eq_id hlt hfix]
    simp

end CFSG.KC.SuzI301Lin

end
