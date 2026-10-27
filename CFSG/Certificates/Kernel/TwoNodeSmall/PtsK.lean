module

public import Certificates.Data.Kernel.TwoNodeSmall.PtsK

public section

namespace CFSG.TwoNodeSmall.PtsK

open CFSG.TwoNodeSmall

theorem foldl_zip_comm : ∀ (a b : Vec) (acc : Nat),
    ((a.zip b).map fun xy => xy.1 * xy.2).foldl (· + ·) acc =
      ((b.zip a).map fun xy => xy.1 * xy.2).foldl (· + ·) acc
  | [], b, acc => by cases b <;> simp
  | x :: a, [], acc => by simp
  | x :: a, y :: b, acc => by
    simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons]
    rw [Nat.mul_comm x y]
    exact foldl_zip_comm a b _

theorem dotv_comm (a b : Vec) : dotv a b = dotv b a := by
  unfold dotv
  rw [foldl_zip_comm]

theorem dotv_cons_free (c : Vec) (a : Nat) (v : Vec) (h : (c.headD 0 == 0) = true) :
    dotv c (a :: v) = dotv c.tail v := by
  cases c with
  | nil => simp [dotv]
  | cons x c =>
    simp only [List.headD_cons, beq_iff_eq] at h
    subst h
    simp [dotv]

theorem Con.holds_cons (q : Con) (a : Nat) (v : Vec) (h : q.free = true) :
    q.holds (a :: v) = q.shift.holds v := by
  cases q with
  | dot c ok =>
    simp only [Con.free] at h
    exact congrArg ok (dotv_cons_free c a v h)
  | coord k ok =>
    cases k with
    | zero => simp [Con.free] at h
    | succ k => simp [Con.holds, Con.shift]

theorem sat_cons (cs : List Con) (a : Nat) (v : Vec) :
    sat cs (a :: v) =
      (sat ((cs.filter Con.free).map Con.shift) v && sat (cs.filter fun q => !q.free) (a :: v)) := by
  induction cs with
  | nil => simp [sat]
  | cons q cs ih =>
    unfold sat at ih ⊢
    cases hq : q.free with
    | true => simp [List.filter_cons, hq, Con.holds_cons q a v hq, ih, Bool.and_assoc]
    | false =>
      simp only [List.all_cons, List.filter_cons, hq, Bool.not_false, if_true, Bool.false_eq_true,
        if_false, ih]
      cases q.holds (a :: v) <;> simp

theorem filter_map_cons (l : List Nat) (cs : List Con) (v : Vec) :
    (l.map (· :: v)).filter (sat cs) =
      if sat ((cs.filter Con.free).map Con.shift) v then
        (l.map (· :: v)).filter (sat (cs.filter fun q => !q.free))
      else [] := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.filter_cons, List.filter_cons, ih, sat_cons]
    cases sat ((cs.filter Con.free).map Con.shift) v <;> simp

theorem flatMap_ite {α β : Type} (l : List α) (p : α → Bool) (F : α → List β) :
    (l.flatMap fun v => if p v then F v else []) = (l.filter p).flatMap F := by
  induction l with
  | nil => simp
  | cons a l ih => cases h : p a <;> simp [List.filter_cons, h, ih]

theorem filter_allVecs : ∀ (n : Nat) (cs : List Con), (allVecs n).filter (sat cs) = enumP n cs
  | 0, cs => by
    simp only [allVecs, enumP, List.filter_cons, List.filter_nil]
  | n + 1, cs => by
    rw [allVecs, List.filter_flatMap]
    simp only [filter_map_cons [0, 1, 2] cs]
    rw [flatMap_ite, filter_allVecs n, enumP]

theorem sat_consH (e : Nat) (o : Nat × Nat × Nat) :
    sat (consH e o) = fun ha =>
      (embJ e).zipIdx.all fun jj => dotv (alpha8 jj.1) ha == if jj.2 = o.1 then o.2.1 else 0 := by
  funext ha
  simp [sat, consH, Con.holds, List.all_map, Function.comp_def]

theorem sat_consA8 (e : Nat) (o : Nat × Nat × Nat) :
    sat (consA8 e o) = fun fa => fa.getD 7 0 != 0 &&
      (embJ e).zipIdx.all fun jj => dotv fa (hvec8 jj.1) == if jj.2 = o.1 then o.2.2 else 0 := by
  funext fa
  simp [sat, consA8, Con.holds, List.all_map, Function.comp_def, dotv_comm fa]

theorem sat_consA9 (e : Nat) (o : Nat × Nat × Nat) :
    sat (consA9 e o) = fun fa => fa.getD 7 0 != 0 && fa.getD 8 0 == 2 &&
      (embJ e).zipIdx.all fun jj => dotv fa (hvec8 jj.1 ++ [0]) == if jj.2 = o.1 then o.2.2 else 0 := by
  funext fa
  simp [sat, consA9, Con.holds, List.all_map, Function.comp_def, dotv_comm fa, Bool.and_assoc]

theorem addPairs8_eq (e : Nat) (o : Nat × Nat × Nat) : addPairs8 e o = addPairs8K e o := by
  simp only [addPairs8, addPairs8K, ← filter_allVecs, sat_consH, sat_consA8]

theorem pts8_eq : pts8 () = pts8K () := by
  simp only [pts8, pts8K, addPairs8_eq]

theorem pts9m_eq : pts9m () = pts9mK () := by
  simp only [pts9m, pts9mK, addPairs8_eq]

theorem pts9_eq : pts9 () = pts9K () := by
  simp only [pts9, pts9K, ← filter_allVecs, sat_consA9]
  rfl

end CFSG.TwoNodeSmall.PtsK

end
