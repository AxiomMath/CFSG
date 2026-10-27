module

public import Certificates.Data.Kernel.SporSch.J4SPairK
public import CFSG.Certificates.Kernel.SporSch.J4SRunSound

public section

namespace CFSG.KS.SporSch.J4B

open CFSG.KC.J4Q CFSG.KC.Loop CFSG.Sporadic.J4Schreier

@[expose] def PairOK (P : Pair) (a b : Nat) : Prop :=
  (WfN P.1 ∧ encN P.1 = a) ∧ (WfN P.2 ∧ encN P.2 = b)

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
variable (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
include hK

theorem mulP_ok {P Q : Pair} {a b a' b' : Nat} (hP : PairOK P a b) (hQ : PairOK Q a' b') :
    PairOK (mulP P Q) (mulJ c rm a a') (mulJ c rm b' b) := by
  have m1 := mul_enc hK hP.1.1 hQ.1.1
  have m2 := mul_enc hK hQ.2.1 hP.2.1
  exact ⟨⟨m1.1, m1.2.trans (by rw [hP.1.2, hQ.1.2])⟩, ⟨m2.1, m2.2.trans (by rw [hP.2.2, hQ.2.2])⟩⟩

omit hK in
theorem invP_ok {P : Pair} {a b : Nat} (hP : PairOK P a b) : PairOK (invP P) b a :=
  ⟨hP.2, hP.1⟩

theorem powP_ok {P : Pair} {a b : Nat} (hP : PairOK P a b) (e : Nat) :
    PairOK (powP P e) (powJ c rm one a e) (powJ c rm one b e) := by
  have m1 := pow_enc hK hP.1.1 e
  have m2 := pow_enc hK hP.2.1 e
  exact ⟨⟨m1.1, m1.2.trans (by rw [hP.1.2])⟩, ⟨m2.1, m2.2.trans (by rw [hP.2.2])⟩⟩

theorem oneP_ok : PairOK oneP one one := ⟨id_enc hK, id_enc hK⟩

omit hK in
theorem letterP_ok {X Y : Pair} {x1 x2 y1 y2 : Nat} (hX : PairOK X x1 x2)
    (hY : PairOK Y y1 y2) {l : Int} (hl : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) :
    PairOK (letterP X Y l) (letA one x1 x2 y1 y2 l) (letB one x1 x2 y1 y2 l) := by
  rcases hl with rfl | rfl | rfl | rfl
  · exact hX
  · exact invP_ok hX
  · exact hY
  · exact invP_ok hY

theorem wordP_ok {X Y : Pair} {x1 x2 y1 y2 : Nat} (hX : PairOK X x1 x2)
    (hY : PairOK Y y1 y2) {s : List Int} {a b : Nat} (hs : PairOK (wordP X Y s) a b) :
    ∀ w : List Int, (∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) →
      PairOK (wordP X Y (w ++ s)) (wFK c rm one x1 x2 y1 y2 w a) (wSK c rm one x1 x2 y1 y2 w b)
  | [], _ => hs
  | l :: w, hw => by
    have ih := wordP_ok hX hY hs w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have e : wordP X Y ((l :: w) ++ s) = mulP (letterP X Y l) (wordP X Y (w ++ s)) := rfl
    have e1 : wFK c rm one x1 x2 y1 y2 (l :: w) a =
        mulJ c rm (letA one x1 x2 y1 y2 l) (wFK c rm one x1 x2 y1 y2 w a) := strictN_eq' _ _
    have e2 : wSK c rm one x1 x2 y1 y2 (l :: w) b =
        mulJ c rm (wSK c rm one x1 x2 y1 y2 w b) (letB one x1 x2 y1 y2 l) := strictN_eq' _ _
    rw [e, e1, e2]
    exact mulP_ok hK (letterP_ok hX hY (hw l List.mem_cons_self)) ih

theorem wordP_ok' {X Y : Pair} {x1 x2 y1 y2 : Nat} (hX : PairOK X x1 x2)
    (hY : PairOK Y y1 y2) (w : List Int) (hw : ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) :
    PairOK (wordP X Y w) (wFK c rm one x1 x2 y1 y2 w one) (wSK c rm one x1 x2 y1 y2 w one) := by
  have := wordP_ok hK hX hY (s := []) (oneP_ok hK) w hw
  rwa [List.append_nil] at this

theorem prodP_ok : ∀ (L : List Pair) (fs ss : List Nat), L.length = fs.length →
    L.length = ss.length → (∀ i < L.length, PairOK L[i]! fs[i]! ss[i]!) →
    PairOK (prodP L) (prodFK c rm one fs) (prodSK c rm one ss)
  | [], [], [], _, _, _ => oneP_ok hK
  | P :: L, a :: fs, b :: ss, h1, h2, h => by
    have ih := prodP_ok L fs ss (by simpa using h1) (by simpa using h2) fun i hi => by
      simpa using h (i + 1) (by simpa using hi)
    have hP : PairOK P a b := by simpa using h 0 (by simp)
    have e1 : prodFK c rm one (a :: fs) = mulJ c rm a (prodFK c rm one fs) := strictN_eq' _ _
    have e2 : prodSK c rm one (b :: ss) = mulJ c rm (prodSK c rm one ss) b := strictN_eq' _ _
    have e : prodP (P :: L) = mulP P (prodP L) := rfl
    rw [e1, e2, e]
    exact mulP_ok hK hP ih

end CFSG.KS.SporSch.J4B

end
