module

public import Certificates.Data.Kernel.Spor.Co2Shape
public import CFSG.Sporadic.Co2Cert.CheckInputs
import CFSG.Certificates.Kernel.Spor.Co2ChainSound
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.Co2Shape

open CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2.Native

@[expose] def shapeOKOf (r : Co2CertFile) : Bool :=
  r.schemaVersion == 1 && r.group == "Co2" && r.prime == 2 && r.dimension == 22 &&
    r.vectors.length == 2300 && r.vectors.all (fun v => v.length == 22 && v.all (· < 2)) &&
    r.basisIndices == co2BasisList &&
    chainShapeOK r.chain 2300 2 11 [0, 1, 2, 3, 5, 4] &&
    chainShapeOK r.coprimeChain 2300 2 17 [0, 1, 3, 2, 5, 4] &&
    r.coprimeConjugator == [-1, 2, 2, 1, 2, -1] && r.point == 0 &&
    r.stabilizerGeneratorIndices == [0, 2, 3, 4, 5, 6, 7, 8, 9, 10] &&
    r.stabilizerOrbits.map List.length == [1, 1408, 891] &&
    r.stabilizerOrbits.all (increasingBelow 2300) &&
    r.merges.map (·.representative) == [1, 3] &&
    r.merges.map (·.instructions.length) == [2298, 2298] &&
    r.merges.all (fun m => m.instructions.all tripleOK)

theorem co2ShapeOK_eq : co2ShapeOK = shapeOKOf co2Rec := rfl

private theorem icode_inj' {x y : Int} (h : CFSG.KS.Mathieu.icode x = CFSG.KS.Mathieu.icode y) :
    x = y := by
  cases x <;> cases y <;> simp only [CFSG.KS.Mathieu.icode, Nat.add_eq, Nat.succ_eq_add_one] at h <;>
    first | omega | (congr 1; omega)

private theorem eqIL_iff : ∀ a b : List Int, eqIL a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: xs, y :: ys, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (eqIL xs ys)
        (Nat.beq (CFSG.KS.Mathieu.icode x) (CFSG.KS.Mathieu.icode y)) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rw [icode_inj' (Nat.eq_of_beq_eq_true h1), eqIL_iff xs ys h2]

private theorem incL_spec (n : Nat) : ∀ (l : List Nat) (p : Nat), incL n l p = true →
    (∀ x ∈ l, x < n) ∧ (∀ x ∈ l.head?, p ≤ x) ∧ l.Pairwise (· < ·)
  | [], _, _ => by simp
  | x :: l, p, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (incL n l (Nat.succ x)) (Nat.ble p x)) (Nat.blt x n) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨ihb, ihh, ihp⟩ := incL_spec n l (Nat.succ x) h3
    have h1 : x < n := Nat.le_of_ble_eq_true h1
    have h2 : p ≤ x := Nat.le_of_ble_eq_true h2
    refine ⟨fun y hy => ?_, by simpa using h2, List.pairwise_cons.2 ⟨fun y hy => ?_, ihp⟩⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      exacts [h1, ihb y hy]
    ·
      have key : ∀ (l : List Nat) (q : Nat), (∀ z ∈ l.head?, q ≤ z) → l.Pairwise (· < ·) →
          ∀ z ∈ l, q ≤ z := by
        intro l q hq hp z hz
        cases l with
        | nil => simp at hz
        | cons a l =>
          have ha : q ≤ a := hq a rfl
          rcases List.mem_cons.1 hz with rfl | hz
          · exact ha
          · exact Nat.le_of_lt (Nat.lt_of_le_of_lt ha (List.rel_of_pairwise_cons hp hz))
      exact key l (Nat.succ x) ihh ihp y hy

private theorem increasingBelow_of {n : Nat} {l : List Nat} (h : incL n l 0 = true) :
    increasingBelow n l = true := by
  obtain ⟨hb, -, hp⟩ := incL_spec n l 0 h
  unfold increasingBelow
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range]
  refine ⟨hb, fun k hk => ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by omega), Option.getD_some, Option.getD_some]
  exact List.pairwise_iff_getElem.1 hp k (k + 1) (by omega) (by omega) (by omega)

private theorem tripleOK_of : ∀ {t : List Nat}, tripleK t = true → tripleOK t = true
  | [], h => absurd h Bool.false_ne_true
  | [_], h => absurd h Bool.false_ne_true
  | [_, _], h => absurd h Bool.false_ne_true
  | _ :: _ :: _ :: _ :: _, h => absurd h Bool.false_ne_true
  | [i, u, v], h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (Nat.blt v 2300) (Nat.blt u 2300))
        (Nat.blt i 2)) true = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    have h2 := (bAnd_iff _ _).1 h2
    have h1 : i < 2 := Nat.le_of_ble_eq_true h1
    have h2' : u < 2300 := Nat.le_of_ble_eq_true h2.1
    have h3 : v < 2300 := Nat.le_of_ble_eq_true h2.2
    unfold tripleOK
    simp only [List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ,
      decide_eq_true h1, decide_eq_true h2', decide_eq_true h3]
    rfl

theorem co2ShapeK_sound {r : Co2CertFile} (hg : r.group = "Co2") (h : co2ShapeK r = true) :
    shapeOKOf r = true := by
  unfold co2ShapeK at h
  simp only [bAnd_iff, Nat.beq_eq, CFSG.KS.Co2SShape.lenL_eq, CFSG.KS.Co2SShape.allL_eq,
    CFSG.KS.Co2SShape.eqNL_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have e14 : ∀ l : List Co2Merge,
      List.rec (motive := fun _ => List Nat) [] (fun m _ ih => List.cons m.representative ih) l =
        l.map (·.representative) := fun l => by induction l <;> simp_all
  have e15 : ∀ l : List Co2Merge, List.rec (motive := fun _ => List Nat) []
      (fun m _ ih => List.cons m.instructions.length ih) l = l.map (·.instructions.length) :=
    fun l => by induction l <;> simp_all
  have e12 : ∀ l : List (List Nat), List.rec (motive := fun _ => List Nat) []
      (fun o _ ih => List.cons o.length ih) l = l.map List.length :=
    fun l => by induction l <;> simp_all
  rw [e14] at h14
  rw [e15] at h15
  rw [e12] at h12
  unfold shapeOKOf
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, and_assoc] at *
  simp only [bAnd_iff, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at h5
  exact ⟨h1, hg, h2, h3, h4, h5, h6, CFSG.KS.Co2SShape.chainK_sound h7,
    CFSG.KS.Co2SShape.chainK_sound h8, eqIL_iff _ _ h9, h10, h11, h12,
    fun o ho => increasingBelow_of (h13 o ho), h14, h15,
    fun m hm t ht => tripleOK_of (h16 m hm t ht)⟩

end CFSG.KS.Co2Shape

end
