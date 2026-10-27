module

public import Certificates.Data.Kernel.Cert690.CBase
public import CFSG.Certificates.Kernel.Cert690.HashSound
public import CFSG.Certificates.Kernel.Cert690.MulSound

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

structure GRel (D : GrpData) (G : GK) : Prop where
  size : D.O.size = G.n
  get : ∀ i, D.O[i]! = G.getO i
  idx : ∀ c, D.idx.getD c G.n = G.ix c
  inv : ∀ i, D.invI[i]! = G.getInv i

theorem act_land (m v : ℕ) : Code.act m (v &&& 63) = Code.act m v := by
  unfold Code.act Code.sel
  have h : ∀ j, j < 6 → (v &&& 63).testBit j = v.testBit j := fun j hj => by
    rw [Nat.testBit_and, show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [hj]
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num), h 5 (by norm_num)]

theorem act_eq_actF (m v : ℕ) : Code.act m v = actF m v := by
  show Code.act m v = mulF m (v &&& 63)
  rw [mulF_vec m (Nat.and_lt_two_pow (n := 6) _ (by norm_num)), act_land]

theorem mul_eq_mulF (a b : ℕ) : Code.mul a b = mulF a b := (mulF_eq a b).symm

theorem one_eq_oneF : Code.one = oneF := oneF_eq.symm

theorem card_hashSet (A : Array ℕ) : (hashSetOfArray A).size = A.toList.dedup.length := by
  rw [hashSetOfArray_size, List.card_toFinset]

theorem contains_hashSet (A : Array ℕ) (x : ℕ) :
    (hashSetOfArray A).contains x = A.toList.contains x := hashSetOfArray_contains A x

section

variable {D : GrpData} {G : GK} (R : GRel D G)
include R

theorem isA2Of_eq (minus : Bool) (i : ℕ) : isA2Of D minus i = isA2K G minus i := by
  unfold isA2Of isA2K
  simp only [R.size, R.get, act_eq_actF, mul_eq_mulF, one_eq_oneF, card_hashSet,
    ← Array.all_toList, List.toList_toArray]

theorem a2FixOf_eq (minus : Bool) (b : ℕ) : a2FixOf D minus b = (a2FixK G minus b).toArray := by
  unfold a2FixOf a2FixK
  simp only [R.size, R.get, act_eq_actF, isA2Of_eq R]

theorem transWitOf_eq (s : List ℕ) (b : ℕ) :
    transWitOf D s.toArray b = (transWitK G s b).toArray := by
  unfold transWitOf transWitK
  simp only [R.size, R.get, act_eq_actF, List.map_toArray]

theorem transOK_eq (s : List ℕ) (b : ℕ) (w : List ℕ) :
    transOK D s.toArray b w.toArray = transK G s b w := by
  unfold transOK transK
  simp only [R.size, R.get, act_eq_actF, List.size_toArray, List.getElem!_toArray]

theorem conjIdxOf_eq (a x : ℕ) : conjIdxOf D a x = conjK G a x := by
  unfold conjIdxOf conjK
  simp only [R.size, R.get, R.inv, R.idx, mul_eq_mulF]

theorem lOK_eq (minus : Bool) (b : ℕ) (L : Array ℕ) : lOK D minus b L = lOKK G minus b L := by
  unfold lOK lOKK
  simp only [R.size, R.get, R.idx, act_eq_actF, mul_eq_mulF, one_eq_oneF, card_hashSet,
    ← Array.all_toList, ← Array.any_toList, ← Array.contains_toList, isA2Of_eq R]

theorem l2OK_eq (minus : Bool) (b : ℕ) (Llist : Array (Array ℕ)) (a2 : List ℕ)
    (wit : Array (ℕ × ℕ)) : l2OK D minus b Llist a2.toArray wit = l2OKK G b Llist a2 wit := by
  unfold l2OK l2OKK
  simp only [R.size, R.get, R.idx, R.inv, act_eq_actF, mul_eq_mulF, List.size_toArray,
    List.getElem!_toArray, ← Array.all_toList, ← Array.any_toList, ← Array.contains_toList]

theorem l3OK_eq (b : ℕ) (Llist : Array (Array ℕ)) (tasks wit : Array (ℕ × ℕ)) :
    l3OK D b Llist tasks wit = l3OKK G b Llist tasks wit := by
  unfold l3OK l3OKK isInvCode
  simp only [card_hashSet, ← Array.all_toList, ← Array.any_toList, ← Array.contains_toList]
  simp only [R.size, R.get, R.idx, R.inv, act_eq_actF, mul_eq_mulF, one_eq_oneF,
    conjIdxOf_eq R, Array.toList_append, Array.toList_map, Array.size_append, Array.size_map,
    List.length_append, List.length_map, Array.length_toList]

theorem l3TaskValid_eq (b : ℕ) (Llist : Array (Array ℕ)) (j u : ℕ) :
    l3TaskValid D b Llist j u = l3ValidK G b Llist j u := by
  unfold l3TaskValid l3ValidK isInvCode
  simp only [R.size, R.get, act_eq_actF, mul_eq_mulF, one_eq_oneF, ← Array.all_toList,
    ← Array.contains_toList]

theorem l3Complete_eq (b : ℕ) (Llist : Array (Array ℕ)) (tasks : Array (ℕ × ℕ)) :
    l3Complete D b Llist tasks = l3CompleteK G b Llist tasks := by
  unfold l3Complete l3CompleteK
  simp only [R.size, l3TaskValid_eq R, ← Array.contains_toList]

theorem censusBaseOf_eq (minus : Bool) (Ld : LData) :
    censusBaseOf minus D Ld = (groupOK minus D &&
      (transK G (singL minus) (b0Of minus) (transWitK G (singL minus) (b0Of minus)) &&
        censusLsK G minus Ld)) := by
  have hs : singOf minus = (singL minus).toArray := rfl
  unfold censusBaseOf censusLsK
  simp only [hs, transWitOf_eq R, transOK_eq R, a2FixOf_eq R, lOK_eq R, l2OK_eq R,
    l3Complete_eq R, l3OK_eq R, ← Array.all_toList]

end

end CFSG.KC.C690

end
