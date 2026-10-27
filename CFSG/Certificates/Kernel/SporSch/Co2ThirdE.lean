
module

public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.SporSch.Co2LESound
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public import Certificates.Data.CFSGNative.YGroups.ExactCheck

public section

namespace CFSG.KS.Co2ThirdE

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatRep CFSG.KS.Co2LE CFSG.KS.Raw
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Schreier

theorem foldl_strong (n : ℕ) : ∀ (ds : List (List ℤ)) (A : Array (Array ℕ)),
    (ds.foldl (fun p w => (p.1.push (wordA n p.1 p.2 w), p.2.push (invCand n (wordA n p.1 p.2 w))))
      (A, A.map (invCand n))).1 = extendArrsN n A ds
  | [], A => rfl
  | w :: ds, A => by
    have h := foldl_strong n ds (A.push (wordA n A (A.map (invCand n)) w))
    rw [Array.map_push] at h
    exact h

theorem extendArrsN_eq (n : ℕ) (A : Array (Array ℕ)) (ds : List (List ℤ)) :
    extendArrsN n A ds = (CFSG.YGroups.ModelNative.strongOf n A ds.toArray).1 := by
  rw [← foldl_strong n ds A]
  unfold CFSG.YGroups.ModelNative.strongOf
  simp only [List.foldl_toArray]

theorem extendArrs_eq (A : Array (Array ℕ)) (ds : List (List ℤ)) :
    extendArrs A ds = (CFSG.YGroups.ModelNative.strongOf 2300 A ds.toArray).1 := by
  rw [← extendArrsN_eq]
  rfl

theorem extendArrsN_size (n : ℕ) : ∀ (ds : List (List ℤ)) (A : Array (Array ℕ)),
    (extendArrsN n A ds).size = A.size + ds.length
  | [], _ => rfl
  | w :: ds, A => by
    have h := extendArrsN_size n ds (A.push (wordArrN n A w))
    rw [Array.size_push] at h
    change (extendArrsN n (A.push (wordArrN n A w)) ds).size = _
    rw [h, List.length_cons]
    omega

theorem extendArrsN_get_lt (n : ℕ) : ∀ (ds : List (List ℤ)) (A : Array (Array ℕ)) {i : ℕ},
    i < A.size → (extendArrsN n A ds)[i]! = A[i]!
  | [], _, _, _ => rfl
  | w :: ds, A, i, hi => by
    change (extendArrsN n (A.push (wordArrN n A w)) ds)[i]! = A[i]!
    rw [extendArrsN_get_lt n ds _ (by rw [Array.size_push]; omega),
      getElem!_pos _ i (by rw [Array.size_push]; omega), getElem!_pos A i hi,
      Array.getElem_push_lt]

theorem extendArrsN_take (n : ℕ) (A : Array (Array ℕ)) (ds : List (List ℤ)) :
    (extendArrsN n A ds).toList.take A.size = A.toList := by
  apply List.ext_getElem
  · simp [extendArrsN_size]
  · intro i h1 h2
    have hi : i < A.size := by simpa using h2
    rw [List.getElem_take, Array.getElem_toList, Array.getElem_toList,
      ← getElem!_pos _ i (by rw [extendArrsN_size]; omega), ← getElem!_pos A i hi,
      extendArrsN_get_lt n ds A hi]

theorem isPermList_unpack {n w P Q : ℕ} (h : permOK n w (mask w) (n * w) P Q = true) :
    CFSG.Sporadic.Co2Cert.isPermList n (unpack n w P).toList = true := by
  have hr := (CFSG.Monster.B.Co2.rep_permOfArr (Orb.isInvA_unpack h)).1
  unfold CFSG.Sporadic.Co2Cert.isPermList
  rw [Array.toArray_toList, Array.length_toList,
    CFSG.KS.Raw.isInvA_of_rep hr (CFSG.KS.Raw.rep_invCand hr)]
  simp [unpack]

theorem all_isPermList {n : ℕ} {X : Array (Array ℕ)}
    (h : ∀ j < X.size, CFSG.Sporadic.Co2Cert.isPermList n X[j]!.toList = true) :
    (X.toList.map Array.toList).all (CFSG.Sporadic.Co2Cert.isPermList n) = true := by
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hl
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  rw [Array.length_toList] at hj
  rw [Array.getElem_toList, ← getElem!_pos X j hj]
  exact h j hj

variable {V : Array ℕ} {PV : ℕ} {R GM : ℕ → ℕ} {ng N : ℕ} {gens : Array (Array ℕ)}

theorem conjPis_get (hV : VOK V PV) (hR : Recs R GM PV ng N) (hg : GensRep V gens GM ng)
    {cap : ℕ} (hcap : N ≤ cap) {conj : Array (Array ℕ)} {nc w : ℕ} {C C' PI : ℕ → ℕ}
    (hc : conj.size = nc) (hcr : ∀ i < nc, Rep 22 V conj[i]! (C i) (C' i))
    (hk : ∀ i < nc, ∀ k < N, conjK R (C i) (C' i) (PI i) w N k = true) :
    ∀ i < nc, (conjPis conj N (leftEnum gens cap))[i]! = unpack N w (PI i) := by
  obtain ⟨he, hok, hrepL⟩ := leftEnum_facts hV hR hg hcap
  have hpos : ∀ j < N, (leftEnum gens cap).pos.getD (keyA (LL V R N)[j]!) 0 = j := by
    intro j hj
    unfold enumOK at hok
    simp only [Bool.and_eq_true] at hok
    have h := CFSG.Monster.B.Co2.allLt_iff.1 hok.2 j hj
    rw [he] at h
    exact beq_iff_eq.1 h
  intro i hi
  unfold conjPis unpack
  rw [getElem!_pos _ i (by rw [Array.size_map, hc]; exact hi), Array.getElem_map,
    ← getElem!_pos conj i (by rw [hc]; exact hi), he]
  refine congrArg (Array.ofFn (n := N)) (funext fun k => ?_)
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (hk i hi k.val k.isLt)
  have hp := blt_lt' h1
  obtain ⟨Mk, hMk⟩ := hrepL k.val k.isLt
  have r1 := rep_compA hV.good (hcr i hi) hMk
  have r2 := rep_invCand hV.good (hcr i hi)
  have r3 := rep_compA hV.good r1 r2
  rw [hV.size] at r1 r2 r3
  have e : compA 2300 (compA 2300 conj[i]! (LL V R N)[k.val]!) (invCand 2300 conj[i]!) =
      (LL V R N)[pg w (mask w) (PI i) k.val]! := by
    rw [r3.1, LL_get R hp, Nat.eq_of_beq_eq_true h2, mmK_eq, mmK_eq]
  rw [e]
  exact hpos _ hp

end CFSG.KS.Co2ThirdE

end
