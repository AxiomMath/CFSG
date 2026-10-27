module

public import Certificates.Data.Kernel.CosetJ.Model
public import Certificates.Data.HePresCheck
public import CFSG.Certificates.Kernel.Misc.Coset.PG
import CFSG.Certificates.Kernel.Spor.CBfsKSound

public section

namespace CFSG.KC.CosetJ.ModelKS

open CFSG.KC.CosetJ.Model CFSG.ComponentClassification.AS81.HePres.Native CFSG.KC.MiscCoset
  CFSG.Monster.B.Co2.Native

private theorem andB_iffM (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

private theorem allN_specM {n : Nat} {p : Nat → Bool} (h : allN n p = true) :
    ∀ i < n, p i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    change andB (p n) (allN n p) = true at h
    rw [andB_iffM] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h.2 i hi
    · exact h.1

private theorem allLt_iffM {n : Nat} {p : Nat → Bool} :
    allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i i.2

private theorem getL_eqM : ∀ (L : List Nat) (i : Nat), getL L i = L.getD i 0
  | [], _ => rfl
  | h :: _, 0 => by
    change h = _
    simp
  | _ :: L, i + 1 => by
    change getL L i = _
    rw [getL_eqM L i]
    simp

private theorem getLL_eqM : ∀ (L : List (List Nat)) (i : Nat), getLL L i = L.getD i []
  | [], _ => rfl
  | h :: _, 0 => by
    change h = _
    simp
  | _ :: L, i + 1 => by
    change getLL L i = _
    rw [getLL_eqM L i]
    simp

private theorem getD_toListM (a : Array Nat) (i : Nat) : a.toList.getD i 0 = a[i]! := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [getElem!_neg a i h, List.getD_eq_default _ _ (by simpa using h)]
    rfl

private theorem getD_mapM (gens : Array (Array Nat)) (g : Nat) :
    (gens.toList.map Array.toList).getD g [] = (gens.getD g #[]).toList := by
  by_cases h : g < gens.size
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [Array.getD, h]
  · rw [List.getD_eq_default _ _ (by simpa using h)]
    simp [Array.getD, h]

private theorem empty_getM (y : Nat) : (#[] : Array Nat)[y]! = 0 := by
  rw [getElem!_neg _ _ (by simp)]
  rfl

private theorem invCand_getM {n : Nat} {t : Array Nat} {U : Nat → Nat}
    (ht : ∀ i < n, t[i]! < n ∧ U t[i]! = i) {y : Nat} (hy : y < n) :
    (invCand n t)[y]! = U y ∧ U y < n := by
  have hd : ∀ i < n, ∀ j < i, t[j]! ≠ t[i]! := fun i hi j hj e => by
    have := congrArg U e
    rw [(ht j (by omega)).2, (ht i hi).2] at this
    omega
  have heq : invCand n t =
      (List.range' 0 n).foldl (fun p i => p.set! t[i]! i) (Array.replicate n 0) := by
    unfold invCand
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  let f : Fin n → Fin n := fun x => ⟨t[x.val]!, (ht x.val x.isLt).1⟩
  have hinj : Function.Injective f := fun a b e => by
    have e' : t[a.val]! = t[b.val]! := congrArg Fin.val e
    have := congrArg U e'
    rw [(ht a.val a.isLt).2, (ht b.val b.isLt).2] at this
    exact Fin.ext this
  obtain ⟨x, hx⟩ := (Finite.surjective_of_injective hinj) ⟨y, hy⟩
  have hTx : t[x.val]! = y := congrArg Fin.val hx
  have hxy : U y = x.val := by rw [← hTx, (ht x.val x.isLt).2]
  refine ⟨?_, by rw [hxy]; exact x.isLt⟩
  rw [heq, ← hTx, (CFSG.KS.CB.set_loop (fun i hi => (ht i hi).1) hd).2 x.val x.isLt, hTx, hxy]

theorem modelCheck_of_modelK {k n : ℕ} {gens : Array (Array ℕ)}
    {rels : List (List (Fin k × Bool))} {I : List (List ℕ)}
    (h : modelK n k (gens.toList.map Array.toList) I (rels.map encW) = true) :
    modelCheck n gens rels = true := by
  unfold modelK at h
  rw [andB_iffM] at h
  obtain ⟨h1, h2⟩ := h
  have hG : ∀ g x, getL (getLL (gens.toList.map Array.toList) g) x = (gens.getD g #[])[x]! := by
    intro g x
    rw [getLL_eqM, getD_mapM, getL_eqM, getD_toListM]
  have hP : ∀ g < k, ∀ i < n, (gens.getD g #[])[i]! < n ∧
      (I.getD g []).getD ((gens.getD g #[])[i]!) 0 = i := by
    intro g hg i hi
    have := allN_specM (allN_specM h1 g hg) i hi
    rw [andB_iffM, hG, getLL_eqM, getL_eqM] at this
    exact ⟨Nat.blt_eq.mp this.1, Nat.eq_of_beq_eq_true this.2⟩
  have hI : ∀ g < k, ∀ y < n, ((gens.map (invCand n)).getD g #[])[y]! = (I.getD g []).getD y 0 ∧
      (I.getD g []).getD y 0 < n := by
    intro g hg y hy
    by_cases hgs : g < gens.size
    · have e : (gens.map (invCand n)).getD g #[] = invCand n (gens.getD g #[]) := by
        simp [Array.getD, hgs]
      rw [e]
      exact invCand_getM (U := fun x => (I.getD g []).getD x 0) (hP g hg) hy
    · have e1 : (gens.map (invCand n)).getD g #[] = #[] := by simp [Array.getD, hgs]
      have e2 : gens.getD g #[] = #[] := by simp [Array.getD, hgs]
      have hy' := hP g hg y hy
      have h0 := hP g hg 0 (by omega)
      rw [e2, empty_getM] at hy' h0
      have hy0 : y = 0 := hy'.2.symm.trans h0.2
      subst hy0
      rw [e1, empty_getM, h0.2]
      exact ⟨rfl, hy⟩
  have hW : ∀ w : List (Fin k × Bool), ∀ x < n,
      (wordArrW n gens (gens.map (invCand n)) w)[x]! =
          walk (gens.toList.map Array.toList) I (encW w) x ∧
        walk (gens.toList.map Array.toList) I (encW w) x < n := by
    intro w
    induction w with
    | nil =>
      intro x hx
      refine ⟨?_, hx⟩
      change (idA n)[x]! = x
      unfold idA
      rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
    | cons l w ih =>
      intro x hx
      obtain ⟨e, hlt⟩ := ih x hx
      obtain ⟨⟨g, hg⟩, s⟩ := l
      have ew : wordArrW n gens (gens.map (invCand n)) ((⟨g, hg⟩, s) :: w) =
          compA n (letterArrW gens (gens.map (invCand n)) (⟨g, hg⟩, s))
            (wordArrW n gens (gens.map (invCand n)) w) := rfl
      have ek : walk (gens.toList.map Array.toList) I (encW ((⟨g, hg⟩, s) :: w)) x =
          letterV (gens.toList.map Array.toList) I (g, s)
            (walk (gens.toList.map Array.toList) I (encW w) x) := rfl
      rw [ew, ek]
      unfold compA
      rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
      try dsimp only
      rw [e]
      generalize walk (gens.toList.map Array.toList) I (encW w) x = y at hlt ⊢
      cases s
      · change ((gens.map (invCand n)).getD g #[])[y]! = getL (getLL I g) y ∧
          getL (getLL I g) y < n
        rw [getLL_eqM, getL_eqM]
        exact hI g hg y hlt
      · change (gens.getD g #[])[y]! = getL (getLL (gens.toList.map Array.toList) g) y ∧
          getL (getLL (gens.toList.map Array.toList) g) y < n
        rw [hG]
        exact ⟨rfl, (hP g hg y hlt).1⟩
  have hR : ∀ R : List (List (ℕ × Bool)), List.rec (motive := fun _ => Bool) true
      (fun r _ ih => andB (allN n fun x => Nat.beq (walk (gens.toList.map Array.toList) I r x) x)
        ih) R = true →
      ∀ r ∈ R, ∀ x < n, walk (gens.toList.map Array.toList) I r x = x := by
    intro R
    induction R with
    | nil => intro _ r hr; simp at hr
    | cons r R ih =>
      intro hR r' hr' x hx
      change andB _ _ = true at hR
      rw [andB_iffM] at hR
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact Nat.eq_of_beq_eq_true (allN_specM hR.1 x hx)
      · exact ih hR.2 r' hr' x hx
  unfold modelCheck relArrCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨fun g hg => ?_, fun r hr => ?_⟩
  · unfold isInvA
    rw [allLt_iffM]
    intro i hi
    obtain ⟨p1, p2⟩ := hP g hg i hi
    rw [(hI g hg _ p1).1, p2, decide_eq_true p1, beq_self_eq_true]
    rfl
  · unfold eqA
    rw [allLt_iffM]
    intro x hx
    rw [(hW r x hx).1, hR _ h2 (encW r) (List.mem_map_of_mem hr) x hx]
    unfold idA
    rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
    simp

end CFSG.KC.CosetJ.ModelKS

end
