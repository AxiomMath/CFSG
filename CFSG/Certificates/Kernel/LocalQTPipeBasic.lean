module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public import CFSG.Certificates.Kernel.LocalQTBaseWProved

public section

namespace CFSG.KC.LQT.PPB

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW.Pf
open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem chunksK_eq (c : Array (Array Nat)) : chunksK c = (Array.flatten c).toList := by
  have e : ∀ l : List (Array Nat),
      (List.rec (motive := fun _ => List (List Nat)) [] (fun a _ ih => List.cons a.toList ih) l :
        List (List Nat)) = l.map Array.toList := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih =>
      change a.toList :: _ = _
      rw [ih]
      rfl
  rw [chunksK, e, flatK_eq, Array.toList_flatten]

theorem length_chunksK (c : Array (Array Nat)) : (chunksK c).length = (Array.flatten c).size := by
  rw [chunksK_eq, Array.length_toList]

theorem rep_chunksK {n w : Nat} (hw : n ≤ 2 ^ w) {c : Array (Array Nat)}
    (h : tabL n (chunksK c) = true) : Rep n w (codeK w (chunksK c)) (Array.flatten c) := by
  have := rep_codeK hw h
  rw [chunksK_eq] at this ⊢
  rw [Array.toArray_toList] at this
  exact this

private noncomputable def treeLoop (P : List Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool) (fun _ _ => true)
      (fun p _ ih gs i => List.rec (motive := fun _ => Bool) false
        (fun g gs' _ => CFSG.KC.LQT.P.letB i fun i' =>
          andB (impB (Nat.blt 0 i') (andB (Nat.blt p i') (Nat.blt g 2))) (ih gs' (Nat.succ i')))
        gs) P

private theorem treeLoop_spec : ∀ (P G : List Nat) (i : Nat), treeLoop P G i = true →
    ∀ j < P.length, 0 < i + j → P.getD j 0 < i + j ∧ G.getD j 0 < 2
  | [], _, _, _, j, hj, _ => by simp at hj
  | p :: P, [], i, h, _, _, _ => by
    have : treeLoop (p :: P) [] i = false := rfl
    rw [this] at h
    exact absurd h (by decide)
  | p :: P, g :: G, i, h, j, hj, hij => by
    have e : treeLoop (p :: P) (g :: G) i = andB (impB (Nat.blt 0 i)
        (andB (Nat.blt p i) (Nat.blt g 2))) (treeLoop P G (Nat.succ i)) := by
      have e0 : treeLoop (p :: P) (g :: G) i = letB i fun i' => andB (impB (Nat.blt 0 i')
          (andB (Nat.blt p i') (Nat.blt g 2))) (treeLoop P G (Nat.succ i')) := rfl
      rw [e0, letB_eq]
    rw [e, andB_iff, impB_iff, andB_iff, blt_iff, blt_iff, blt_iff] at h
    obtain ⟨h1, h2⟩ := h
    cases j with
    | zero =>
      have hi : 0 < i := by simpa using hij
      obtain ⟨h3, h4⟩ := h1 hi
      simp only [List.getD_cons_zero, Nat.add_zero]
      exact ⟨h3, h4⟩
    | succ j =>
      have := treeLoop_spec P G (Nat.succ i) h2 j (by simpa using hj) (by omega)
      have e2 : Nat.succ i + j = i + (j + 1) := by omega
      rw [e2] at this
      simpa only [List.getD_cons_succ] using this

theorem tree_sound (N : Nat) (ps gs : Array (Array Nat))
    (h : treeK N (chunksK ps) (chunksK gs) = true) :
    treeValid N (Array.flatten ps) (Array.flatten gs) := by
  have e : treeK N (chunksK ps) (chunksK gs) = andB (Nat.beq (lenA (chunksK ps)) N)
      (andB (Nat.beq (lenA (chunksK gs)) N) (treeLoop (chunksK ps) (chunksK gs) 0)) := rfl
  rw [e, andB_iff, andB_iff, beq_iff, beq_iff, lenA_eq, lenA_eq, length_chunksK,
    length_chunksK] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hs := treeLoop_spec _ _ 0 h3
  rw [chunksK_eq, chunksK_eq] at hs
  refine ⟨h1, h2, fun i hi hi0 => ?_⟩
  have := hs i (by rw [Array.length_toList]; omega) (by omega)
  have key : ∀ (a : Array Nat) (i : Nat), a.getD i 0 = a.toList.getD i 0 := by
    intro a i
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rw [key, key, Nat.zero_add] at *
  exact this

theorem inv_sound {n w : Nat} (hw : n ≤ 2 ^ w) (a b ai bi : Array (Array Nat))
    (h : invK n w (chunksK a) (chunksK b) (chunksK ai) (chunksK bi) = true) :
    invValid n (Array.flatten a) (Array.flatten b) (Array.flatten ai) (Array.flatten bi) := by
  unfold invK at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨ha, hb, hai, hbi, h1, h2⟩ := h
  have h1' := Nat.eq_of_beq_eq_true h1
  have h2' := Nat.eq_of_beq_eq_true h2
  have ra := rep_chunksK hw ha
  have rb := rep_chunksK hw hb
  have rai := rep_chunksK hw hai
  have rbi := rep_chunksK hw hbi
  have ia := rep_inv ra rai hw h1'
  have ib := rep_inv rb rbi hw h2'
  exact ⟨ra.1, rb.1, rai.1, rbi.1, fun q hq => ⟨ia q hq, ib q hq⟩⟩

theorem asz_sound (N : Nat) (a b : Array (Array Nat)) (h : aszK N (chunksK a) (chunksK b) = true) :
    aszOK N (Array.flatten a) (Array.flatten b) := by
  unfold aszK at h
  rw [andB_iff, lenA_eq, lenA_eq, length_chunksK, length_chunksK] at h
  exact ⟨Nat.le_of_ble_eq_true h.1, Nat.le_of_ble_eq_true h.2⟩

theorem xs_sound (N : Nat) (xs : Array (List Nat)) (h : xsK N xs.toList = true) : xsOK N xs := by
  unfold xsK at h
  rw [andB_iff, andB_iff, blt_iff, lenA_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [allA_eq, List.all_eq_true] at h3
  have key : ∀ l ∈ xs.toList, ∀ x ∈ l, x < N := by
    intro l hl x hx
    have := h3 l hl
    rw [allL_eq, List.all_eq_true] at this
    simpa using this x hx
  refine ⟨by simpa using h1, ?_, fun i hi x hx => ?_⟩
  · have hz : xs.toList ≠ [] := fun e => by rw [e] at h1; simp at h1
    obtain ⟨l, t, ht⟩ := List.exists_cons_of_ne_nil hz
    rw [ht] at h2
    have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons y l' => exact Bool.noConfusion (show false = true from h2)
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ht, hl]
    rfl
  · have hmem : xs.getD i [] ∈ xs.toList := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
      exact Array.getElem_mem_toList ..
    exact key _ hmem x hx

end CFSG.KC.LQT.PPB

end
