module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Check
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42Enum

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.P12

open Equiv
open CFSG.RankThree.PartTwo.Sec4.Item434F42 (wordElt wordElt_cons)

variable {n : ℕ}

@[expose] def permArr (n : ℕ) (σ : Perm (Fin n)) : Array ℕ :=
  Array.ofFn (n := n) fun i => (σ i : ℕ)

theorem permArr_getElem! (σ : Perm (Fin n)) {k : ℕ} (hk : k < n) :
    (permArr n σ)[k]! = (σ ⟨k, hk⟩ : ℕ) := by
  rw [permArr, getElem!_pos (Array.ofFn _) k (by simpa using hk), Array.getElem_ofFn]

theorem permArr_injective : Function.Injective (permArr n) := by
  intro σ τ h
  ext i
  have h1 := permArr_getElem! σ i.isLt
  have h2 := permArr_getElem! τ i.isLt
  rw [h] at h1
  exact h1.symm.trans h2

theorem pmul_permArr (σ τ : Perm (Fin n)) :
    pmul n (permArr n σ) (permArr n τ) = permArr n (σ * τ) := by
  have key : ∀ i : Fin n, (permArr n σ)[(permArr n τ)[i.val]!]! = ((σ * τ) i : ℕ) := by
    intro i
    rw [permArr_getElem! τ i.isLt, permArr_getElem! σ (τ ⟨i.val, i.isLt⟩).isLt]
    rfl
  unfold pmul
  rw [show (fun i : Fin n => (permArr n σ)[(permArr n τ)[i.val]!]!) =
    fun i => (((σ * τ) i : Fin n) : ℕ) from funext key]
  rfl

theorem pid_eq_permArr : pid n = permArr n (1 : Perm (Fin n)) := rfl

theorem pswap_eq_permArr {a b : ℕ} (ha : a < n) (hb : b < n) :
    pswap n a b = permArr n (Equiv.swap (⟨a, ha⟩ : Fin n) ⟨b, hb⟩) := by
  unfold pswap permArr
  congr 1
  funext i
  rw [Equiv.swap_apply_def]
  by_cases h1 : i.val = a
  · have : i = ⟨a, ha⟩ := Fin.ext h1
    simp [this]
  · by_cases h2 : i.val = b
    · have : i = ⟨b, hb⟩ := Fin.ext h2
      by_cases hba : b = a
      · subst hba; simp [this]
      · simp [this, hba]
    · have e1 : i ≠ ⟨a, ha⟩ := fun h => h1 (by simpa using congrArg Fin.val h)
      have e2 : i ≠ ⟨b, hb⟩ := fun h => h2 (by simpa using congrArg Fin.val h)
      simp [h1, h2, e1, e2]

@[expose] def swapPerm (n : ℕ) (ab : ℕ × ℕ) : Perm (Fin n) :=
  if h : ab.1 < n ∧ ab.2 < n then Equiv.swap ⟨ab.1, h.1⟩ ⟨ab.2, h.2⟩ else 1

@[expose] def swapsPerm (n : ℕ) (w : List (ℕ × ℕ)) : Perm (Fin n) := (w.map (swapPerm n)).prod

theorem swapsOK_iff {w : List (ℕ × ℕ)} :
    swapsOK n w = true ↔ w.length % 2 = 0 ∧ ∀ ab ∈ w, ab.1 < n ∧ ab.2 < n ∧ ab.1 ≠ ab.2 := by
  simp only [swapsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq, and_assoc]

theorem swapsOK_bounds {w : List (ℕ × ℕ)} (h : swapsOK n w = true) :
    ∀ ab ∈ w, ab.1 < n ∧ ab.2 < n := fun ab hab =>
  ⟨(swapsOK_iff.1 h).2 ab hab |>.1, (swapsOK_iff.1 h).2 ab hab |>.2.1⟩

theorem swapsOK_ne {w : List (ℕ × ℕ)} (h : swapsOK n w = true) : ∀ ab ∈ w, ab.1 ≠ ab.2 :=
  fun ab hab => ((swapsOK_iff.1 h).2 ab hab).2.2

theorem swapsOK_even {w : List (ℕ × ℕ)} (h : swapsOK n w = true) : Even w.length :=
  Nat.even_iff.2 (swapsOK_iff.1 h).1

theorem swapsArr_eq {w : List (ℕ × ℕ)} (h : ∀ ab ∈ w, ab.1 < n ∧ ab.2 < n) :
    swapsArr n w = permArr n (swapsPerm n w) := by
  induction w with
  | nil => simp [swapsArr, swapsPerm, pid_eq_permArr]
  | cons ab w ih =>
    have hab := h ab (List.mem_cons_self ..)
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have e : swapsPerm n (ab :: w) =
        Equiv.swap (⟨ab.1, hab.1⟩ : Fin n) ⟨ab.2, hab.2⟩ * swapsPerm n w := by
      simp [swapsPerm, swapPerm, hab]
    rw [e, ← pmul_permArr, ← ih', ← pswap_eq_permArr hab.1 hab.2]
    rfl

theorem sign_swapsPerm {w : List (ℕ × ℕ)} (h : swapsOK n w = true) :
    Perm.sign (swapsPerm n w) = 1 := by
  have hb := swapsOK_bounds h
  have hne := swapsOK_ne h
  have hev := swapsOK_even h
  rw [swapsPerm, Perm.sign_prod_list_swap]
  · simpa using hev.neg_one_pow
  · intro g hg
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.1 hg
    refine ⟨⟨ab.1, (hb ab hab).1⟩, ⟨ab.2, (hb ab hab).2⟩, ?_, ?_⟩
    · intro e
      exact hne ab hab (congrArg Fin.val e)
    · simp [swapPerm, hb ab hab]

@[expose] def gensFn (n : ℕ) (ws : List (List (ℕ × ℕ))) (k : ℕ) : alternatingGroup (Fin n) :=
  if h : swapsOK n (ws.getD k []) = true then
    ⟨swapsPerm n (ws.getD k []), Perm.mem_alternatingGroup.2 (sign_swapsPerm h)⟩ else 1

theorem gensFn_coe {ws : List (List (ℕ × ℕ))} {k : ℕ} (hk : k < ws.length)
    (hv : ∀ w ∈ ws, swapsOK n w = true) :
    ((gensFn n ws k : alternatingGroup (Fin n)) : Perm (Fin n)) = swapsPerm n (ws.getD k []) := by
  have h : swapsOK n (ws.getD k []) = true := by
    rw [List.getD_eq_getElem _ _ hk]
    exact hv _ (List.getElem_mem hk)
  unfold gensFn
  rw [dif_pos h]

theorem permArr_gensFn {ws : List (List (ℕ × ℕ))} {k : ℕ} (hk : k < ws.length)
    (hv : ∀ w ∈ ws, swapsOK n w = true) :
    (ws.map (swapsArr n)).getD k #[] = permArr n ((gensFn n ws k : alternatingGroup (Fin n)) :
      Perm (Fin n)) := by
  rw [gensFn_coe hk hv, List.getD_eq_getElem _ _ (by simpa using hk),
    List.getD_eq_getElem _ _ hk]
  simp only [List.getElem_map]
  exact swapsArr_eq (swapsOK_bounds (hv _ (List.getElem_mem hk)))

theorem wordArr_eq {ws : List (List (ℕ × ℕ))} (hv : ∀ w ∈ ws, swapsOK n w = true)
    {w : List ℕ} (hw : ∀ l ∈ w, l < ws.length) :
    wordArr n (ws.map (swapsArr n)) w =
      permArr n ((wordElt (gensFn n ws) w : alternatingGroup (Fin n)) : Perm (Fin n)) := by
  induction w with
  | nil => simp [wordArr, wordElt, pid_eq_permArr]
  | cons l w ih =>
    have ih' := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    rw [wordElt_cons, wordArr, List.foldr_cons, ← wordArr, ih',
      permArr_gensFn (hw l (List.mem_cons_self ..)) hv, pmul_permArr]
    rfl

end CFSG.EvenSporadicStandard.M12Std.SolomonK.P12
