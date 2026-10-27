module

public import Certificates.Data.Kernel.N6ModClass

public section

namespace CFSG.KernelN6

open CFSG.CGT.T75JM

abbrev Small (c : Cols) : Prop := ∀ i, c.col i < 16

theorem compC_assoc (a b c : Cols) : compC (compC a b) c = compC a (compC b c) := by
  ext <;> exact applyC_compC a b _

theorem small_compC {a : Cols} (ha : Small a) (b : Cols) : Small (compC a b) := by
  intro i
  fin_cases i <;> exact applyC_lt ha _

theorem small_idC : Small idC := by
  intro i
  fin_cases i <;> decide

theorem small_unpackC (m : ℕ) : Small (unpackC m) := by
  intro i
  fin_cases i <;> simp only [unpackC, Cols.col] <;> omega

theorem idC_compC {c : Cols} (hc : Small c) : compC idC c = c := by
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  simp only [Cols.col] at h0 h1 h2 h3
  ext <;> simp only [compC] <;> exact applyC_idC (by assumption)

theorem small_powC {a : Cols} (ha : Small a) : ∀ n, Small (powC a n)
  | 0 => small_idC
  | _ + 1 => small_compC ha _

theorem small_evalC {X Y : Cols} (hX : Small X) (hY : Small Y) : ∀ w, Small (evalC X Y w)
  | [] => small_idC
  | l :: _ => by
    unfold evalC
    split
    · exact small_compC hX _
    · exact small_compC hY _

structure InvPair (P Pi : Cols) : Prop where
  sP : Small P
  sPi : Small Pi
  left : compC Pi P = idC
  right : compC P Pi = idC

namespace InvPair

variable {P Pi : Cols} (h : InvPair P Pi)
include h

theorem cj_comp {A B : Cols} (hB : Small B) :
    compC (cjC P Pi A) (cjC P Pi B) = cjC P Pi (compC A B) := by
  unfold cjC
  rw [compC_assoc, ← compC_assoc P, ← compC_assoc P, h.right, idC_compC hB]
  simp only [compC_assoc]

theorem cj_id : cjC P Pi idC = idC := by
  unfold cjC
  rw [compC_idC, h.left]

theorem cj_pow {A : Cols} (hA : Small A) : ∀ n, powC (cjC P Pi A) n = cjC P Pi (powC A n)
  | 0 => h.cj_id.symm
  | n + 1 => by
    simp only [powC]
    rw [cj_pow hA n, h.cj_comp (small_powC hA n)]

theorem cj_evalC {X Y : Cols} (hX : Small X) (hY : Small Y) :
    ∀ w, evalC (cjC P Pi X) (cjC P Pi Y) w = cjC P Pi (evalC X Y w)
  | [] => h.cj_id.symm
  | l :: w => by
    simp only [evalC]
    rw [cj_evalC hX hY w]
    split
    · exact h.cj_comp (small_evalC hX hY w)
    · exact h.cj_comp (small_evalC hX hY w)

theorem uncj {A : Cols} (hA : Small A) : compC (compC P (cjC P Pi A)) Pi = A := by
  unfold cjC
  rw [← compC_assoc, ← compC_assoc, h.right, idC_compC hA, compC_assoc, h.right, compC_idC]

theorem relC_cj {X Y : Cols} (hX : Small X) (hY : Small Y) (hr : RelC X Y) :
    RelC (cjC P Pi X) (cjC P Pi Y) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h.cj_comp hX, h1, h.cj_id]
  · intro he
    apply h2
    rw [← h.uncj hX, he, compC_idC, h.right]
  · rw [h.cj_pow hY, h3, h.cj_id]
  · rw [h.cj_comp hY, h.cj_pow (small_compC hX Y), h4, h.cj_id]
  · rw [h.cj_comp hY, h.cj_comp (small_compC hY Y), h.cj_pow (small_compC hX _), h5, h.cj_id]

theorem equivC_of_cj {X Y : Cols} (hX : Small X) (hY : Small Y)
    (he : EquivC (cjC P Pi X) (cjC P Pi Y)) : EquivC X Y := by
  obtain ⟨Q, Qi, hQ, hQi, h1, h2, h3, h4⟩ := he
  have sQ : Small Q := hQ
  have sQi : Small Qi := hQi
  have back : ∀ {A : Cols}, Small A → compC A P = compC P (cjC P Pi A) := fun {A} hA => by
    unfold cjC
    rw [← compC_assoc, ← compC_assoc, h.right, idC_compC hA]
  refine ⟨compC P Q, compC Qi Pi, small_compC h.sP Q, small_compC sQi Pi, ?_, ?_, ?_, ?_⟩
  · rw [compC_assoc, ← compC_assoc Pi, h.left, idC_compC sQ, h1]
  · rw [compC_assoc, ← compC_assoc Q, h2, idC_compC h.sPi, h.right]
  · rw [← compC_assoc, back hX, compC_assoc, h3, compC_assoc]
  · rw [← compC_assoc, back hY, compC_assoc, h4, compC_assoc]

end InvPair

theorem eqC_iff {a b : Cols} : eqC a b = true ↔ a = b := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  simp [eqC, Nat.beq_eq, and_assoc]

theorem small_of_smallB {a : Cols} (h : smallB a = true) : Small a := by
  simp only [smallB, Bool.and_eq_true, Nat.blt_eq] at h
  intro i
  fin_cases i <;> simp only [Cols.col] <;> omega

theorem relCB_iff {X Y : Cols} : relCB X Y = true ↔ RelC X Y := by
  simp only [relCB, RelC, Bool.and_eq_true, Bool.not_eq_true', eqC_iff, Bool.eq_false_iff, ne_eq]
  tauto

theorem equivData_of_equivB {X Y Q Qi : Cols} (h : equivB X Y Q Qi = true) : EquivData X Y Q Qi := by
  simp only [equivB, Bool.and_eq_true, eqC_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨small_of_smallB h1, small_of_smallB h2, h3, h4, h5, h6⟩

theorem eqNL_eq : ∀ {s t : List ℕ}, eqNL s t = true → s = t
  | [], [] => fun _ => rfl
  | a :: s, b :: t => fun h => by
    simp only [eqNL, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, eqNL_eq h.2]
  | [], _ :: _ => fun h => by simp [eqNL] at h
  | _ :: _, [] => fun h => by simp [eqNL] at h

theorem mem_of_filter {p : ℕ → Bool} {L : List ℕ}
    (h : eqNL ((List.range' 0 65536).filter p) (L.map (· % 65536)) = true) {m : ℕ}
    (hm : m < 65536) (hp : p m = true) : ∃ e ∈ L, e % 65536 = m := by
  have h' := eqNL_eq h
  have : m ∈ (List.range' 0 65536).filter p :=
    List.mem_filter.2 ⟨List.mem_range'_1.2 ⟨Nat.zero_le _, hm⟩, hp⟩
  rw [h'] at this
  exact List.mem_map.1 this

theorem conj_rep {L : List ℕ} (hL : invAll L = true) {X : Cols} (hX : Small X)
    (h1 : compC X X = idC) (h2 : X ≠ idC) :
    ∃ P Pi r, InvPair P Pi ∧ cjC P Pi X = repC r := by
  unfold invAll at hL
  rw [Bool.and_eq_true, List.all_eq_true] at hL
  have hm := packC_lt hX
  have hp : isInvB (packC X) = true := by
    unfold isInvB
    rw [unpackC_packC hX, Bool.and_eq_true, eqC_iff, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      eqC_iff]
    exact ⟨h1, h2⟩
  obtain ⟨e, he, hem⟩ := mem_of_filter hL.1 hm hp
  have hok := hL.2 e he
  simp only [invRecOK, Bool.and_eq_true, eqC_iff] at hok
  rw [hem, unpackC_packC hX] at hok
  exact ⟨_, _, _, ⟨small_unpackC _, small_unpackC _, hok.1.1, hok.1.2⟩, hok.2⟩

theorem rel_rep {L₀ : List ℕ} (h0 : relAll 0 L₀ = true) (h1 : relAll 1 [] = true) (r : ℕ)
    {Y : Cols} (hY : Small Y) (hr : RelC (repC r) Y) :
    EquivC (repC r) Y ∨ EquivC (repC r) (evalC (repC r) Y twistWord) := by
  have key : ∀ {r' : ℕ} {L : List ℕ}, relAll r' L = true → RelC (repC r') Y →
      ∃ e ∈ L, e % 65536 = packC Y ∧ relRecOK e = true := by
    intro r' L h hrel
    unfold relAll at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    have hp : relB r' (packC Y) = true := by
      unfold relB
      rw [unpackC_packC hY]
      exact relCB_iff.2 hrel
    obtain ⟨e, he, hem⟩ := mem_of_filter h.1 (packC_lt hY) hp
    exact ⟨e, he, hem, h.2 e he⟩
  by_cases hr0 : r = 0
  · subst hr0
    obtain ⟨e, -, hem, hok⟩ := key h0 hr
    unfold relRecOK at hok
    rw [hem, unpackC_packC hY] at hok
    have hok := equivData_of_equivB hok
    have hrep : repC 0 = modelX := rfl
    rw [hrep]
    split at hok
    · exact Or.inl ⟨_, _, hok⟩
    · exact Or.inr ⟨_, _, hok⟩
  · have hrep : repC r = repC 1 := by simp [repC, hr0]
    rw [hrep] at hr
    obtain ⟨e, he, -, -⟩ := key h1 hr
    simp at he

theorem modClass_of_checks {L L₀ : List ℕ} (hA : invAll L = true) (h0 : relAll 0 L₀ = true)
    (h1 : relAll 1 [] = true) : ModClass := by
  intro X Y hX hY hrel
  obtain ⟨P, Pi, r, hP, hc⟩ := conj_rep hA hX hrel.1 hrel.2.1
  have hrel' := hP.relC_cj hX hY hrel
  rw [hc] at hrel'
  have sY' : Small (cjC P Pi Y) := small_compC (small_compC hP.sPi Y) P
  rcases rel_rep h0 h1 r sY' hrel' with he | he
  · left
    rw [← hc] at he
    exact hP.equivC_of_cj hX hY he
  · right
    rw [← hc, hP.cj_evalC hX hY] at he
    exact hP.equivC_of_cj hX (small_evalC hX hY _) he

end CFSG.KernelN6
