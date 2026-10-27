module

public import Certificates.Data.Kernel.Co1Three.Seeds
public import CFSG.Certificates.Kernel.Co1BWordSound
public import CFSG.Certificates.Kernel.Co1BSound
public import CFSG.Sporadic.Schreier.Co1Base

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Enum CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem brec_eq_true (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = true ↔ (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp

theorem nrec_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem getL_eq (x : Nat) (L : List Nat) (i : Nat) : getL x L i = L.getD i x := by
  induction L generalizing i with
  | nil => rfl
  | cons a L ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem lenL_eq (L : List Nat) : lenL L = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => exact congrArg Nat.succ ih

theorem getL_mem {S : List Nat} {r : Nat} (h : r < S.length) : getL 0 S r ∈ S := by
  rw [getL_eq, List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem chGet_eq (CH : List (Nat × Nat × List Nat)) (i : Nat) : chGet CH i = CH.getD i (0, 0, []) := by
  induction CH generalizing i with
  | nil => rfl
  | cons a L ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem eqLK_sound : ∀ a b : List Nat, eqLK a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [eqLK])
  | _ :: _, [], h => absurd h (by simp [eqLK])
  | x :: a, y :: b, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (eqLK a b) (Nat.beq x y) = true := h
    rw [brec_eq_true] at h'
    simp only [Bool.false_eq_true, and_false, or_false, Nat.beq_eq] at h'
    rw [h'.1, eqLK_sound a b h'.2]

@[expose] def NodeIn (H : Subgroup GL24) (TS : Nat → Nat) (k : Nat) : Prop :=
  ∃ g ∈ H, MRep (unpackR 24 (TS k)) g

theorem mRep_mulWK {A B : Nat} {g h : GL24} (hA : MRep (unpackR 24 A) g) (hB : MRep (unpackR 24 B) h) :
    MRep (unpackR 24 (mulWK A B)) (g * h) := by
  have := hA.mul hB
  rwa [Native.mul, mulWK_unpack] at this

theorem mRep_of_mulWK_one {W X : Nat} {g : GL24} (hX : MRep (unpackR 24 X) g) (h : mulWK W X = oneK) :
    MRep (unpackR 24 W) g⁻¹ := by
  have h1 : rowsMatrix 24 (unpackR 24 W) * (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) = 1 := by
    rw [← hX, ← rowsMatrix_mulRows, mulWK_unpack, h, ← one_eq]
    exact MRep.one
  unfold MRep
  calc rowsMatrix 24 (unpackR 24 W)
      = rowsMatrix 24 (unpackR 24 W) * ((g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
          ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))) := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    _ = ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by rw [← mul_assoc, h1, one_mul]

theorem okRefK_sound {S : List Nat} {lo k r : Nat} (h : okRefK S.length lo k r = true) :
    refK S S.length lo r ∈ S ∨ (lo ≤ refK S S.length lo r ∧ refK S S.length lo r < k) := by
  unfold okRefK at h
  unfold refK
  rw [brec_eq_true] at h
  rw [nrec_eq]
  rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · rw [if_pos h1]
    rw [Nat.blt_eq] at h1
    exact Or.inl (getL_mem h1)
  · rw [h1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Nat.blt_eq] at h2
    exact Or.inr ⟨Nat.le_add_right _ _, h2⟩

theorem recK_sound {TS : Nat → Nat} {S : List Nat} {lo k c : Nat} (h : recK TS S lo k c = true) :
    ∃ r₁ r₂, okRefK S.length lo k r₁ = true ∧
      ((okRefK S.length lo k r₂ = true ∧
          TS k = mulWK (TS (refK S S.length lo r₁)) (TS (refK S S.length lo r₂))) ∨
        mulWK (TS k) (TS (refK S S.length lo r₁)) = oneK) := by
  unfold recK at h
  simp only [strictB_eq, lenL_eq] at h
  refine ⟨(c.shiftRight 1).land 1048575, c.shiftRight 21, ?_⟩
  simp only [brec_eq_true, Bool.false_eq_true, and_false, or_false] at h
  obtain ⟨-, h1, h3⟩ := h
  refine ⟨h1, ?_⟩
  rcases h3 with ⟨-, h3⟩ | ⟨-, h3, h4⟩
  · exact Or.inr (Nat.eq_of_beq_eq_true h3)
  · exact Or.inl ⟨h3, Nat.eq_of_beq_eq_true h4⟩

theorem runK_cons (TS : Nat → Nat) (S : List Nat) (lo k c : Nat) (cs : List Nat) :
    runK TS S lo k (c :: cs) = Bool.rec (motive := fun _ => Bool) false (runK TS S lo (k + 1) cs)
      (recK TS S lo k c) := by
  change strictB k (fun k => Bool.rec (motive := fun _ => Bool) false (runK TS S lo (Nat.succ k) cs)
    (recK TS S lo k c)) = _
  rw [strictB_eq]

theorem runK_sound {TS : Nat → Nat} {S : List Nat} {lo : Nat} :
    ∀ {k : Nat} {cs : List Nat}, runK TS S lo k cs = true →
      ∀ j < cs.length, recK TS S lo (k + j) (cs.getD j 0) = true
  | _, [], _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k, c :: cs, h, j, hj => by
    rw [runK_cons, brec_eq_true] at h
    simp only [Bool.false_eq_true, and_false, or_false] at h
    cases j with
    | zero => exact h.1
    | succ j =>
      have := runK_sound h.2 j (Nat.lt_of_succ_lt_succ hj)
      rwa [Nat.add_right_comm, Nat.add_assoc] at this

theorem chunkK_sound {TS : Nat → Nat} {CH : List (Nat × Nat × List Nat)} {WL : Nat → List Nat} {i : Nat}
    (h : chunkK TS CH WL i = true) :
    ∀ j < (WL i).length, recK TS (CH.getD i (0, 0, [])).2.2 (CH.getD i (0, 0, [])).2.1
      ((CH.getD i (0, 0, [])).1 + j) ((WL i).getD j 0) = true := by
  unfold chunkK at h
  rw [chGet_eq] at h
  generalize CH.getD i (0, 0, []) = x at h ⊢
  obtain ⟨st, lo, S⟩ := x
  exact runK_sound h

@[expose] def InChunk (CH : List (Nat × Nat × List Nat)) (WL : Nat → List Nat) (j m : Nat) : Prop :=
  (CH.getD j (0, 0, [])).1 ≤ m ∧ m < (CH.getD j (0, 0, [])).1 + (WL j).length

theorem layFromK_cons (WL : Nat → List Nat) (N st lo : Nat) (S : List Nat) (CH : List (Nat × Nat × List Nat))
    (i s plo : Nat) (pS : List Nat) :
    layFromK WL N ((st, lo, S) :: CH) i s plo pS = true ↔ st = s ∧ (lo = st ∨ (lo = plo ∧ eqLK S pS = true)) ∧
      layFromK WL N CH (i + 1) (st + (WL i).length) lo S = true := by
  change strictB i (fun i => strictB s fun s =>
    Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (layFromK WL N CH (Nat.succ i) (Nat.add st (lenL (WL i))) lo S)
      (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (eqLK S pS) (Nat.beq lo plo))
        true (Nat.beq lo st))) (Nat.beq st s)) = true ↔ _
  rw [strictB_eq, strictB_eq, lenL_eq]
  simp only [brec_eq_true, Bool.false_eq_true, and_false, or_false, Nat.beq_eq, true_and, and_true]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    rcases h2 with h2 | ⟨-, h4⟩
    · exact Or.inl h2
    · exact Or.inr h4
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    by_cases hl : lo = st
    · exact Or.inl hl
    · refine Or.inr ⟨?_, ?_⟩
      · exact Bool.eq_false_iff.2 fun h => hl (Nat.eq_of_beq_eq_true h)
      · rcases h2 with h2 | h2
        · exact absurd h2 hl
        · exact ⟨h2.1, h2.2⟩

theorem layFromK_sound (WL : Nat → List Nat) (N : Nat) :
    ∀ (CH : List (Nat × Nat × List Nat)) (i s plo : Nat) (pS : List Nat),
      layFromK WL N CH i s plo pS = true →
      (∀ k, s ≤ k → k < N → ∃ j < CH.length, InChunk CH (fun j => WL (i + j)) j k) ∧
      (∀ j < CH.length, ∀ m, (CH.getD j (0, 0, [])).2.1 ≤ m → m < (CH.getD j (0, 0, [])).1 →
        (∃ j' < CH.length, InChunk CH (fun j => WL (i + j)) j' m ∧
          (CH.getD j' (0, 0, [])).2 = (CH.getD j (0, 0, [])).2) ∨
        (plo ≤ m ∧ m < s ∧ (CH.getD j (0, 0, [])).2 = (plo, pS)))
  | [], i, s, plo, pS, h => by
    have hs : s = N := Nat.eq_of_beq_eq_true h
    refine ⟨fun k h1 h2 => absurd (hs ▸ h1) (Nat.not_le.2 h2), fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | (st, lo, S) :: CH, i, s, plo, pS, h => by
    rw [layFromK_cons] at h
    obtain ⟨rfl, hlo, h⟩ := h
    obtain ⟨hA, hB⟩ := layFromK_sound WL N CH (i + 1) (st + (WL i).length) lo S h
    have head : ∀ m, lo ≤ m → m < st → plo ≤ m ∧ m < st ∧ (lo, S) = (plo, pS) := by
      intro m h1 h2
      rcases hlo with hlo | ⟨hlo, hS⟩
      · exact absurd (hlo ▸ h1) (Nat.not_le.2 h2)
      · rw [eqLK_sound S pS hS, ← hlo]
        exact ⟨h1, h2, rfl⟩
    refine ⟨fun k h1 h2 => ?_, fun j hj m h1 h2 => ?_⟩
    · by_cases hk : k < st + (WL i).length
      · exact ⟨0, Nat.succ_pos _, h1, by simpa using hk⟩
      · obtain ⟨j, hj, hc⟩ := hA k (Nat.le_of_not_lt hk) h2
        refine ⟨j + 1, Nat.succ_lt_succ hj, ?_⟩
        simpa [InChunk, Nat.add_assoc, Nat.add_comm 1] using hc
    · cases j with
      | zero => exact Or.inr (by simpa using head m h1 h2)
      | succ j =>
        simp only [List.getD_cons_succ] at h1 h2 ⊢
        rcases hB j (Nat.lt_of_succ_lt_succ hj) m h1 h2 with ⟨j', hj', hc, he⟩ | ⟨h3, h4, he⟩
        · refine Or.inl ⟨j' + 1, Nat.succ_lt_succ hj', ?_, by simpa using he⟩
          simpa [InChunk, Nat.add_assoc, Nat.add_comm 1] using hc
        · rw [he]
          by_cases hm : st ≤ m
          · exact Or.inl ⟨0, Nat.succ_pos _, ⟨by simpa using hm, by simpa using h4⟩, by simp⟩
          · exact Or.inr (head m h3 (Nat.lt_of_not_le hm))

theorem layoutK_sound {CH : List (Nat × Nat × List Nat)} {WL : Nat → List Nat} {n₀ N : Nat}
    (h : layoutK CH WL n₀ N = true) :
    (∀ k, n₀ ≤ k → k < N → ∃ j < CH.length, InChunk CH WL j k) ∧
    (∀ j < CH.length, ∀ m, (CH.getD j (0, 0, [])).2.1 ≤ m → m < (CH.getD j (0, 0, [])).1 →
      ∃ j' < CH.length, InChunk CH WL j' m ∧ (CH.getD j' (0, 0, [])).2 = (CH.getD j (0, 0, [])).2) := by
  obtain ⟨hA, hB⟩ := layFromK_sound WL N CH 0 n₀ n₀ [] h
  simp only [Nat.zero_add] at hA hB
  refine ⟨hA, fun j hj m h1 h2 => ?_⟩
  rcases hB j hj m h1 h2 with h3 | ⟨h3, h4, -⟩
  · exact h3
  · exact absurd h3 (Nat.not_le.2 h4)

theorem seedsBelowK_sound :
    ∀ {CH : List (Nat × Nat × List Nat)}, seedsBelowK CH = true →
      ∀ j < CH.length, ∀ s ∈ (CH.getD j (0, 0, [])).2.2, s < (CH.getD j (0, 0, [])).1
  | [], _, j, hj => absurd hj (Nat.not_lt_zero j)
  | (st, lo, S) :: CH, h, j, hj => by
    have h' : Bool.rec (motive := fun _ => Bool) false (seedsBelowK CH) (allLtK st S) = true := h
    rw [brec_eq_true] at h'
    simp only [Bool.false_eq_true, and_false, or_false] at h'
    cases j with
    | zero =>
      intro s hs
      have key : ∀ T : List Nat, allLtK st T = true → ∀ s ∈ T, s < st := by
        intro T
        induction T with
        | nil => intro _ s hs; exact absurd hs List.not_mem_nil
        | cons a T ih =>
          intro hT s hs
          have hT' : Bool.rec (motive := fun _ => Bool) false (allLtK st T) (Nat.blt a st) = true := hT
          rw [brec_eq_true] at hT'
          simp only [Bool.false_eq_true, and_false, or_false, Nat.blt_eq] at hT'
          rcases List.mem_cons.1 hs with rfl | hs
          · exact hT'.1
          · exact ih hT'.2 s hs
      exact key S h'.1 s hs
    | succ j => exact seedsBelowK_sound h'.2 j (Nat.lt_of_succ_lt_succ hj)

theorem nodeIn_chunk (H : Subgroup GL24) {TS : Nat → Nat} {CH : List (Nat × Nat × List Nat)}
    {WL : Nat → List Nat} {n₀ N : Nat} (hlay : layoutK CH WL n₀ N = true)
    (hch : ∀ j < CH.length, chunkK TS CH WL j = true) :
    ∀ k j, j < CH.length → InChunk CH WL j k → (∀ s ∈ (CH.getD j (0, 0, [])).2.2, NodeIn H TS s) →
      NodeIn H TS k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hj hk hS
    obtain ⟨-, hB⟩ := layoutK_sound hlay
    have hr := chunkK_sound (hch j hj) (k - (CH.getD j (0, 0, [])).1) (by have := hk.2; have := hk.1; omega)
    rw [Nat.add_sub_cancel' hk.1] at hr
    obtain ⟨r₁, r₂, h₁, h₂⟩ := recK_sound hr
    have href : ∀ r, okRefK (CH.getD j (0, 0, [])).2.2.length (CH.getD j (0, 0, [])).2.1 k r = true →
        NodeIn H TS (refK (CH.getD j (0, 0, [])).2.2 (CH.getD j (0, 0, [])).2.2.length
          (CH.getD j (0, 0, [])).2.1 r) := by
      intro r hr
      rcases okRefK_sound hr with hm | ⟨hm1, hm2⟩
      · exact hS _ hm
      · by_cases hst : (CH.getD j (0, 0, [])).1 ≤ refK (CH.getD j (0, 0, [])).2.2
            (CH.getD j (0, 0, [])).2.2.length (CH.getD j (0, 0, [])).2.1 r
        · exact ih _ hm2 j hj ⟨hst, by have := hk.2; omega⟩ hS
        · obtain ⟨j', hj', hc, he⟩ := hB j hj _ hm1 (Nat.lt_of_not_le hst)
          refine ih _ hm2 j' hj' hc ?_
          rw [he]
          exact hS
    rcases h₂ with ⟨h₂, he⟩ | he
    · obtain ⟨g, hg, hgr⟩ := href r₁ h₁
      obtain ⟨g', hg', hgr'⟩ := href r₂ h₂
      exact ⟨g * g', H.mul_mem hg hg', by rw [he]; exact mRep_mulWK hgr hgr'⟩
    · obtain ⟨g, hg, hgr⟩ := href r₁ h₁
      exact ⟨g⁻¹, H.inv_mem hg, mRep_of_mulWK_one hgr he⟩

theorem nodeIn_all (H : Subgroup GL24) {TS : Nat → Nat} {CH : List (Nat × Nat × List Nat)}
    {WL : Nat → List Nat} {n₀ N : Nat} (hlay : layoutK CH WL n₀ N = true)
    (hch : ∀ j < CH.length, chunkK TS CH WL j = true) (hsb : seedsBelowK CH = true)
    (hseed : ∀ k < n₀, NodeIn H TS k) : ∀ k < N, NodeIn H TS k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkN
    by_cases hk : k < n₀
    · exact hseed k hk
    · obtain ⟨j, hj, hc⟩ := (layoutK_sound hlay).1 k (Nat.le_of_not_lt hk) hkN
      refine nodeIn_chunk H hlay hch k j hj hc fun s hs => ?_
      have h1 := seedsBelowK_sound hsb j hj s hs
      have h2 := hc.1
      have hsk : s < k := by omega
      exact ih s hsk (by omega)

end CFSG.KC.Co1Cl

end
