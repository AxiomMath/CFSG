module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JC0
public import Mathlib.Data.Set.Card

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B.ZJFin

private theorem foldl_invariant {α β : Type*} (l : List α) (f : β → α → β) (P : β → Prop) :
    ∀ b₀, P b₀ → (∀ b a, a ∈ l → P b → P (f b a)) → P (l.foldl f b₀) := by
  induction l with
  | nil => intro b₀ h0 _; simpa using h0
  | cons a l ih =>
    intro b₀ h0 hstep
    rw [List.foldl_cons]
    exact ih (f b₀ a) (hstep b₀ a (by simp) h0)
      (fun b a' ha' hb => hstep b a' (by simp [ha']) hb)

private theorem stepAux_subset {gens : List Nat} {S : Set Nat}
    (hS : ∀ g ∈ gens, ∀ x ∈ S, mmul g x ∈ S) {x : Nat} (hx : x ∈ S) {st : List Nat × Nat}
    (hst : ∀ y ∈ st.1, y ∈ S) : ∀ y ∈ (stepAux gens x st).1, y ∈ S := by
  unfold stepAux
  refine foldl_invariant gens
    (fun st g => if st.2.testBit (mmul g x) then st
      else (mmul g x :: st.1, st.2 ||| (1 <<< mmul g x)))
    (fun st : List Nat × Nat => ∀ y ∈ st.1, y ∈ S) st hst ?_
  intro st g hg hst'
  split_ifs with h
  · exact hst'
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hS g hg x hx
    · exact hst' y hy

private theorem closAux_subset {gens : List Nat} {S : Set Nat}
    (hS : ∀ g ∈ gens, ∀ x ∈ S, mmul g x ∈ S) :
    ∀ n frontier all seen, (∀ y ∈ frontier, y ∈ S) → (∀ y ∈ all, y ∈ S) →
      ∀ y ∈ closAux gens n frontier all seen, y ∈ S := by
  intro n
  induction n with
  | zero => intro frontier all seen _ hall y hy; simpa [closAux] using hall y hy
  | succ n ih =>
    intro frontier all seen hfront hall y hy
    cases frontier with
    | nil => simpa [closAux] using hall y hy
    | cons x xs =>
      let r : List Nat × Nat := (x :: xs).foldl (fun st x => stepAux gens x st) ([], seen)
      have hr1 : ∀ z ∈ r.1, z ∈ S := by
        change ∀ z ∈ ((x :: xs).foldl (fun st x => stepAux gens x st) ([], seen)).1, z ∈ S
        refine foldl_invariant (x :: xs) (fun st x => stepAux gens x st)
          (fun st : List Nat × Nat => ∀ z ∈ st.1, z ∈ S) ([], seen) ?_ ?_
        · intro z hz; simp at hz
        · intro st g hg hst'
          exact stepAux_subset hS (hfront g hg) hst'
      have hrall : ∀ z ∈ r.1 ++ all, z ∈ S := by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hr1 z hz
        · exact hall z hz
      exact ih r.1 (r.1 ++ all) r.2 hr1 hrall y hy

theorem mem_clos {gens : List Nat} {S : Set Nat} (h1 : one ∈ S)
    (hS : ∀ g ∈ gens, ∀ x ∈ S, mmul g x ∈ S) : ∀ y ∈ clos gens, y ∈ S := by
  intro y hy
  refine closAux_subset hS 64 [one] [one] (1 <<< one) ?_ ?_ y ?_
  · intro z hz; rw [List.mem_singleton] at hz; rw [hz]; exact h1
  · intro z hz; rw [List.mem_singleton] at hz; rw [hz]; exact h1
  · exact hy

private theorem testBit_fold_or (l : List Nat) (c y : Nat) :
    (l.foldl (fun c x => c ||| (1 <<< x)) c).testBit y = (c.testBit y || decide (y ∈ l)) := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    have hyx : decide (a = y) = decide (y = a) := by simp [eq_comm]
    rw [hyx]
    simp only [List.mem_cons, Bool.decide_or]
    exact Bool.or_assoc (c.testBit y) (decide (y = a)) (decide (y ∈ l))

private theorem testBit_closSet (l : List Nat) (y : Nat) :
    (closSet l).testBit y = true ↔ y ∈ l := by
  change (l.foldl (fun c x => c ||| (1 <<< x)) 0).testBit y = true ↔ y ∈ l
  rw [testBit_fold_or]
  simp

theorem witness_sound {cl : List Nat} (h : witness cl = true) : Witness {x | x ∈ cl} := by
  simp only [witness] at h
  rw [Bool.or_eq_true_iff] at h
  rcases h with h | h
  · left
    rw [List.any_eq_true] at h
    obtain ⟨a, haC, ha⟩ := h
    rw [List.mem_filter] at haC
    obtain ⟨haCl, hacs⟩ := haC
    beta_reduce at ha
    simp only [Bool.and_eq_true_iff] at ha
    obtain ⟨⟨hane, ha2ne⟩, ha4⟩ := ha
    rw [bne_iff_ne] at hane ha2ne
    rw [beq_iff_eq] at ha4
    exact ⟨a, (testBit_closSet cl a).mp hacs, haCl, hane, ha2ne, ha4⟩
  · right
    rw [List.any_eq_true] at h
    obtain ⟨a, haI, hb⟩ := h
    beta_reduce at hb
    rw [List.any_eq_true] at hb
    obtain ⟨b, hbI, hab⟩ := hb
    beta_reduce at hab
    rw [List.mem_filter] at haI hbI
    obtain ⟨haC, hai⟩ := haI
    obtain ⟨hbC, hbi⟩ := hbI
    rw [List.mem_filter] at haC hbC
    obtain ⟨haCl, hacs⟩ := haC
    obtain ⟨hbCl, hbcs⟩ := hbC
    simp only [Bool.and_eq_true_iff] at hab
    obtain ⟨habne, habc⟩ := hab
    rw [bne_iff_ne] at habne
    rw [beq_iff_eq] at habc
    simp only [isInv, Bool.and_eq_true_iff] at hai hbi
    obtain ⟨hai1, hai2⟩ := hai
    obtain ⟨hbi1, hbi2⟩ := hbi
    rw [bne_iff_ne] at hai1 hbi1
    rw [beq_iff_eq] at hai2 hbi2
    exact ⟨a, (testBit_closSet cl a).mp hacs, b, (testBit_closSet cl b).mp hbcs,
      haCl, hbCl, hai1, hbi1, hai2, hbi2, habne, habc⟩

theorem Witness.mono {S S' : Set Nat} (hS : S ⊆ S') (h : Witness S) : Witness S' := by
  rcases h with ⟨a, haS, haCl, ha1, ha2, ha4⟩ |
    ⟨a, haS, b, hbS, haCl, hbCl, ha1, hb1, ha2, hb2, hab, habc⟩
  · exact Or.inl ⟨a, hS haS, haCl, ha1, ha2, ha4⟩
  · exact Or.inr ⟨a, hS haS, b, hS hbS, haCl, hbCl, ha1, hb1, ha2, hb2, hab, habc⟩

theorem ff1 {S : Set Nat} (hP : ∀ x ∈ S, x ∈ Plist) (h1 : one ∈ S)
    (hm : ∀ a ∈ S, ∀ b ∈ S, mmul a b ∈ S) (hT : T ∈ S) (hL : L ∈ S) (hR : R ∈ S)
    (hw : ¬ Witness S) (h8 : 8 ∣ S.ncard) : S = {x | x ∈ S48} := by
  have hgen3 : ∀ g ∈ [T, L, R], ∀ x ∈ S, mmul g x ∈ S := by
    intro g hg x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact hm T hT x hx
    · exact hm L hL x hx
    · exact hm R hR x hx
  have hH0 : ∀ x ∈ H0, x ∈ S := fun x hx => mem_clos h1 hgen3 x (H0_sub_clos x hx)
  have hrep : ∀ g ∈ S, g ∉ H0 →
      ∃ h ∈ H0, mmul g h ∈ repsNT ∧ mmul g h ∈ S48 ∧ g48 ∈ S := by
    intro g hg hgH0
    rcases coset_ok g (hP g hg) with hgH0' | ⟨h, hh, hhr⟩
    · exact absurd hgH0' hgH0
    · have hrS : mmul g h ∈ S := hm g hg h (hH0 h hh)
      have hgen4 : ∀ a ∈ [T, L, R, mmul g h], ∀ x ∈ S, mmul a x ∈ S := by
        intro a ha x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact hm T hT x hx
        · exact hm L hL x hx
        · exact hm R hR x hx
        · exact hm (mmul g h) hrS x hx
      rcases reps_ok (mmul g h) hhr with ⟨hr48, hg48c⟩ | hwit
      · exact ⟨h, hh, hhr, hr48, mem_clos h1 hgen4 g48 hg48c⟩
      · exfalso
        exact hw (Witness.mono (fun x hx => mem_clos h1 hgen4 x hx) (witness_sound hwit))
  by_cases hSH0 : ∀ x ∈ S, x ∈ H0
  · exfalso
    have hSeq : S = {x | x ∈ H0} := by
      apply Set.ext; intro x; exact ⟨fun hx => hSH0 x hx, fun hx => hH0 x hx⟩
    have hcard : S.ncard = 12 := by
      rw [hSeq, ← List.coe_toFinset H0, Set.ncard_coe_finset,
        List.toFinset_card_of_nodup H0_card.2, H0_card.1]
    have hnot : ¬ (8 ∣ 12) := by decide
    exact hnot (by simpa [hcard] using h8)
  · have hex : ∃ x, x ∈ S ∧ x ∉ H0 := by simpa [not_forall] using hSH0
    obtain ⟨g0, hg0, hg0H0⟩ := hex
    obtain ⟨_, _, _, _, hg48S⟩ := hrep g0 hg0 hg0H0
    have hgen4 : ∀ g ∈ [T, L, R, g48], ∀ x ∈ S, mmul g x ∈ S := by
      intro g hg x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact hm T hT x hx
      · exact hm L hL x hx
      · exact hm R hR x hx
      · exact hm g48 hg48S x hx
    have hS48sub : ∀ x ∈ S48, x ∈ S := fun x hx => mem_clos h1 hgen4 x (S48_sub_clos x hx)
    have hSsub : ∀ x ∈ S, x ∈ S48 := by
      intro g hg
      by_cases hgH0 : g ∈ H0
      · exact H0_sub_S48 g hgH0
      · obtain ⟨h, hh, _, hghS48, _⟩ := hrep g hg hgH0
        exact S48_cosets g (hP g hg) h hh hghS48
    exact Set.ext fun x => ⟨fun hx => hSsub x hx, fun hx => hS48sub x hx⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B.ZJFin
