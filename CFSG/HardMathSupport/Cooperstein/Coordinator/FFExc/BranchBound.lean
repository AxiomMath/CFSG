module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

structure WGraph where
  nb : ℕ → ℕ
  wt : ℕ → ℕ

namespace WGraph

@[expose] def Indep (g : WGraph) (I : Finset ℕ) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, u ≠ v → (g.nb u).testBit v = false

@[expose] def grow (g : WGraph) : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, C, mx => (C, mx)
  | fuel + 1, cand, C, mx =>
    if cand = 0 then (C, mx) else
      grow g fuel (cand &&& g.nb cand.log2) (C ||| 2 ^ cand.log2) (max mx (g.wt cand.log2))

@[expose] def bound (g : WGraph) : ℕ → ℕ → Option ℕ
  | 0, mask => if mask = 0 then some 0 else none
  | fuel + 1, mask =>
    if mask = 0 then some 0 else
      let r := grow g 256 (mask &&& g.nb mask.log2) (2 ^ mask.log2) (g.wt mask.log2)
      (bound g fuel (mask ^^^ r.1)).map (· + r.2)

@[expose] def bnb (g : WGraph) (order : List ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, mask, budget =>
    if (match bound g 256 mask with | some b => decide (b ≤ budget) | none => false) then true
    else
      match order.find? (fun v => mask.testBit v) with
      | none => false
      | some v =>
        decide (g.wt v ≤ budget) &&
          bnb g order fuel (mask ^^^ (mask &&& (g.nb v ||| 2 ^ v))) (budget - g.wt v) &&
          bnb g order fuel (mask ^^^ 2 ^ v) budget

variable (g : WGraph)

structure GrowInv (mask C cand mx : ℕ) : Prop where
  Cmask : ∀ u, C.testBit u = true → mask.testBit u = true
  Cclq : ∀ u v, C.testBit u = true → C.testBit v = true → u ≠ v →
    (g.nb u).testBit v = true ∨ (g.nb v).testBit u = true
  candmask : ∀ c, cand.testBit c = true → mask.testBit c = true
  candnb : ∀ c, cand.testBit c = true → ∀ u, C.testBit u = true → (g.nb u).testBit c = true
  mxw : ∀ u, C.testBit u = true → g.wt u ≤ mx

theorem grow_spec (mask : ℕ) : ∀ (fuel cand C mx : ℕ), GrowInv g mask C cand mx →
    GrowInv g mask (g.grow fuel cand C mx).1 0 (g.grow fuel cand C mx).2 ∧
      ∀ u, C.testBit u = true → (g.grow fuel cand C mx).1.testBit u = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro cand C mx h
    exact ⟨⟨h.Cmask, h.Cclq, by simp, by simp, h.mxw⟩, fun u hu => hu⟩
  | succ n ih =>
    intro cand C mx h
    simp only [grow]
    split_ifs with hc
    · exact ⟨⟨h.Cmask, h.Cclq, by simp, by simp, h.mxw⟩, fun u hu => hu⟩
    · have hu : cand.testBit cand.log2 = true := Nat.testBit_log2 hc
      have hnew : GrowInv g mask (C ||| 2 ^ cand.log2) (cand &&& g.nb cand.log2)
          (max mx (g.wt cand.log2)) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro w hw
          rw [Nat.testBit_or, Nat.testBit_two_pow] at hw
          rcases Bool.or_eq_true_iff.1 hw with hw | hw
          · exact h.Cmask w hw
          · have := of_decide_eq_true hw
            rw [← this]; exact h.candmask _ hu
        · intro a b ha hb hab
          rw [Nat.testBit_or, Nat.testBit_two_pow] at ha hb
          rcases Bool.or_eq_true_iff.1 ha with ha | ha <;>
            rcases Bool.or_eq_true_iff.1 hb with hb | hb
          · exact h.Cclq a b ha hb hab
          · have := of_decide_eq_true hb
            subst this
            exact Or.inl (h.candnb _ hu a ha)
          · have := of_decide_eq_true ha
            subst this
            exact Or.inr (h.candnb _ hu b hb)
          · exact absurd ((of_decide_eq_true ha).symm.trans (of_decide_eq_true hb)) hab
        · intro c hc'
          rw [Nat.testBit_and] at hc'
          exact h.candmask c (Bool.and_eq_true_iff.1 hc').1
        · intro c hc' w hw
          rw [Nat.testBit_and] at hc'
          obtain ⟨hc1, hc2⟩ := Bool.and_eq_true_iff.1 hc'
          rw [Nat.testBit_or, Nat.testBit_two_pow] at hw
          rcases Bool.or_eq_true_iff.1 hw with hw | hw
          · exact h.candnb c hc1 w hw
          · have := of_decide_eq_true hw
            rw [← this]; exact hc2
        · intro w hw
          rw [Nat.testBit_or, Nat.testBit_two_pow] at hw
          rcases Bool.or_eq_true_iff.1 hw with hw | hw
          · exact (h.mxw w hw).trans (le_max_left _ _)
          · have := of_decide_eq_true hw
            rw [← this]; exact le_max_right _ _
      obtain ⟨h1, h2⟩ := ih _ _ _ hnew
      refine ⟨h1, fun w hw => h2 w ?_⟩
      rw [Nat.testBit_or, hw, Bool.true_or]

theorem bound_sound : ∀ (fuel mask b : ℕ), g.bound fuel mask = some b →
    ∀ I : Finset ℕ, (∀ v ∈ I, mask.testBit v = true) → g.Indep I → ∑ v ∈ I, g.wt v ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
    intro mask b hb I hI hind
    simp only [bound] at hb
    split_ifs at hb with hm
    · cases hb
      subst hm
      have : I = ∅ := Finset.eq_empty_of_forall_notMem fun v hv => by
        have := hI v hv
        simp at this
      simp [this]
  | succ n ih =>
    intro mask b hb I hI hind
    simp only [bound] at hb
    split_ifs at hb with hm
    · cases hb
      subst hm
      have : I = ∅ := Finset.eq_empty_of_forall_notMem fun v hv => by
        have := hI v hv
        simp at this
      simp [this]
    · set v := mask.log2 with hvdef
      have hv : mask.testBit v = true := Nat.testBit_log2 hm
      set r := g.grow 256 (mask &&& g.nb v) (2 ^ v) (g.wt v) with hr
      have hinit : GrowInv g mask (2 ^ v) (mask &&& g.nb v) (g.wt v) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro u hu
          rw [Nat.testBit_two_pow] at hu
          rw [← of_decide_eq_true hu]; exact hv
        · intro a b ha hb hab
          rw [Nat.testBit_two_pow] at ha hb
          exact absurd ((of_decide_eq_true ha).symm.trans (of_decide_eq_true hb)) hab
        · intro c hc
          rw [Nat.testBit_and] at hc
          exact (Bool.and_eq_true_iff.1 hc).1
        · intro c hc u hu
          rw [Nat.testBit_and] at hc
          rw [Nat.testBit_two_pow] at hu
          rw [← of_decide_eq_true hu]; exact (Bool.and_eq_true_iff.1 hc).2
        · intro u hu
          rw [Nat.testBit_two_pow] at hu
          rw [← of_decide_eq_true hu]
      obtain ⟨hspec, hmono⟩ := grow_spec g mask 256 _ _ _ hinit
      rw [← hr] at hspec hmono
      cases hbound : g.bound n (mask ^^^ r.1) with
      | none => rw [hbound] at hb; simp at hb
      | some b' =>
        rw [hbound] at hb
        simp only [Option.map_some, Option.some.injEq] at hb
        subst hb
        have hrest : ∑ w ∈ I.filter (fun w => ¬ r.1.testBit w = true), g.wt w ≤ b' := by
          refine ih _ b' hbound _ ?_ ?_
          · intro w hw
            rw [Finset.mem_filter] at hw
            rw [Nat.testBit_xor]
            have h1 := hI w hw.1
            have h2 : r.1.testBit w = false := by simpa using hw.2
            rw [h1, h2]; rfl
          · intro u hu w hw huw
            exact hind u (Finset.mem_filter.1 hu).1 w (Finset.mem_filter.1 hw).1 huw
        have hclq : ∑ w ∈ I.filter (fun w => r.1.testBit w = true), g.wt w ≤ r.2 := by
          set J := I.filter (fun w => r.1.testBit w = true) with hJ
          by_cases hJe : J = ∅
          · rw [hJe]; simp
          · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.2 hJe
            have hsing : J = {u} := by
              refine Finset.eq_singleton_iff_unique_mem.2 ⟨hu, fun w hw => ?_⟩
              by_contra hne
              have hwJ := Finset.mem_filter.1 hw
              have huJ := Finset.mem_filter.1 hu
              rcases hspec.Cclq w u hwJ.2 huJ.2 hne with h1 | h1
              · rw [hind w hwJ.1 u huJ.1 (Ne.symm (Ne.symm hne))] at h1
                exact Bool.false_ne_true h1
              · rw [hind u huJ.1 w hwJ.1 (Ne.symm hne)] at h1
                exact Bool.false_ne_true h1
            rw [hsing, Finset.sum_singleton]
            exact hspec.mxw u (Finset.mem_filter.1 hu).2
        rw [← Finset.sum_filter_add_sum_filter_not I (fun w => r.1.testBit w = true)]
        omega

theorem bnb_sound (order : List ℕ) : ∀ (fuel mask budget : ℕ), g.bnb order fuel mask budget = true →
    ∀ I : Finset ℕ, (∀ v ∈ I, mask.testBit v = true) → g.Indep I → ∑ v ∈ I, g.wt v ≤ budget := by
  intro fuel
  induction fuel with
  | zero => intro mask budget h; simp [bnb] at h
  | succ n ih =>
    intro mask budget h I hI hind
    simp only [bnb] at h
    split_ifs at h with hb
    · revert hb
      cases hbd : g.bound 256 mask with
      | none => simp
      | some b =>
        intro hb
        have hle : b ≤ budget := of_decide_eq_true hb
        exact (g.bound_sound 256 mask b hbd I hI hind).trans hle
    · revert h
      cases hfind : order.find? (fun v => mask.testBit v) with
      | none => simp
      | some v =>
        intro h
        have hvm : mask.testBit v = true := by
          have := List.find?_some hfind
          simpa using this
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hwv, hin⟩, hout⟩ := h
        by_cases hvI : v ∈ I
        · have hrec := ih _ _ hin (I.erase v) ?_ ?_
          · rw [← Finset.add_sum_erase I _ hvI]
            omega
          · intro w hw
            obtain ⟨hwv', hwI⟩ := Finset.mem_erase.1 hw
            rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow]
            have h1 := hI w hwI
            have h2 : (g.nb v).testBit w = false := hind v hvI w hwI (Ne.symm hwv')
            have h3 : decide (v = w) = false := by simp [Ne.symm hwv']
            rw [h1, h2, h3]; rfl
          · intro u hu w hw huw
            exact hind u (Finset.mem_of_mem_erase hu) w (Finset.mem_of_mem_erase hw) huw
        · refine ih _ _ hout I ?_ hind
          intro w hw
          rw [Nat.testBit_xor, Nat.testBit_two_pow]
          have h1 := hI w hw
          have h3 : decide (v = w) = false := by
            simp only [decide_eq_false_iff_not]
            rintro rfl
            exact hvI hw
          rw [h1, h3]; rfl

end WGraph

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
