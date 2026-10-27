module

public import Certificates.Data.Kernel.TitsDK
public import CFSG.Certificates.Kernel.TitsOctSound

public section

namespace CFSG.KC.TitsDSound

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TitsDK CFSG.KC.TitsOctSound
open CFSG.KC.TwoF4LieSound (bAnd_eq' strictB_eq')

variable {lp : ℕ → ℕ} {PL : ℕ}

theorem bNotD (c : Bool) : Bool.rec (motive := fun _ => Bool) true false c = !c := by
  cases c <;> rfl

theorem anyN_iffD {n : ℕ} {f : ℕ → Bool} : anyN n f = true ↔ ∃ i < n, f i = true := by
  unfold anyN
  rw [bIf_d]
  split
  · rename_i h
    rw [allN_iff'] at h
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro i hi hf
    have := h i hi
    rw [bIf_d, if_pos hf] at this
    exact Bool.false_ne_true this
  · rename_i h
    rw [allN_iff'] at h
    simp only [true_iff]
    push Not at h
    obtain ⟨i, hi, hf⟩ := h
    refine ⟨i, hi, ?_⟩
    rw [bIf_d] at hf
    cases e : f i <;> simp_all

theorem recR_sound {A : ℕ → ℕ} {k : ℕ} {isRoot : ℕ → Bool} {L cnt LAY ORD PR LB PS : ℕ}
    (h : recR lp A k isRoot L cnt LAY ORD PR LB PS = true) :
    (∀ i < cnt, fw 13 ORD i < 4680 ∧ (fw 4 LB i = 15 → isRoot (fw 13 ORD i) = true) ∧
      (fw 4 LB i ≠ 15 → fw 12 PR i < i ∧ fw 4 LB i < k ∧
        actV lp (gp (A (fw 4 LB i))) (fw 13 ORD (fw 12 PR i)) (fw 13 ORD i) = true)) ∧
    ∀ x < 4680, layAt LAY x = L → fw 13 PS x < cnt ∧ fw 13 ORD (fw 13 PS x) = x := by
  unfold recR at h
  simp only [bAnd_eq', Bool.and_eq_true, allN_iff', strictB_eq', blt_d, beq_d,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi => ?_, fun x hx hL => ?_⟩
  · obtain ⟨hx, h'⟩ := h1 i hi
    rw [bIf_d] at h'
    refine ⟨hx, fun hr => ?_, fun hr => ?_⟩
    · rwa [if_pos (decide_eq_true hr)] at h'
    · rw [if_neg (by simpa using hr)] at h'
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h'
  · have h' := h2 x hx
    rw [bIf_d, if_pos (decide_eq_true hL)] at h'
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using h'

theorem recR_reach {X V : Type*} [Group X] [MulAction X V] {c : ℕ → V} {a : ℕ → X} {S : Set X}
    {A : ℕ → ℕ} {k : ℕ} {isRoot : ℕ → Bool} {L cnt LAY ORD PR LB PS : ℕ}
    (ha : ∀ j < k, a j ∈ S)
    (hact : ∀ j < k, ∀ y x, y < 4680 → x < 4680 → actV lp (gp (A j)) y x = true →
      a j • c y = c x)
    (h : recR lp A k isRoot L cnt LAY ORD PR LB PS = true) :
    ∀ x < 4680, layAt LAY x = L →
      ∃ r, isRoot r = true ∧ ∃ g ∈ Subgroup.closure S, g • c r = c x := by
  obtain ⟨hst, hcov⟩ := recR_sound h
  have key : ∀ i < cnt, ∃ r, isRoot r = true ∧
      ∃ g ∈ Subgroup.closure S, g • c r = c (fw 13 ORD i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      obtain ⟨hlt, hroot, hstep⟩ := hst i hi
      by_cases hr : fw 4 LB i = 15
      · exact ⟨_, hroot hr, 1, Subgroup.one_mem _, one_smul _ _⟩
      · obtain ⟨hpi, hlb, hav⟩ := hstep hr
        obtain ⟨r, hr', g, hg, e⟩ := ih _ hpi (by omega)
        refine ⟨r, hr', a (fw 4 LB i) * g,
          Subgroup.mul_mem _ (Subgroup.subset_closure (ha _ hlb)) hg, ?_⟩
        rw [mul_smul, e]
        exact hact _ hlb _ _ (hst _ (by omega)).1 hlt hav
  intro x hx hL
  obtain ⟨hq, e⟩ := hcov x hx hL
  obtain ⟨r, hr, g, hg, e'⟩ := key _ hq
  exact ⟨r, hr, g, hg, by rw [e', e]⟩

theorem stabK_sound {E : ℕ → ℕ} {n a b : ℕ} (h : stabK lp PL E n a b = true) :
    (∀ i < n, actV lp (gp (E i)) a a = true ∧ actV lp (gp (E i)) b b = true) ∧
    ∀ k < degK a, ∃ i < n, actV lp (gp (E i)) (nbK lp PL a k) (nbK lp PL a k) = true ∧
      ∃ k' < degK a, actV lp (gp (E i)) (nbK lp PL a k') (nbK lp PL a k') = false := by
  unfold TitsDK.stabK at h
  simp only [bAnd_eq', bNotD, Bool.and_eq_true, allN_iff', anyN_iffD, Bool.not_eq_true'] at h
  exact h

theorem transK_sound {E : ℕ → ℕ} {n a w : ℕ} (h : transK lp PL E n a w = true) :
    ∀ k < degK a, ∃ i < n, actV lp (gp (E i)) w (nbK lp PL a k) = true := by
  unfold transK at h
  simp only [allN_iff', anyN_iffD] at h
  exact h

theorem exactK_sound {e w b k0 : ℕ} (h : exactK lp PL e w b k0 = true) :
    actV lp (gp e) w w = true ∧ k0 < degK b ∧
      ∀ k < degK b, (actV lp (gp e) (nbK lp PL b k) (nbK lp PL b k) = true ↔ k = k0) := by
  unfold exactK at h
  simp only [bAnd_eq', bNotD, Bool.and_eq_true, allN_iff', blt_d, beq_d, decide_eq_true_eq] at h
  obtain ⟨hw, hk0, h3⟩ := h
  refine ⟨hw, hk0, fun k hk => ?_⟩
  have h' := h3 k hk
  rw [bIf_d] at h'
  by_cases hkk : k = k0
  · rw [if_pos (decide_eq_true hkk)] at h'
    exact ⟨fun _ => hkk, fun _ => h'⟩
  · rw [if_neg (by simpa using hkk)] at h'
    simp only [Bool.not_eq_true'] at h'
    exact ⟨fun ha => absurd (ha.symm.trans h') (by decide), fun h'' => absurd h'' hkk⟩

theorem labK_sound {a : ℕ} {lab : ℕ → ℕ} (h : labK lp PL a lab = true) :
    degK a = 5 ∧ (∀ i < 5, ∀ j < i, lab i ≠ lab j) ∧
      (∀ i < 5, ∃ k < 5, lab i = nbK lp PL a k) ∧ ∀ k < 5, ∃ i < 5, lab i = nbK lp PL a k := by
  unfold labK at h
  simp only [bAnd_eq', bNotD, Bool.and_eq_true, allN_iff', anyN_iffD, beq_d, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem affK_sound {A : ℕ → ℕ} {k : ℕ} {lab : ℕ → ℕ} {AF : ℕ} (h : affK lp A k lab AF = true) :
    ∀ j < k, 0 < fw 3 AF (2 * j) ∧ fw 3 AF (2 * j) < 5 ∧ fw 3 AF (2 * j + 1) < 5 ∧
      ∀ i < 5, actV lp (gp (A j)) (lab i)
        (lab ((fw 3 AF (2 * j) * i + fw 3 AF (2 * j + 1)) % 5)) = true := by
  unfold affK at h
  simp only [allN_iff', strictB_eq', bAnd_eq', Bool.and_eq_true, blt_d, decide_eq_true_eq] at h
  intro j hj
  obtain ⟨h1, h2, h3, h4⟩ := h j hj
  exact ⟨h1, h2, h3, h4⟩

end CFSG.KC.TitsDSound

end
