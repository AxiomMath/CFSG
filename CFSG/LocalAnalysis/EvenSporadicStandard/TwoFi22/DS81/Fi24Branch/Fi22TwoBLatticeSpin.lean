module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBLatticeCheck
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {P : ℕ → Prop}

theorem reduce_nil (v : ℕ) : reduce [] v = v := rfl

theorem reduce_cons (b : ℕ) (B : List ℕ) (v : ℕ) :
    reduce (b :: B) v = reduce B (if v.testBit (lead b) then v ^^^ b else v) := rfl

theorem reduce_mem (hx : ∀ a b, P a → P b → P (a ^^^ b)) :
    ∀ (B : List ℕ), (∀ b ∈ B, P b) → ∀ v : ℕ, P v → P (reduce B v) := by
  intro B
  induction B with
  | nil => intro _ v hv; rwa [reduce_nil]
  | cons b B ih =>
    intro hB v hv
    rw [reduce_cons]
    have hb : P b := hB b (List.mem_cons_self ..)
    refine ih (fun b' hb' => hB b' (List.mem_cons_of_mem _ hb')) _ ?_
    split_ifs
    · exact hx _ _ hv hb
    · exact hv

theorem reduce_eq_zero (h0 : P 0) (hx : ∀ a b, P a → P b → P (a ^^^ b)) :
    ∀ (B : List ℕ), (∀ b ∈ B, P b) → ∀ v : ℕ, reduce B v = 0 → P v := by
  intro B
  induction B with
  | nil => intro _ v hv; rw [reduce_nil] at hv; exact hv ▸ h0
  | cons b B ih =>
    intro hB v hv
    rw [reduce_cons] at hv
    have hb : P b := hB b (List.mem_cons_self ..)
    have ih' := ih (fun b' hb' => hB b' (List.mem_cons_of_mem _ hb'))
    split_ifs at hv with hbit
    · have h1 : P (v ^^^ b) := ih' _ hv
      have e : v = (v ^^^ b) ^^^ b := by simp [Nat.xor_assoc]
      rw [e]
      exact hx _ _ h1 hb
    · exact ih' _ hv

theorem ins_mem {r : ℕ} (hr : P r) :
    ∀ {B : List ℕ}, (∀ b ∈ B, P b) → ∀ b ∈ ins r B, P b
  | [], _ => by
    intro b hb
    simp only [ins, List.mem_singleton] at hb
    exact hb ▸ hr
  | c :: B, hB => by
    intro b hb
    unfold ins at hb
    split_ifs at hb with hlt
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact hr
      · exact hB b hb
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact hB b (List.mem_cons_self ..)
      · exact ins_mem hr (fun b' hb' => hB b' (List.mem_cons_of_mem _ hb')) b hb

theorem addVec_mem (h0 : P 0) (hx : ∀ a b, P a → P b → P (a ^^^ b)) {B : List ℕ}
    (hB : ∀ b ∈ B, P b) {v : ℕ} (hv : P v) : ∀ b ∈ addVec B v, P b := by
  have hr : P (reduce B v) := reduce_mem hx B hB v hv
  unfold addVec
  dsimp only
  split_ifs with h
  · exact hB
  · exact ins_mem hr hB

theorem spinStep_mem {f g : ℕ → ℕ} (h0 : P 0) (hx : ∀ a b, P a → P b → P (a ^^^ b))
    (hf : ∀ c, P c → P (f c)) (hg : ∀ c, P c → P (g c)) {B : List ℕ} (hB : ∀ b ∈ B, P b) :
    ∀ b ∈ spinStep f g B, P b := by
  unfold spinStep
  have key : ∀ (L : List ℕ), (∀ b ∈ L, P b) → ∀ acc : List ℕ, (∀ b ∈ acc, P b) →
      ∀ b ∈ L.foldl (fun acc b => addVec (addVec acc (f b)) (g b)) acc, P b := by
    intro L
    induction L with
    | nil => intro _ acc hacc; simpa using hacc
    | cons c L ih =>
      intro hL acc hacc
      simp only [List.foldl_cons]
      have hc : P c := hL c (List.mem_cons_self ..)
      refine ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)) _ ?_
      exact addVec_mem h0 hx (addVec_mem h0 hx hacc (hf c hc)) (hg c hc)
  exact key B hB B hB

theorem spinBasis_mem {f g : ℕ → ℕ} (h0 : P 0) (hx : ∀ a b, P a → P b → P (a ^^^ b))
    (hf : ∀ c, P c → P (f c)) (hg : ∀ c, P c → P (g c)) {x : ℕ} (hxP : P x) :
    ∀ b ∈ spinBasis f g x, P b := by
  unfold spinBasis
  have key : ∀ (L : List ℕ) (acc : List ℕ), (∀ b ∈ acc, P b) →
      ∀ b ∈ L.foldl (fun B _ => spinStep f g B) acc, P b := by
    intro L
    induction L with
    | nil => intro acc hacc; simpa using hacc
    | cons c L ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      exact ih _ (spinStep_mem h0 hx hf hg hacc)
  exact key _ [x] (by simpa using hxP)

theorem spin_sound {f g : ℕ → ℕ} (h0 : P 0) (hx : ∀ a b, P a → P b → P (a ^^^ b))
    (hf : ∀ c, P c → P (f c)) (hg : ∀ c, P c → P (g c)) {x : ℕ} (hxP : P x) {y : ℕ}
    (hy : reduce (spinBasis f g x) y = 0) : P y :=
  reduce_eq_zero h0 hx _ (spinBasis_mem h0 hx hf hg hxP) _ hy

theorem spinCheck_spec {f g : ℕ → ℕ} {e m : ℕ} (h : spinCheck f g e m = true) :
    0 < e ∧ e < 1024 ∧ dotM m e = false ∧
      ∀ x < 1024, x ≠ 0 → x ≠ e → ∀ y < 1024, (dotM m x = true ∨ dotM m y = false) →
        reduce (spinBasis f g x) y = 0 := by
  unfold spinCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨he0, he1⟩, hem⟩, hall⟩ := h
  refine ⟨he0, he1, hem, fun x hx hx0 hxe y hy hcond => ?_⟩
  have h1 := allLt_spec hall hx
  simp only [Bool.or_eq_true, beq_iff_eq, hx0, hxe, false_or] at h1
  have h2 := allLt_spec h1 hy
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with h2 | ⟨h2, h3⟩
  · exact h2
  · rcases hcond with hc | hc
    · rw [hc] at h2
      exact absurd h2 (by simp)
    · rw [hc] at h3
      exact absurd h3 (by simp)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
