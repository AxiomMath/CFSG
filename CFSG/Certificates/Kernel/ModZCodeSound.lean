module

public import Certificates.Data.Kernel.ModZCode
public import CFSG.Certificates.Kernel.T10CodeSound
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2ModZData

public section

namespace CFSG.KC.ModZCode

open CFSG.KC.T10Code CFSG.OddStandard.AltStdSmall4.G2

theorem testBit_sqMask (mul : Nat → Nat → Nat) (N c : Nat) :
    (sqMask mul N).testBit c = true ↔ ∃ g < N, mul g g = c := by
  induction N with
  | zero => simp [sqMask]
  | succ N ih =>
    change (Nat.lor (sqMask mul N) (Nat.shiftLeft 1 (mul N N))).testBit c = true ↔ _
    rw [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, ih, Nat.shiftLeft_eq', Nat.one_shiftLeft,
      Nat.testBit_two_pow, decide_eq_true_iff]
    constructor
    · rintro (⟨g, hg, h⟩ | h)
      · exact ⟨g, by omega, h⟩
      · exact ⟨N, by omega, h⟩
    · rintro ⟨g, hg, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
      · exact Or.inl ⟨g, hg, h⟩
      · exact Or.inr h

theorem memN_spec {r : Nat} : ∀ {L : List Nat}, memN r L = true → r ∈ L
  | [], h => absurd h Bool.false_ne_true
  | a :: L, h => by
    change (Nat.beq a r || memN r L) = true at h
    rw [Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (memN_spec h)

theorem allF1_spec {mul : Nat → Nat → Nat} {K N e tc : Nat} :
    ∀ {W : List (Nat × Nat × Nat × Nat)}, allF1 mul K N e tc W = true →
      ∀ w ∈ W, F1 mul K N e tc w.1 w.2.1 w.2.2.1 w.2.2.2 = true
  | [], _, w, hw => absurd hw List.not_mem_nil
  | v :: W, h, w, hw => by
    change Bool.rec (motive := fun _ => Bool) false (allF1 mul K N e tc W)
      (F1 mul K N e tc v.1 v.2.1 v.2.2.1 v.2.2.2) = true at h
    cases hv : F1 mul K N e tc v.1 v.2.1 v.2.2.1 v.2.2.2
    · rw [hv] at h
      exact absurd h Bool.false_ne_true
    · rw [hv] at h
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hv
      · exact allF1_spec h w hw

theorem cntN_add (p : Nat → Bool) (a b : Nat) :
    cntN p (a + b) = cntN p a + cntN (fun i => p (a + i)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change Bool.rec (motive := fun _ => Nat) (cntN p (a + b)) (Nat.succ (cntN p (a + b)))
      (p (a + b)) = cntN p a + Bool.rec (motive := fun _ => Nat)
        (cntN (fun i => p (a + i)) b) (Nat.succ (cntN (fun i => p (a + i)) b)) (p (a + b))
    rw [ih]
    cases p (a + b) <;> rfl

theorem cntB_eq (p : Nat → Bool) (nb : Nat) : cntB p nb = cntN p (128 * nb) := by
  induction nb with
  | zero => rfl
  | succ nb ih =>
    change cntB p nb + cntN (fun i => p (128 * nb + i)) 128 = _
    rw [ih, Nat.mul_succ, cntN_add]

theorem cntB_K {K : Nat} (hK : K % 128 = 0) (p : Nat → Bool) : cntB p (Nat.div K 128) = cntN p K := by
  rw [cntB_eq]
  congr 1
  change 128 * (K / 128) = K
  omega

theorem all_of_blocks {p : Nat → Bool} {nb : Nat}
    (h : allR (fun b => allR p (Nat.mul 128 b) 128) 0 nb = true) : ∀ x < 128 * nb, p x = true := by
  intro x hx
  have hb := allR_spec h (x / 128) (by omega)
  have := allR_spec hb (x % 128) (Nat.mod_lt _ (by omega))
  rwa [Nat.zero_add, Nat.mul_eq, Nat.div_add_mod] at this

section Model

variable {α : Type} [Group α] [DecidableEq α] {K : Nat} {ofC : Nat → α} {mul : Nat → Nat → Nat}
  (hmul : ∀ m n, ofC (mul m n) = ofC m * ofC n) (hlt : ∀ m n, mul m n < K)
  (hinj : ∀ m < K, ∀ n < K, ofC m = ofC n → m = n) (hone : ofC 0 = 1)
include hmul hlt hinj hone

theorem beq_one_eq {c : Nat} (hc : c < K) : (ofC c == 1) = Nat.beq c 0 := by
  have hK : 0 < K := by have := hlt 0 0; omega
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq, ← hone]
  exact ⟨hinj c hc 0 hK, fun h => by rw [h]⟩

theorem beq_mul_one {c d : Nat} : (ofC c * ofC d == 1) = Nat.beq (mul c d) 0 := by
  rw [← hmul, beq_one_eq hmul hlt hinj hone (hlt c d)]

theorem commB_eq {g x : Nat} : ModZ.commB (ofC g) (ofC x) = commc mul g x := by
  rw [ModZ.commB, commc, ← hmul, ← hmul, Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  exact ⟨hinj _ (hlt g x) _ (hlt x g), fun h => by rw [h]⟩

theorem pow_eq (y e : Nat) : ofC (powC mul y e) = ofC y ^ e := by
  induction e with
  | zero => exact hone.trans (pow_zero _).symm
  | succ e ih =>
    change ofC (mul (powC mul y e) y) = _
    rw [hmul, ih, pow_succ]

theorem powC_lt (y e : Nat) : powC mul y e < K := by
  cases e with
  | zero => have := hlt 0 0; change 0 < K; omega
  | succ e => exact hlt _ _

omit hmul hlt hinj hone in
theorem length_filter (p : α → Bool) :
    (((List.range K).map ofC).filter p).length = cntN (fun g => p (ofC g)) K := by
  rw [cntN_eq, List.filter_map, List.length_map]
  rfl

theorem checkE_of (hK : K % 128 = 0) (inE : α → Bool) (inEc : Nat → Bool)
    (hE : ∀ x < K, inE (ofC x) = inEc x)
    (SQ N : Nat) (hSQ : SQ = sqMask mul K) (h : ∀ x < K, FE mul K inEc SQ N x = true) :
    ModZ.checkE ((List.range K).map ofC) inE N = true := by
  simp only [ModZ.checkE, List.all_eq_true]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  have hx := List.mem_range.1 hx
  have hS : (((List.range K).map ofC).map fun g => g * g).contains (ofC x) = tb SQ x := by
    rw [Bool.eq_iff_iff, List.contains_iff, List.map_map, List.mem_map, tb_eq, hSQ,
      testBit_sqMask]
    constructor
    · rintro ⟨g, hg, he⟩
      refine ⟨g, List.mem_range.1 hg, hinj _ (hlt g g) _ hx ?_⟩
      rw [hmul]
      exact he
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, List.mem_range.2 hg, by simp only [Function.comp_apply, hmul]⟩
  have hC : (((List.range K).map ofC).filter fun g => ModZ.commB g (ofC x)).length =
      cntN (fun g => commc mul g x) K := by
    rw [length_filter]
    exact cntN_congr fun g _ => commB_eq hmul hlt hinj hone
  have hd : ∀ a b : Nat, decide (a ≤ b) = Nat.ble a b := fun a b => by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.ble_eq]
  have := h x hx
  rw [FE, cntB_K hK] at this
  rw [hE x hx, beq_one_eq hmul hlt hinj hone hx, beq_mul_one hmul hlt hinj hone, hS, hC, hd]
  exact this

theorem checkC_of (hK : K % 128 = 0) (code : α → Nat) (inM inA : α → Bool) (inMc inAc : Nat → Bool)
    (hM : ∀ x < K, inM (ofC x) = inMc x) (hA : ∀ x < K, inA (ofC x) = inAc x)
    (tc N e : Nat) (htc : tc < K) (W : List (Nat × Nat × Nat × Nat)) (Rc : List Nat)
    (hR : Rc = W.map Prod.fst) (h1 : allF1 mul K N e tc W = true) (wr wg wh : Nat → Nat)
    (h2 : ∀ x < K, F2 mul K inMc inAc Rc wr wg wh x = true) :
    ModZ.checkC ((List.range K).map ofC) code inM inA (ofC tc) N e (Rc.map ofC) = true := by
  have hinv : ∀ g h : Nat, Nat.beq (mul g h) 0 = true → ofC h = (ofC g)⁻¹ := fun g h hgh => by
    have := congrArg ofC (Nat.eq_of_beq_eq_true hgh)
    rw [hmul, hone] at this
    exact eq_inv_of_mul_eq_one_right this
  simp only [ModZ.checkC, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro r hr
    obtain ⟨rc, hrc, rfl⟩ := List.mem_map.1 hr
    rw [hR] at hrc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hrc
    have hF := allF1_spec h1 w hw
    simp only [F1, cntB_K hK, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at hF
    rw [Bool.or_eq_true, Bool.or_eq_true]
    rcases hF with (hF | ⟨⟨hy, hyr⟩, hye⟩) | ⟨⟨hg, hgh⟩, hgt⟩
    · refine Or.inl (Or.inl ?_)
      rw [length_filter, cntN_congr fun g _ => commB_eq hmul hlt hinj hone]
      exact bne_iff_ne.2 (Nat.ne_of_beq_eq_false (by simpa using hF))
    · refine Or.inl (Or.inr (List.any_eq_true.2 ⟨ofC w.2.1, List.mem_filter.2
        ⟨List.mem_map.2 ⟨w.2.1, List.mem_range.2 hy, rfl⟩, by rw [commB_eq hmul hlt hinj hone]; exact hyr⟩, ?_⟩))
      rw [← pow_eq hmul hlt hinj hone, bne, beq_one_eq hmul hlt hinj hone (powC_lt hmul hlt hinj hone _ _)]
      exact hye
    · refine Or.inr (List.any_eq_true.2 ⟨(ofC w.2.2.1, (ofC w.2.2.1)⁻¹),
        List.mem_map.2 ⟨ofC w.2.2.1, List.mem_map.2 ⟨w.2.2.1, List.mem_range.2 hg, rfl⟩, rfl⟩, ?_⟩)
      rw [← hinv _ _ hgh, ← hmul, ← hmul, commB_eq hmul hlt hinj hone]
      exact hgt
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have hx := List.mem_range.1 hx
    have hF := h2 x hx
    simp only [F2, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at hF
    rw [hM x hx, hA x hx, beq_mul_one hmul hlt hinj hone, Bool.or_eq_true, Bool.or_eq_true,
      Bool.or_eq_true]
    rcases hF with hF | ⟨⟨⟨hr, hg⟩, hgh⟩, hc⟩
    · exact Or.inl hF
    · refine Or.inr (List.any_eq_true.2 ⟨ModZ.conjCodes (((List.range K).map ofC).map
        fun g => (g, g⁻¹)) code (ofC (wr x)), List.mem_map.2 ⟨ofC (wr x),
        List.mem_map.2 ⟨wr x, memN_spec hr, rfl⟩, rfl⟩, ?_⟩)
      rw [List.contains_iff, ModZ.conjCodes, List.mem_map]
      refine ⟨(ofC (wg x), (ofC (wg x))⁻¹), List.mem_map.2 ⟨ofC (wg x),
        List.mem_map.2 ⟨wg x, List.mem_range.2 hg, rfl⟩, rfl⟩, ?_⟩
      rw [← hinv _ _ hgh, ← hmul, ← hmul, Nat.eq_of_beq_eq_true hc]

end Model

end CFSG.KC.ModZCode
