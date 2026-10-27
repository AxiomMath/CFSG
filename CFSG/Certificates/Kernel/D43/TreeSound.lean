module

public import Certificates.Data.Kernel.D43.Tree
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.D43

variable {G : Type*} [Group G] [MulAction G (Fin 26572)]

@[expose] noncomputable def dG (γ : ℕ → G) (d : ℕ) : G :=
  if 1 ≤ d ∧ d ≤ 8 then γ (d - 1) else if 9 ≤ d ∧ d ≤ 16 then (γ (d - 9))⁻¹ else 1

@[expose] noncomputable def wG (γ : ℕ → G) : ℕ → ℕ → G
  | 0, _ => 1
  | f + 1, w => if w = 0 then 1 else wG γ f (w / 32) * dG γ (w % 32)

@[expose] def TabRep (F : ℕ → ℕ) (γ : ℕ → G) : Prop :=
  ∀ k < 8, ∀ p : Fin 26572, ((γ k • p : Fin 26572) : ℕ) = tabAt F k p

@[expose] noncomputable def lG (γ : ℕ → G) (W : ℕ → ℕ) (j : ℕ) : G := wG γ 24 (W j)

@[expose] noncomputable def maskGroup (γ : ℕ → G) (W : ℕ → ℕ) (M : ℕ) : Subgroup G :=
  Subgroup.closure {x | ∃ j, M.testBit j = true ∧ x = lG γ W j}

theorem tree_bAnd {a c : Bool} (h : Bool.rec (motive := fun _ => Bool) false c a = true) :
    a = true ∧ c = true := by
  cases a <;> simp_all

theorem tree_strictN (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Enum.strictN y k = k y := by
  cases y <;> rfl

theorem tree_strictB (y : ℕ) (k : ℕ → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem tree_allBlk {b : ℕ} {f : ℕ → Bool} :
    ∀ {len : ℕ}, CFSG.KC.Enum.allBlk b f len = true → ∀ l < len, f (b + l) = true
  | 0, _ => fun l hl => absurd hl (Nat.not_lt_zero l)
  | len + 1, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (CFSG.KC.Enum.allBlk b f len)
        (f (Nat.add b len)) = true := h
    obtain ⟨h1, h2⟩ := tree_bAnd h'
    intro l hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
    · exact tree_allBlk h2 l hl
    · exact h1

theorem tree_testBit {M j : ℕ} : Nat.land (Nat.shiftRight M j) 1 = 1 ↔ M.testBit j = true := by
  change (M >>> j) &&& 1 = 1 ↔ _
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  simp

theorem wAp_ge (F : ℕ → ℕ) : ∀ (f w p : ℕ), 26572 ≤ p → 26572 ≤ wAp F f w p
  | 0, _, _, hp => hp
  | f + 1, w, p, hp => by
    have hg : gAp F (Nat.land w 31) p = 65535 := by
      unfold gAp
      rcases hb : Nat.blt p (nat_lit 26572) with _ | _
      · rfl
      · have hb' : p + 1 ≤ 26572 := Nat.le_of_ble_eq_true hb
        omega
    change Bool.rec (motive := fun _ => ℕ) (CFSG.KC.Enum.strictN (gAp F (Nat.land w 31) p)
      fun q => wAp F f (Nat.shiftRight w 5) q) p (Nat.beq w 0) ≥ 26572
    cases Nat.beq w 0
    · change CFSG.KC.Enum.strictN _ _ ≥ 26572
      rw [tree_strictN, hg]
      exact wAp_ge F f _ _ (by decide)
    · exact hp

theorem gAp_spec {F : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ) (d : ℕ) (p : Fin 26572)
    (h : gAp F d p < 26572) : gAp F d p = ((dG γ d • p : Fin 26572) : ℕ) := by
  have hT : ∀ k < 8, ∀ x : Fin 26572, tabAt F k x = ((γ k • x : Fin 26572) : ℕ) :=
    fun k hk x => (hγ k hk x).symm
  have hb : Nat.blt (p : ℕ) (nat_lit 26572) = true := Nat.blt_eq.mpr p.isLt
  unfold gAp at h ⊢
  rw [hb] at h ⊢
  dsimp only at h ⊢
  unfold dG
  revert h
  rcases h0 : Nat.beq d (nat_lit 0) with _ | _
  · have hd0 : d ≠ 0 := Nat.ne_of_beq_eq_false h0
    dsimp only
    rcases h8 : Nat.ble d (nat_lit 8) with _ | _
    · have hd8 : ¬ d ≤ 8 := fun e => Bool.noConfusion ((Nat.ble_eq_true_of_le e).symm.trans h8)
      dsimp only
      rw [if_neg (by omega)]
      rcases h16 : Nat.ble d (nat_lit 16) with _ | _
      · have hd16 : ¬ d ≤ 16 := fun e => Bool.noConfusion ((Nat.ble_eq_true_of_le e).symm.trans h16)
        intro _
        dsimp only
        rw [if_neg (by omega), one_smul]
      · have hd16 : d ≤ 16 := Nat.le_of_ble_eq_true h16
        dsimp only
        rw [if_pos ⟨by omega, hd16⟩]
        simp only [tree_strictN]
        have e9 : Nat.sub d (nat_lit 9) = d - 9 := rfl
        rw [e9]
        have hk : d - 9 < 8 := by omega
        rw [hT _ hk p, hT _ hk (γ (d - 9) • p), hT _ hk (γ (d - 9) • γ (d - 9) • p)]
        rcases he : Nat.beq ((γ (d - 9) • γ (d - 9) • γ (d - 9) • p : Fin 26572) : ℕ) p with _ | _
        · intro h
          dsimp only at h
          omega
        · intro _
          have he' : γ (d - 9) • (γ (d - 9) • γ (d - 9) • p) = p :=
            Fin.ext (Nat.eq_of_beq_eq_true he)
          dsimp only
          congr 1
          exact (eq_inv_smul_iff).2 he'
    · have hd8 : d ≤ 8 := Nat.le_of_ble_eq_true h8
      intro _
      dsimp only
      rw [if_pos ⟨by omega, hd8⟩]
      have e1 : Nat.sub d (nat_lit 1) = d - 1 := rfl
      rw [e1]
      exact hT _ (by omega) p
  · have hd0 : d = 0 := Nat.eq_of_beq_eq_true h0
    intro _
    subst hd0
    simp

theorem wAp_spec {F : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ) :
    ∀ (f w : ℕ) (p : Fin 26572), wAp F f w p < 26572 → wAp F f w p = ((wG γ f w • p : Fin 26572) : ℕ)
  | 0, w, p, _ => by
    change (p : ℕ) = ((wG γ 0 w • p : Fin 26572) : ℕ)
    rw [wG, one_smul]
  | f + 1, w, p, h => by
    change Bool.rec (motive := fun _ => ℕ) (CFSG.KC.Enum.strictN (gAp F (Nat.land w 31) p)
      fun q => wAp F f (Nat.shiftRight w 5) q) p (Nat.beq w 0) < 26572 at h
    change Bool.rec (motive := fun _ => ℕ) (CFSG.KC.Enum.strictN (gAp F (Nat.land w 31) p)
      fun q => wAp F f (Nat.shiftRight w 5) q) p (Nat.beq w 0) = _
    rw [wG]
    revert h
    rcases hw : Nat.beq w 0 with _ | _
    · have hw0 : w ≠ 0 := Nat.ne_of_beq_eq_false hw
      intro h
      dsimp only at h ⊢
      rw [tree_strictN] at h ⊢
      rw [if_neg hw0]
      have h31 : Nat.land w 31 = w % 32 := Nat.and_two_pow_sub_one_eq_mod w 5
      have h5 : Nat.shiftRight w 5 = w / 32 := Nat.shiftRight_eq_div_pow w 5
      rw [h31, h5] at h ⊢
      have hq : gAp F (w % 32) p < 26572 := by
        by_contra hc
        exact absurd h (Nat.not_lt.2 (wAp_ge F f _ _ (Nat.not_lt.1 hc)))
      have hg := gAp_spec hγ (w % 32) p hq
      have hp' : (⟨gAp F (w % 32) p, hq⟩ : Fin 26572) = dG γ (w % 32) • p := Fin.ext hg
      have ih := wAp_spec hγ f (w / 32) ⟨gAp F (w % 32) p, hq⟩ h
      exact ih.trans (by rw [hp', mul_smul])
    · have hw0 : w = 0 := Nat.eq_of_beq_eq_true hw
      intro _
      dsimp only
      rw [if_pos hw0, one_smul]

theorem lAp_spec {F W : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ) {j : ℕ} {p : Fin 26572}
    (h : lAp F W j p < 26572) : lAp F W j p = ((lG γ W j • p : Fin 26572) : ℕ) :=
  wAp_spec hγ 24 (W j) p h

theorem fixAll_spec {F W : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ) {B i lo M : ℕ}
    (h : fixAll F W B i lo M = true) {j : ℕ} (hj : j < 17) (hM : M.testBit j = true) :
    lo ≤ j ∧ ∀ u < i, ∀ hb : bAt B u < 26572,
      lG γ W j • (⟨bAt B u, hb⟩ : Fin 26572) = ⟨bAt B u, hb⟩ := by
  unfold fixAll at h
  have hc := tree_allBlk h j hj
  rw [Nat.zero_add] at hc
  unfold fixChk at hc
  rw [tree_strictB] at hc
  beta_reduce at hc
  have h1 : Nat.land (Nat.shiftRight M j) (nat_lit 1) = 1 := tree_testBit.2 hM
  rw [h1] at hc
  revert hc
  rcases hl : Nat.ble lo j with _ | _ <;> rcases hf : fixesB F W B i j with _ | _ <;> intro hc <;>
    first | exact absurd hc (by decide) | skip
  refine ⟨Nat.le_of_ble_eq_true hl, fun u hu hbu => ?_⟩
  have hfu := tree_allBlk hf u hu
  beta_reduce at hfu
  rw [tree_strictB] at hfu
  beta_reduce at hfu
  rw [Nat.zero_add] at hfu
  have e := Nat.eq_of_beq_eq_true hfu
  have hl' : lAp F W j (⟨bAt B u, hbu⟩ : Fin 26572) < 26572 := by
    change lAp F W j (bAt B u) < 26572
    rw [e]
    exact hbu
  have hs := lAp_spec hγ hl'
  apply Fin.ext
  rw [← hs]
  exact e

theorem treeChk_facts {F W R Q : ℕ → ℕ} {ℓ o b M t : ℕ} (h : treeChk F W R Q ℓ o b M t = true) :
    ptAt R o t < 26572 ∧ posAt Q ℓ (ptAt R o t) = t ∧ (t = 0 → ptAt R o t = b) ∧
      (t ≠ 0 → ∃ par lab, par < t ∧ M.testBit lab = true ∧
        lAp F W lab (ptAt R o par) = ptAt R o t) := by
  unfold treeChk at h
  rw [tree_strictB] at h
  beta_reduce at h
  rw [tree_strictB] at h
  beta_reduce at h
  obtain ⟨h1, h2⟩ := tree_bAnd h
  obtain ⟨h2, h3⟩ := tree_bAnd h2
  have hpt : ptAt R o t < 26572 := Nat.le_of_ble_eq_true h1
  have hpos : posAt Q ℓ (ptAt R o t) = t := Nat.eq_of_beq_eq_true h2
  refine ⟨hpt, hpos, fun ht => ?_, fun ht => ?_⟩
  · subst ht
    have h3' : Nat.beq (ptAt R o 0) b = true := h3
    exact Nat.eq_of_beq_eq_true h3'
  · have hb0 : Nat.beq t (nat_lit 0) = false := by
      rcases hz : Nat.beq t (nat_lit 0) with _ | _
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hz) ht
    rw [hb0] at h3
    dsimp only at h3
    rw [tree_strictB] at h3
    beta_reduce at h3
    rw [tree_strictB] at h3
    beta_reduce at h3
    obtain ⟨h4, h5⟩ := tree_bAnd h3
    obtain ⟨h5, h6⟩ := tree_bAnd h5
    have h4' : Nat.land (Nat.shiftRight (recAt R o t) 15) 32767 < t := Nat.le_of_ble_eq_true h4
    exact ⟨_, Nat.shiftRight (recAt R o t) 30, h4', tree_testBit.1 (Nat.eq_of_beq_eq_true h5),
      Nat.eq_of_beq_eq_true h6⟩

theorem treeChunks_spec {F W R Q : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ)
    {ℓ o s b M C : ℕ} (hs : s ≤ 256 * C) (hb : b < 26572)
    (h : ∀ c < C, treeChunk F W R Q ℓ o s b M c = true) :
    (∀ t < s, ptAt R o t < 26572) ∧
      (∀ t < s, ∀ t' < s, ptAt R o t = ptAt R o t' → t = t') ∧
      ∀ t < s, ∃ g ∈ maskGroup γ W M, ((g • (⟨b, hb⟩ : Fin 26572) : Fin 26572) : ℕ) = ptAt R o t := by
  have hall : ∀ t < s, treeChk F W R Q ℓ o b M t = true := by
    intro t ht
    have hc := tree_allBlk (h (t / 256) (by omega)) (t % 256) (Nat.mod_lt t (by decide))
    beta_reduce at hc
    have e : Nat.mul (nat_lit 256) (t / 256) + t % 256 = t := Nat.div_add_mod t 256
    rw [e] at hc
    have hts : Nat.blt t s = true := Nat.blt_eq.mpr ht
    rw [hts] at hc
    exact hc
  refine ⟨fun t ht => (treeChk_facts (hall t ht)).1, fun t ht t' ht' e => ?_, fun t ht => ?_⟩
  · calc t = posAt Q ℓ (ptAt R o t) := (treeChk_facts (hall t ht)).2.1.symm
      _ = posAt Q ℓ (ptAt R o t') := by rw [e]
      _ = t' := (treeChk_facts (hall t' ht')).2.1
  · induction t using Nat.strong_induction_on with
    | _ t ih =>
    obtain ⟨hpt, -, h0, hpar⟩ := treeChk_facts (hall t ht)
    by_cases ht0 : t = 0
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [one_smul]
      exact (h0 ht0).symm
    · obtain ⟨par, lab, hpl, hbit, hlap⟩ := hpar ht0
      obtain ⟨g', hg', hg'b⟩ := ih par hpl (by omega)
      have hpp : ptAt R o par < 26572 := (treeChk_facts (hall par (by omega))).1
      have hl : lAp F W lab (⟨ptAt R o par, hpp⟩ : Fin 26572) < 26572 := by
        change lAp F W lab (ptAt R o par) < 26572
        rw [hlap]
        exact hpt
      have hs := lAp_spec hγ hl
      have hfin : (⟨ptAt R o par, hpp⟩ : Fin 26572) = g' • ⟨b, hb⟩ := Fin.ext hg'b.symm
      refine ⟨lG γ W lab * g', Subgroup.mul_mem _ (Subgroup.subset_closure ⟨lab, hbit, rfl⟩) hg', ?_⟩
      rw [mul_smul, ← hfin, ← hs]
      exact hlap

end CFSG.KC.D43

end
