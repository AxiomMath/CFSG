module

public import Certificates.Data.Kernel.Fi22Gen.Defs
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option maxRecDepth 4000

namespace CFSG.KS.Fi22Gen

open CFSG.KC.Enum CFSG.KS CFSG.KS.Fi22L
open scoped Pointwise

theorem ulK_spec {UL : List Nat} (h : ulK UL = true) :
    UL.length = 22 ∧ (∀ i < 21, gD UL i < gD UL (i + 1)) ∧ gD UL 21 < 3510 := by
  unfold ulK at h
  simp only [bAnd_iff, Raw.Orb.allN_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1, fun i hi => h.2.1 i hi, h.2.2⟩

theorem lettersLt_spec {m : Nat} {w : List Nat} (h : lettersLt m w = true) : ∀ l ∈ w, l < m := by
  intro l hl
  unfold lettersLt at h
  exact Nat.blt_eq.mp (List.all_eq_true.1 h l hl)

theorem treeK_spec {UL gw : List Nat} {N root KP PL PI : Nat}
    (h : treeK UL gw N root KP PL PI = true) :
    ulK UL = true ∧ (∀ l ∈ gw, l < 32) ∧ wAp LT gw (gD UL 0) = 0 ∧ root < N ∧
    (∀ k, k + 1 < N → rKey KP k < rKey KP (k + 1)) ∧
    ∀ k < N, (∀ i < 21, rPt KP k i < rPt KP k (i + 1)) ∧ rPt KP k 21 < 3510 ∧
      (k = root → rDep PL k = 0 ∧
        ∀ i < 22, rPi PI k i < 22 ∧ rPt KP k i = wAp LT gw (gD UL (rPi PI k i))) ∧
      (k ≠ root → rPar PL k < N ∧ rDep PL k = rDep PL (rPar PL k) + 1 ∧ rLab PL k < 32 ∧
        LT (rLab PL k) 0 = 0 ∧ ∀ i < 22, rPi PI k i < 22 ∧
          rPt KP k i = LT (rLab PL k) (rPt KP (rPar PL k) (rPi PI k i))) := by
  unfold treeK headK at h
  rw [bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff] at h
  obtain ⟨⟨hu, hg, h0, hr, hk⟩, hrows⟩ := h
  refine ⟨hu, lettersLt_spec hg, Nat.beq_eq.mp h0, Nat.blt_eq.mp hr, ?_, ?_⟩
  · intro k hk1
    unfold keysK at hk
    exact Nat.blt_eq.mp (Raw.Orb.allN_iff.1 hk k (by change k < N - 1; omega))
  · intro k hkN
    unfold rowsK at hrows
    have hk := Raw.Orb.allN_iff.1 hrows k hkN
    rw [Nat.add_eq, Nat.zero_add] at hk
    unfold rowK ptsK at hk
    rw [bAnd_iff, bAnd_iff, Raw.Orb.bIf_eq] at hk
    obtain ⟨⟨hinc, hlast⟩, hrest⟩ := hk
    refine ⟨fun i hi => Nat.blt_eq.mp (Raw.Orb.allN_iff.1 hinc i hi), Nat.blt_eq.mp hlast, ?_, ?_⟩
    · intro hkr
      have hb : Nat.beq k root = true := Nat.beq_eq.mpr hkr
      rw [if_pos hb] at hrest
      unfold rootK at hrest
      rw [bAnd_iff] at hrest
      refine ⟨Nat.beq_eq.mp hrest.1, fun i hi => ?_⟩
      have hi' := Raw.Orb.allN_iff.1 hrest.2 i hi
      rw [Raw.Orb.strictB_eq, bAnd_iff, Nat.blt_eq, Nat.beq_eq] at hi'
      exact hi'
    · intro hkr
      have hb : Nat.beq k root = false := by
        cases e : Nat.beq k root
        · rfl
        · exact absurd (Nat.beq_eq.mp e) hkr
      rw [if_neg (by rw [hb]; decide)] at hrest
      unfold edgeK at hrest
      rw [Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff,
        Nat.blt_eq, Nat.beq_eq, Nat.blt_eq, Nat.beq_eq] at hrest
      obtain ⟨hp, hd, hl, h0, hall⟩ := hrest
      refine ⟨hp, hd, hl, h0, fun i hi => ?_⟩
      have hi' := Raw.Orb.allN_iff.1 hall i hi
      rw [Raw.Orb.strictB_eq, bAnd_iff, Nat.blt_eq, Nat.beq_eq] at hi'
      exact hi'

theorem itP_eq (f : Nat → Nat) : ∀ (o x : Nat), itP f o x = f^[o] x
  | 0, _ => rfl
  | o + 1, x => by
    change strictN (f x) (itP f o) = f^[o + 1] x
    rw [Raw.Orb.strictN_eq, itP_eq f o, Function.iterate_succ_apply]

theorem ordK_spec {w1 w2 : List Nat} (h : ordK w1 w2 = true) :
    (∀ l ∈ w1, l < 2) ∧ (∀ l ∈ w2, l < 2) ∧
      ∀ b < 5, (wAp AB w1)^[5] (BS b) = BS b ∧ (wAp AB w2)^[14] (BS b) = BS b := by
  unfold ordK at h
  rw [bAnd_iff, bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨lettersLt_spec h1, lettersLt_spec h2, fun b hb => ?_⟩
  have hb' := Raw.Orb.allN_iff.1 h3 b hb
  rw [Raw.Orb.strictB_eq, bAnd_iff, Nat.beq_eq, Nat.beq_eq, itP_eq, itP_eq] at hb'
  exact hb'

theorem traceK_spec {UL w1 w2 p1 p2 : List Nat} (h : traceK UL w1 w2 p1 p2 = true) :
    ∀ i < 22, gD p1 i < 22 ∧ gD p2 i < 22 ∧ wAp AB w1 (gD UL i) = gD UL (gD p1 i) ∧
      wAp AB w2 (wAp AB w2 (gD UL i)) = gD UL (gD p2 i) := by
  intro i hi
  unfold traceK at h
  have hi' := Raw.Orb.allN_iff.1 h i hi
  rw [Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, bAnd_iff, bAnd_iff, bAnd_iff,
    Nat.blt_eq, Nat.blt_eq, Nat.beq_eq, Nat.beq_eq] at hi'
  exact hi'

theorem PP_eq (p1 p2 : List Nat) (c j : Nat) : PP p1 p2 c j = if c = 0 then gD p1 j else gD p2 j := by
  unfold PP
  rw [Raw.Orb.nIf_eq]
  by_cases hc : c = 0
  · rw [if_pos (Nat.beq_eq.mpr hc), if_pos hc]
  · rw [if_neg (by intro e; exact hc (Nat.beq_eq.mp e)), if_neg hc]

theorem levelK_spec {p1 p2 : List Nat} {W : List (List Nat)} {O P G : List Nat} {i : Nat}
    (h : levelK p1 p2 W O P G i = true) :
    (∀ w ∈ W, ∀ l ∈ w, l < 2) ∧ (∀ w ∈ W, ∀ j < i, wAp (PP p1 p2) w j = j) ∧
      gD O 0 = i ∧ (∀ a < lvS i, gD O a < 22) ∧
      (∀ a < lvS i, ∀ b < a, gD O a ≠ gD O b) ∧
      ∀ a, 0 < a → a < lvS i → gD P a < a ∧ gD G a < W.length ∧
        gD O a = wAp (PP p1 p2) (W.getD (gD G a) []) (gD O (gD P a)) := by
  unfold levelK at h
  rw [Raw.Orb.strictB_eq] at h
  simp only [bAnd_iff] at h
  obtain ⟨hw, hfix, -, -, -, h0, hlt, hne, htree⟩ := h
  refine ⟨fun w hw' => lettersLt_spec (List.all_eq_true.1 hw w hw'), fun w hw' j hj => ?_,
    Nat.beq_eq.mp h0, fun a ha => Nat.blt_eq.mp (Raw.Orb.allN_iff.1 hlt a ha), ?_, ?_⟩
  · have := List.all_eq_true.1 hfix w hw'
    exact Nat.beq_eq.mp (Raw.Orb.allN_iff.1 this j hj)
  · intro a ha b hb e
    have := Raw.Orb.allN_iff.1 (Raw.Orb.allN_iff.1 hne a ha) b hb
    rw [e] at this
    simp at this
  · intro a ha0 has
    have := Raw.Orb.allN_iff.1 htree (a - 1) (by change a - 1 < lvS i - 1; omega)
    have e : Nat.succ (a - 1) = a := by omega
    rw [Raw.Orb.strictB_eq, e, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, bAnd_iff, bAnd_iff,
      Nat.blt_eq, Nat.blt_eq, Nat.beq_eq] at this
    exact this

section Words

variable {G : Type*} [Group G] [MulAction G (Fin 3510)]

theorem wAp_cons (f : Nat → Nat → Nat) (l : Nat) (w : List Nat) (x : Nat) :
    wAp f (l :: w) x = f l (wAp f w x) := rfl

@[expose] def wG (g : Nat → G) (w : List Nat) : G := (w.map g).prod

theorem wG_smul (g : Nat → G) (f : Nat → Nat → Nat) (m : Nat)
    (hg : ∀ l < m, ∀ x (hx : x < 3510), (g l • (⟨x, hx⟩ : Fin 3510)).val = f l x) :
    ∀ w : List Nat, (∀ l ∈ w, l < m) → ∀ x (hx : x < 3510),
      (wG g w • (⟨x, hx⟩ : Fin 3510)).val = wAp f w x
  | [], _, x, hx => by simp [wG, wAp]
  | l :: w, hw, x, hx => by
    have ih := wG_smul g f m hg w (fun z hz => hw z (List.mem_cons_of_mem l hz)) x hx
    have hlt : wAp f w x < 3510 := by
      rw [← ih]
      exact (wG g w • (⟨x, hx⟩ : Fin 3510)).isLt
    have e : wG g w • (⟨x, hx⟩ : Fin 3510) = ⟨wAp f w x, hlt⟩ := Fin.ext ih
    have hw' : wG g (l :: w) = g l * wG g w := by simp [wG]
    rw [hw', mul_smul, e, hg l (hw l List.mem_cons_self), wAp_cons]

theorem pow_smul_val {x : G} {F : Nat → Nat}
    (hx : ∀ y (hy : y < 3510), (x • (⟨y, hy⟩ : Fin 3510)).val = F y) :
    ∀ (o y : Nat) (hy : y < 3510), ((x ^ o) • (⟨y, hy⟩ : Fin 3510)).val = F^[o] y
  | 0, y, hy => by simp
  | o + 1, y, hy => by
    have hlt : F y < 3510 := by
      rw [← hx y hy]
      exact (x • (⟨y, hy⟩ : Fin 3510)).isLt
    have e : x • (⟨y, hy⟩ : Fin 3510) = ⟨F y, hlt⟩ := Fin.ext (hx y hy)
    rw [pow_succ, mul_smul, e, pow_smul_val hx o, Function.iterate_succ_apply]

end Words

@[expose] def ptSet (f : Nat → Nat) : Finset (Fin 3510) :=
  Finset.univ.filter fun y => ∃ i ∈ Finset.range 22, f i = y.val

theorem mem_ptSet {f : Nat → Nat} {y : Fin 3510} : y ∈ ptSet f ↔ ∃ i < 22, f i = y.val := by
  simp only [ptSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]

theorem mem_iff_gD {L : List Nat} (hL : L.length = 22) (v : Nat) :
    v ∈ L ↔ ∃ j < 22, gD L j = v := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hL ▸ hj, List.getD_eq_getElem _ _ hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hL ▸ hj, (List.getD_eq_getElem _ _ (hL ▸ hj)).symm⟩

theorem lt_of_inc {f : Nat → Nat} (hinc : ∀ i < 21, f i < f (i + 1)) :
    ∀ i j, i < j → j < 22 → f i < f j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact (ih h (by omega)).trans (hinc j (by omega))
    · rw [h]
      exact hinc j (by omega)

theorem ptSet_map {f : Nat → Nat} (hinc : ∀ i < 21, f i < f (i + 1)) (hlt : f 21 < 3510) :
    (ptSet f).map Fin.valEmbedding = (Finset.range 22).image f := by
  ext v
  simp only [Finset.mem_map, Fin.valEmbedding_apply, Finset.mem_image, Finset.mem_range,
    mem_ptSet]
  constructor
  · rintro ⟨y, ⟨i, hi, hiy⟩, rfl⟩
    exact ⟨i, hi, hiy⟩
  · rintro ⟨i, hi, rfl⟩
    have hb : f i < 3510 := by
      rcases Nat.lt_or_ge i 21 with h | h
      · exact (lt_of_inc hinc i 21 h (by omega)).trans hlt
      · have : i = 21 := by omega
        rw [this]
        exact hlt
    exact ⟨⟨f i, hb⟩, ⟨i, hi, rfl⟩, rfl⟩

theorem card_ptSet {f : Nat → Nat} (hinc : ∀ i < 21, f i < f (i + 1)) (hlt : f 21 < 3510) :
    (ptSet f).card = 22 := by
  rw [← Finset.card_map Fin.valEmbedding, ptSet_map hinc hlt, Finset.card_image_of_injOn,
    Finset.card_range]
  intro i hi j hj e
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact absurd e (lt_of_inc hinc i j h hj).ne
  · exact absurd e (lt_of_inc hinc j i h hi).ne'

theorem enum_eq {f g : Nat → Nat} (hf : ∀ i < 21, f i < f (i + 1)) (hf' : f 21 < 3510)
    (hg : ∀ i < 21, g i < g (i + 1)) (hg' : g 21 < 3510) (h : ptSet f = ptSet g) :
    ∀ i < 22, f i = g i := by
  have hs : (Finset.range 22).image f = (Finset.range 22).image g := by
    rw [← ptSet_map hf hf', ← ptSet_map hg hg', h]
  have hc : ((Finset.range 22).image f).card = 22 := by
    rw [← ptSet_map hf hf', Finset.card_map, card_ptSet hf hf']
  have mf : StrictMono fun i : Fin 22 => f i.val := fun i j hij => lt_of_inc hf i j hij j.isLt
  have mg : StrictMono fun i : Fin 22 => g i.val := fun i j hij => lt_of_inc hg i j hij j.isLt
  have ef := Finset.orderEmbOfFin_unique hc (f := fun i : Fin 22 => f i.val)
    (fun i => Finset.mem_image.2 ⟨i.val, Finset.mem_range.2 i.isLt, rfl⟩) mf
  have eg := Finset.orderEmbOfFin_unique hc (f := fun i : Fin 22 => g i.val)
    (fun i => by
      rw [hs]
      exact Finset.mem_image_of_mem g (Finset.mem_range.2 i.isLt)) mg
  intro i hi
  exact congrFun (ef.trans eg.symm) ⟨i, hi⟩

set_option exponentiation.threshold 264 in
theorem rKey_val (KP k : Nat) : rKey KP k = KP / 2 ^ (264 * k) % 2 ^ 264 :=
  Raw.Orb.fld_eq KP (264 * k) 264

theorem rPt_val (KP k i : Nat) : rPt KP k i = KP / 2 ^ (264 * k + 12 * i) % 2 ^ 12 :=
  Raw.Orb.fld_eq KP (264 * k + 12 * i) 12

theorem rKey_eq {KP k k' : Nat} (h : ∀ i < 22, rPt KP k i = rPt KP k' i) :
    rKey KP k = rKey KP k' := by
  rw [rKey_val, rKey_val]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hb : b < 264
  · have e := congrArg (fun z => z.testBit (b % 12)) (h (b / 12) (by omega))
    have hlt : b % 12 < 12 := Nat.mod_lt _ (by norm_num)
    have e1 : b % 12 + (264 * k + 12 * (b / 12)) = b + 264 * k := by omega
    have e2 : b % 12 + (264 * k' + 12 * (b / 12)) = b + 264 * k' := by omega
    change (rPt KP k (b / 12)).testBit (b % 12) = (rPt KP k' (b / 12)).testBit (b % 12) at e
    rw [rPt_val, rPt_val, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
      Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, decide_eq_true hlt, Bool.true_and,
      Bool.true_and, e1, e2] at e
    rw [e]
  · simp [hb]

theorem dc_le {G X : Type*} [Group G] [MulAction G X] [Fintype X] [DecidableEq X]
    [MulAction.IsPretransitive G X] (U : Finset X) (x0 : X) (S : Finset (Finset X))
    (hS : ∀ V ∈ S, V ∈ MulAction.orbit G U ∧ x0 ∈ V) :
    Fintype.card X * S.card ≤ Nat.card (MulAction.orbit G U) * U.card := by
  classical
  set O : Finset (Finset X) := Finset.univ.filter fun V => V ∈ MulAction.orbit G U with hO
  have hcO : Nat.card (MulAction.orbit G U) = O.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
    congr 1
    ext V
    simp [hO]
  have hsum := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := O)
    (t := (Finset.univ : Finset X)) (r := fun V x => x ∈ V)
  have hl : ∀ V ∈ O, (Finset.bipartiteAbove (fun V x => x ∈ V) Finset.univ V).card = U.card := by
    intro V hV
    rw [hO, Finset.mem_filter] at hV
    obtain ⟨g, rfl⟩ := hV.2
    simp only [Finset.bipartiteAbove, Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact Finset.card_smul_finset g U
  rw [Finset.sum_congr rfl hl, Finset.sum_const, smul_eq_mul] at hsum
  have hr : ∀ x ∈ (Finset.univ : Finset X),
      S.card ≤ (Finset.bipartiteBelow (fun V x => x ∈ V) O x).card := by
    intro x _
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x0 x
    refine Finset.card_le_card_of_injOn (fun V => g • V) ?_ ?_
    · intro V hV
      obtain ⟨hVo, hx0⟩ := hS V hV
      change g • V ∈ Finset.bipartiteBelow (fun V x => x ∈ V) O x
      rw [Finset.mem_bipartiteBelow, hO, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · obtain ⟨h, hh⟩ := hVo
        refine ⟨g * h, ?_⟩
        change (g * h) • U = g • V
        rw [mul_smul]
        change h • U = V at hh
        rw [hh]
      · change x ∈ g • V
        rw [← hg]
        exact Finset.smul_mem_smul_finset hx0
    · intro V _ W _ e
      have := congrArg (fun Z => g⁻¹ • Z) e
      simpa using this
  have := Finset.sum_le_sum hr
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, ← hsum] at this
  rw [hcO]
  exact this

section Tree

variable {G : Type*} [Group G] [MulAction G (Fin 3510)]

theorem orbit_ge_of_treeK [MulAction.IsPretransitive G (Fin 3510)] {UL gw : List Nat}
    {N root KP PL PI : Nat} (h : treeK UL gw N root KP PL PI = true) (g : Nat → G)
    (hg : ∀ l < 32, ∀ x (hx : x < 3510), (g l • (⟨x, hx⟩ : Fin 3510)).val = LT l x)
    (U : Finset (Fin 3510)) (hU : ∀ y : Fin 3510, y ∈ U ↔ ∃ j < 22, gD UL j = y.val) :
    3510 * N ≤ Nat.card (MulAction.orbit G U) * 22 := by
  obtain ⟨hul, hgw, h0, hroot, hkeys, hrows⟩ := treeK_spec h
  obtain ⟨-, huinc, hulast⟩ := ulK_spec hul
  have hUeq : U = ptSet (gD UL) := Finset.ext fun y => by rw [hU, mem_ptSet]
  have hcU : U.card = 22 := by rw [hUeq]; exact card_ptSet huinc hulast
  have hUlt : ∀ j < 22, gD UL j < 3510 := by
    intro j hj
    rcases Nat.lt_or_ge j 21 with h | h
    · exact (lt_of_inc huinc j 21 h (by omega)).trans hulast
    · rw [show j = 21 by omega]; exact hulast
  let R : Nat → Finset (Fin 3510) := fun k => ptSet (rPt KP k)
  have hcR : ∀ k < N, (R k).card = 22 := fun k hk =>
    card_ptSet (hrows k hk).1 (hrows k hk).2.1
  let z : Fin 3510 := ⟨0, by norm_num⟩
  have key : ∀ d k, k < N → rDep PL k = d → R k ∈ MulAction.orbit G U ∧ z ∈ R k := by
    intro d
    induction d with
    | zero =>
      intro k hk hd
      by_cases hkr : k = root
      · obtain ⟨-, hpts⟩ := (hrows k hk).2.2.1 hkr
        have hsub : R k ⊆ wG g gw • U := by
          intro y hy
          obtain ⟨i, hi, hiy⟩ := mem_ptSet.1 hy
          obtain ⟨hj, hv⟩ := hpts i hi
          have hlt := hUlt _ hj
          refine Finset.mem_smul_finset.2 ⟨⟨gD UL (rPi PI k i), hlt⟩, (hU _).2 ⟨_, hj, rfl⟩, ?_⟩
          apply Fin.ext
          rw [wG_smul g LT 32 hg gw hgw _ hlt, ← hv, hiy]
        have he : R k = wG g gw • U := Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_smul_finset, hcU, hcR k hk])
        refine ⟨⟨wG g gw, he.symm⟩, ?_⟩
        rw [he]
        refine Finset.mem_smul_finset.2 ⟨⟨gD UL 0, hUlt 0 (by norm_num)⟩,
          (hU _).2 ⟨0, by norm_num, rfl⟩, ?_⟩
        apply Fin.ext
        rw [wG_smul g LT 32 hg gw hgw _ (hUlt 0 (by norm_num)), h0]
      · obtain ⟨-, hd', -⟩ := (hrows k hk).2.2.2 hkr
        omega
    | succ d ih =>
      intro k hk hd
      by_cases hkr : k = root
      · obtain ⟨hd0, -⟩ := (hrows k hk).2.2.1 hkr
        omega
      · obtain ⟨hp, hd', hl, hl0, hpts⟩ := (hrows k hk).2.2.2 hkr
        obtain ⟨hpo, hpz⟩ := ih (rPar PL k) hp (by omega)
        have hsub : R k ⊆ g (rLab PL k) • R (rPar PL k) := by
          intro y hy
          obtain ⟨i, hi, hiy⟩ := mem_ptSet.1 hy
          obtain ⟨hj, hv⟩ := hpts i hi
          have hlt : rPt KP (rPar PL k) (rPi PI k i) < 3510 := by
            have := (ptSet_map (hrows _ hp).1 (hrows _ hp).2.1).symm ▸
              (Finset.mem_image_of_mem (rPt KP (rPar PL k)) (Finset.mem_range.2 hj))
            obtain ⟨y', -, hy'⟩ := Finset.mem_map.1 this
            rw [← hy']
            exact y'.isLt
          refine Finset.mem_smul_finset.2 ⟨⟨_, hlt⟩, mem_ptSet.2 ⟨_, hj, rfl⟩, ?_⟩
          apply Fin.ext
          rw [hg _ hl _ hlt, ← hv, hiy]
        have he : R k = g (rLab PL k) • R (rPar PL k) := Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_smul_finset, hcR _ hp, hcR k hk])
        refine ⟨?_, ?_⟩
        · obtain ⟨x, hx⟩ := hpo
          refine ⟨g (rLab PL k) * x, ?_⟩
          change (g (rLab PL k) * x) • U = R k
          change x • U = R (rPar PL k) at hx
          rw [he, mul_smul, hx]
        · rw [he]
          have hz : g (rLab PL k) • z = z := Fin.ext (by rw [hg _ hl 0 (by norm_num), hl0])
          rw [← hz]
          exact Finset.smul_mem_smul_finset hpz
  have hinj : Set.InjOn R (Finset.range N : Set Nat) := by
    have mono : ∀ k k', k < k' → k' < N → rKey KP k < rKey KP k' := by
      intro k k' hkk hk'
      induction k' with
      | zero => omega
      | succ k' ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hkk with h | h
        · exact (ih h (by omega)).trans (hkeys k' hk')
        · rw [h]
          exact hkeys k' hk'
    intro k hk k' hk' e
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    have hp := enum_eq (hrows k hk).1 (hrows k hk).2.1 (hrows k' hk').1 (hrows k' hk').2.1 e
    have hkey := rKey_eq hp
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd hkey (mono k k' h hk').ne
    · exact absurd hkey (mono k' k h hk).ne'
  have hS := dc_le (G := G) U z ((Finset.range N).image R) (by
    intro V hV
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hV
    exact key _ k (Finset.mem_range.1 hk) rfl)
  rw [Finset.card_image_of_injOn hinj, Finset.card_range, Fintype.card_fin, hcU] at hS
  exact hS

end Tree

section Elts

variable {G : Type*} [Group G] [MulAction G (Fin 3510)]

theorem elts_of_checks {UL w1 w2 p1 p2 : List Nat} (hul : ulK UL = true)
    (hord : ordK w1 w2 = true) (htr : traceK UL w1 w2 p1 p2 = true) (m : Nat → G)
    (hm : ∀ c < 2, ∀ x (hx : x < 3510), (m c • (⟨x, hx⟩ : Fin 3510)).val = AB c x)
    (hsep : ∀ x : G, (∀ b < 5, ∀ hb : BS b < 3510, x • (⟨BS b, hb⟩ : Fin 3510) = ⟨BS b, hb⟩) →
      x = 1)
    (U : Finset (Fin 3510)) (hU : ∀ y : Fin 3510, y ∈ U ↔ ∃ j < 22, gD UL j = y.val) :
    wG m w1 ^ 5 = 1 ∧ (wG m w2 ^ 2) ^ 7 = 1 ∧ wG m w1 • U = U ∧ wG m w2 ^ 2 • U = U := by
  obtain ⟨hl1, hl2, hbase⟩ := ordK_spec hord
  obtain ⟨-, huinc, hulast⟩ := ulK_spec hul
  have hUeq : U = ptSet (gD UL) := Finset.ext fun y => by rw [hU, mem_ptSet]
  have hcU : U.card = 22 := by rw [hUeq]; exact card_ptSet huinc hulast
  have hUlt : ∀ j < 22, gD UL j < 3510 := by
    intro j hj
    rcases Nat.lt_or_ge j 21 with h | h
    · exact (lt_of_inc huinc j 21 h (by omega)).trans hulast
    · rw [show j = 21 by omega]; exact hulast
  have s1 := wG_smul m AB 2 hm w1 hl1
  have s2 := wG_smul m AB 2 hm w2 hl2
  have s22 : ∀ x (hx : x < 3510), ((wG m w2 ^ 2) • (⟨x, hx⟩ : Fin 3510)).val =
      wAp AB w2 (wAp AB w2 x) := by
    intro x hx
    rw [pow_smul_val s2 2 x hx, Function.iterate_succ_apply, Function.iterate_one]
  have hstab : ∀ x : G, (∀ i (hi : i < 22), ∃ j < 22,
      (x • (⟨gD UL i, hUlt i hi⟩ : Fin 3510)).val = gD UL j) → x • U = U := by
    intro x himg
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_smul_finset])
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_smul_finset.1 hy
    obtain ⟨i, hi, hiu⟩ := (hU u).1 hu
    obtain ⟨j, hj, hv⟩ := himg i hi
    have e : u = ⟨gD UL i, hUlt i hi⟩ := Fin.ext hiu.symm
    rw [hU, e]
    exact ⟨j, hj, hv.symm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine hsep _ fun b hb hb' => Fin.ext ?_
    rw [pow_smul_val s1 5 _ hb']
    exact (hbase b hb).1
  · rw [← pow_mul]
    refine hsep _ fun b hb hb' => Fin.ext ?_
    rw [pow_smul_val s2 (2 * 7) _ hb']
    exact (hbase b hb).2
  · refine hstab _ fun i hi => ?_
    obtain ⟨hj, -, hv, -⟩ := traceK_spec htr i hi
    exact ⟨gD p1 i, hj, by rw [s1, hv]⟩
  · refine hstab _ fun i hi => ?_
    obtain ⟨-, hj, -, hv⟩ := traceK_spec htr i hi
    exact ⟨gD p2 i, hj, by rw [s22, hv]⟩

end Elts

section Chain

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def preS (t : Nat → X) (i : Nat) : Subgroup G where
  carrier := {g | ∀ j < i, g • t j = t j}
  mul_mem' {a b} ha hb j hj := by
    change (a * b) • t j = t j
    rw [mul_smul, hb j hj, ha j hj]
  one_mem' j _ := one_smul G (t j)
  inv_mem' {a} ha j hj := by
    change a⁻¹ • t j = t j
    rw [inv_smul_eq_iff, ha j hj]

theorem mem_preS {t : Nat → X} {i : Nat} {g : G} : g ∈ preS t i ↔ ∀ j < i, g • t j = t j :=
  Iff.rfl

theorem orbit_mul_stab {Y : Type*} [MulAction G Y] (K : Subgroup G) (y : Y) :
    Nat.card (MulAction.orbit K y) * Nat.card (MulAction.stabilizer K y) = Nat.card K := by
  have e1 : (MulAction.stabilizer K y).index = Nat.card (MulAction.orbit K y) := by
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  rw [← e1, mul_comm]
  exact Subgroup.card_mul_index _

theorem card_stab_sub (H : Subgroup G) (t : Nat → X) (i : Nat) :
    Nat.card (MulAction.stabilizer ↥(H ⊓ preS t i) (t i)) = Nat.card ↥(H ⊓ preS t (i + 1)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, (Subgroup.mem_inf.1 x.1.2).1, mem_preS.2 fun j hj => ?_⟩
      invFun := fun x => ⟨⟨x.1, Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 x.2).1,
        mem_preS.2 fun j hj => mem_preS.1 (Subgroup.mem_inf.1 x.2).2 j (by omega)⟩⟩, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · exact mem_preS.1 (Subgroup.mem_inf.1 x.1.2).2 j h
    · rw [h]
      exact x.2
  · rw [MulAction.mem_stabilizer_iff]
    exact mem_preS.1 (Subgroup.mem_inf.1 x.2).2 i (by omega)

theorem chain_card [Finite G] (H : Subgroup G) (n : Nat) (t : Nat → X) (s : Nat → Nat)
    (hs : ∀ i < n, s i ≤ Nat.card (MulAction.orbit ↥(H ⊓ preS t i) (t i))) :
    ∏ i ∈ Finset.range n, s i ≤ Nat.card (MulAction.orbit H fun j : Fin n => t j) := by
  have step : ∀ i ≤ n, (∏ j ∈ Finset.range i, s j) * Nat.card ↥(H ⊓ preS t i) ≤ Nat.card H := by
    intro i hi
    induction i with
    | zero =>
      have : H ⊓ preS t 0 = H := by
        rw [inf_eq_left]
        intro g _
        exact mem_preS.2 fun j hj => absurd hj (Nat.not_lt_zero j)
      simp only [this, Finset.prod_range_zero, one_mul, le_refl]
    | succ i ih =>
      have h1 := ih (by omega)
      have h2 := orbit_mul_stab (H ⊓ preS t i) (t i)
      rw [card_stab_sub] at h2
      rw [Finset.prod_range_succ, mul_assoc]
      refine le_trans ?_ h1
      apply Nat.mul_le_mul_left
      rw [← h2]
      exact Nat.mul_le_mul_right _ (hs i (by omega))
  have hfin := step n le_rfl
  have hst : Nat.card (MulAction.stabilizer H fun j : Fin n => t j) = Nat.card ↥(H ⊓ preS t n) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, mem_preS.2 fun j hj => ?_⟩⟩
        invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    · have := congrFun (MulAction.mem_stabilizer_iff.1 x.2) ⟨j, hj⟩
      exact this
    · rw [MulAction.mem_stabilizer_iff]
      funext j
      exact mem_preS.1 (Subgroup.mem_inf.1 x.2).2 j j.isLt
  have ho := orbit_mul_stab H fun j : Fin n => t j
  rw [hst] at ho
  have hpos : 0 < Nat.card ↥(H ⊓ preS t n) := Nat.card_pos
  rw [← ho] at hfin
  exact Nat.le_of_mul_le_mul_right hfin hpos

end Chain

section Tuple

variable {G : Type*} [Group G] [MulAction G (Fin 3510)]

@[expose] noncomputable def tP (UL : List Nat) (j : Nat) : Fin 3510 := ⟨gD UL j % 3510, Nat.mod_lt _ (by norm_num)⟩

theorem lvS_prod : ∏ i ∈ Finset.range 5, lvS i = 443520 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  decide

theorem getD_mem {W : List (List Nat)} {c : Nat} (hc : c < W.length) : W.getD c [] ∈ W := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some]
  exact List.getElem_mem hc

theorem orbit_ge_of_chainK [Finite G] {UL w1 w2 p1 p2 : List Nat}
    {lvW : List (List (List Nat))} {lvO lvP lvG : List (List Nat)} (hul : ulK UL = true)
    (hord : ordK w1 w2 = true) (htr : traceK UL w1 w2 p1 p2 = true)
    (hch : chainK p1 p2 lvW lvO lvP lvG = true) (m : Nat → G)
    (hm : ∀ c < 2, ∀ x (hx : x < 3510), (m c • (⟨x, hx⟩ : Fin 3510)).val = AB c x)
    (H : Subgroup G) (h1 : wG m w1 ∈ H) (h2 : wG m w2 ^ 2 ∈ H) :
    443520 ≤ Nat.card (MulAction.orbit H fun j : Fin 5 => tP UL j) := by
  obtain ⟨hl1, hl2, -⟩ := ordK_spec hord
  obtain ⟨-, huinc, hulast⟩ := ulK_spec hul
  have hUlt : ∀ j < 22, gD UL j < 3510 := by
    intro j hj
    rcases Nat.lt_or_ge j 21 with h | h
    · exact (lt_of_inc huinc j 21 h (by omega)).trans hulast
    · rw [show j = 21 by omega]; exact hulast
  have hUinj : ∀ i j, i < 22 → j < 22 → gD UL i = gD UL j → i = j := by
    intro i j hi hj e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd e (lt_of_inc huinc i j h hj).ne
    · exact absurd e (lt_of_inc huinc j i h hi).ne'
  have htP : ∀ j < 22, (tP UL j).val = gD UL j := fun j hj => Nat.mod_eq_of_lt (hUlt j hj)
  have s1 := wG_smul m AB 2 hm w1 hl1
  have s2 := wG_smul m AB 2 hm w2 hl2
  let ψ : Nat → G := fun c => if c = 0 then wG m w1 else wG m w2 ^ 2
  have hψH : ∀ c, ψ c ∈ H := by
    intro c
    by_cases hc : c = 0
    · simp only [ψ, if_pos hc]; exact h1
    · simp only [ψ, if_neg hc]; exact h2
  have hψ : ∀ c < 2, ∀ j < 22, PP p1 p2 c j < 22 ∧ ψ c • tP UL j = tP UL (PP p1 p2 c j) := by
    intro c hc j hj
    obtain ⟨hj1, hj2, hv1, hv2⟩ := traceK_spec htr j hj
    rw [PP_eq]
    by_cases hc0 : c = 0
    · simp only [ψ, if_pos hc0]
      refine ⟨hj1, Fin.ext ?_⟩
      have e : tP UL j = ⟨gD UL j, hUlt j hj⟩ := Fin.ext (htP j hj)
      rw [e, s1, hv1, htP _ hj1]
    · simp only [ψ, if_neg hc0]
      refine ⟨hj2, Fin.ext ?_⟩
      have e : tP UL j = ⟨gD UL j, hUlt j hj⟩ := Fin.ext (htP j hj)
      rw [e, pow_smul_val s2 2 _ (hUlt j hj), Function.iterate_succ_apply, Function.iterate_one,
        htP _ hj2, hv2]
  have hword : ∀ w : List Nat, (∀ l ∈ w, l < 2) → ∀ j < 22,
      wAp (PP p1 p2) w j < 22 ∧ wG ψ w • tP UL j = tP UL (wAp (PP p1 p2) w j) := by
    intro w
    induction w with
    | nil => intro _ j hj; simp [wG, wAp, hj]
    | cons l w ih =>
      intro hw j hj
      obtain ⟨hlt, he⟩ := ih (fun z hz => hw z (List.mem_cons_of_mem l hz)) j hj
      obtain ⟨hlt', he'⟩ := hψ l (hw l List.mem_cons_self) _ hlt
      refine ⟨hlt', ?_⟩
      have e : wG ψ (l :: w) = ψ l * wG ψ w := by simp [wG]
      rw [e, mul_smul, he, he', wAp_cons]
  have hwH : ∀ w : List Nat, wG ψ w ∈ H := by
    intro w
    induction w with
    | nil =>
      rw [wG, List.map_nil, List.prod_nil]
      exact H.one_mem
    | cons l w ih =>
      have e : wG ψ (l :: w) = ψ l * wG ψ w := by simp [wG]
      rw [e]
      exact H.mul_mem (hψH l) ih
  rw [← lvS_prod]
  unfold chainK at hch
  refine chain_card H 5 (tP UL) lvS fun i hi => ?_
  have hlv := levelK_spec (Raw.Orb.allN_iff.1 hch i hi)
  set W := lvW.getD i []
  set O := lvO.getD i []
  set P := lvP.getD i []
  set Gl := lvG.getD i []
  obtain ⟨hWl, hWfix, hO0, hOlt, hOne, htree⟩ := hlv
  have hWS : ∀ c < W.length, wG ψ (W.getD c []) ∈ H ⊓ preS (tP UL) i := by
    intro c hc
    have hmem : W.getD c [] ∈ W := getD_mem hc
    refine Subgroup.mem_inf.2 ⟨hwH _, mem_preS.2 fun j hj => ?_⟩
    rw [(hword _ (hWl _ hmem) j (by omega)).2, hWfix _ hmem j hj]
  have reach : ∀ a, a < lvS i → ∃ x ∈ H ⊓ preS (tP UL) i, x • tP UL i = tP UL (gD O a) := by
    intro a
    refine Nat.strong_induction_on a ?_
    intro a ih ha
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      exact ⟨1, Subgroup.one_mem _, by rw [one_smul, hO0]⟩
    · obtain ⟨hp, hc, he⟩ := htree a hpos ha
      obtain ⟨x, hx, hxe⟩ := ih _ hp (by omega)
      refine ⟨wG ψ (W.getD (gD Gl a) []) * x, Subgroup.mul_mem _ (hWS _ hc) hx, ?_⟩
      have hmem : W.getD (gD Gl a) [] ∈ W := getD_mem hc
      rw [mul_smul, hxe, (hword _ (hWl _ hmem) _ (hOlt _ (by omega))).2, he]
  choose! f hf hfe using reach
  let F : Fin (lvS i) → MulAction.orbit ↥(H ⊓ preS (tP UL) i) (tP UL i) := fun a =>
    ⟨tP UL (gD O a), ⟨⟨f a, hf a a.isLt⟩, hfe a a.isLt⟩⟩
  have hF : Function.Injective F := by
    intro a b e
    have e' : tP UL (gD O a) = tP UL (gD O b) := congrArg Subtype.val e
    have e'' := congrArg Fin.val e'
    rw [htP _ (hOlt _ a.isLt), htP _ (hOlt _ b.isLt)] at e''
    have hab := hUinj _ _ (hOlt _ a.isLt) (hOlt _ b.isLt) e''
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hOne _ b.isLt _ h hab.symm
    · exact hOne _ a.isLt _ h hab
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_fin] at this

end Tuple

end CFSG.KS.Fi22Gen

end
