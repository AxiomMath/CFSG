module

public import Certificates.Data.Kernel.F4Planes
public import CFSG.Certificates.Kernel.F4Syl3.ModelUse
public import CFSG.Certificates.Kernel.SporCov.P3Group
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.F4Planes

open CFSG.KC.F4Syl3 Subgroup

theorem allN_spec {f : ℕ → Bool} : ∀ {n : ℕ}, allN n f = true → ∀ i, i < n → f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have e : allN (n + 1) f = Bool.rec (motive := fun _ => Bool) false (allN n f) (f n) := rfl
    rw [e] at h
    cases hf : f n
    · rw [hf] at h
      exact absurd h Bool.false_ne_true
    · rw [hf] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact allN_spec h i hi
      · exact hf

theorem allL_spec {α : Type} {f : α → Bool} : ∀ {l : List α}, allL l f = true → ∀ x ∈ l, f x = true
  | [], _, x, hx => absurd hx (List.not_mem_nil)
  | y :: l, h, x, hx => by
    have e : allL (y :: l) f = Bool.rec (motive := fun _ => Bool) false (allL l f) (f y) := rfl
    rw [e] at h
    cases hf : f y
    · rw [hf] at h
      exact absurd h Bool.false_ne_true
    · rw [hf] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hf
      · exact allL_spec h x hx

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem testBit_of_bitB {M v : ℕ} (h : bitB M v = true) : M.testBit v = true := by
  by_contra hb
  have e1 : Nat.land M (Nat.shiftLeft 1 v) = M &&& 2 ^ v := by
    rw [← Nat.one_shiftLeft]
    rfl
  have e : Nat.land M (Nat.shiftLeft 1 v) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [e1, Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : v = i
    · subst hi
      rw [Bool.eq_false_iff.2 hb]
      rfl
    · simp [hi]
  have h' : Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 v)) = true := h
  rw [e] at h'
  exact absurd h' (by decide)

theorem testBit_lor_shift {e M v : ℕ} (h : (Nat.lor (Nat.shiftLeft 1 e) M).testBit v = true) :
    e = v ∨ M.testBit v = true := by
  have e1 : Nat.lor (Nat.shiftLeft 1 e) M = 2 ^ e ||| M := by
    rw [← Nat.one_shiftLeft]
    rfl
  rw [e1, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (of_decide_eq_true h)
  · exact Or.inr h

variable {VT AT QT OM PR : ℕ}

theorem mem_of_maskC {y yi v : ℕ} :
    ∀ {l : List ℕ}, (maskC VT AT QT y yi l).testBit v = true →
      ∃ e ∈ l, conjT VT AT QT y yi e = v
  | [], h => by
    have e : maskC VT AT QT y yi [] = 0 := rfl
    rw [e, Nat.zero_testBit] at h
    exact absurd h Bool.false_ne_true
  | e :: l, h => by
    have e0 : maskC VT AT QT y yi (e :: l) =
        Nat.lor (Nat.shiftLeft 1 (conjT VT AT QT y yi e)) (maskC VT AT QT y yi l) := rfl
    rw [e0] at h
    rcases testBit_lor_shift h with h | h
    · exact ⟨e, List.mem_cons.2 (Or.inl rfl), h⟩
    · obtain ⟨e', he', hc⟩ := mem_of_maskC h
      exact ⟨e', List.mem_cons.2 (Or.inr he'), hc⟩

theorem mem_of_rowsMask {v : ℕ} :
    ∀ {rows : List (ℕ × ℕ × ℕ)}, (rowsMask VT AT QT PR rows).testBit v = true →
      ∃ row ∈ rows, (rowMask VT AT QT PR row).testBit v = true
  | [], h => by
    have e : rowsMask VT AT QT PR [] = 0 := rfl
    rw [e, Nat.zero_testBit] at h
    exact absurd h Bool.false_ne_true
  | row :: rows, h => by
    have e0 : rowsMask VT AT QT PR (row :: rows) =
        rowMask VT AT QT PR row ||| rowsMask VT AT QT PR rows := rfl
    rw [e0, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨row, List.mem_cons.2 (Or.inl rfl), h⟩
    · obtain ⟨r', hr', hc⟩ := mem_of_rowsMask h
      exact ⟨r', List.mem_cons.2 (Or.inr hr'), hc⟩

theorem pmulT_eq (ht : tabChk VT AT QT = true) {m n : ℕ} (hm : m < 729) (hn : n < 729) :
    pmulT VT AT QT m n = pmul m n := by
  simp only [tabChk, Bool.and_eq_true] at ht
  obtain ⟨⟨hV, hA⟩, hQ⟩ := ht
  have h1 : m % 81 < 81 := Nat.mod_lt _ (by decide)
  have h2 : m / 81 < 9 := by omega
  have h3 : n % 81 < 81 := Nat.mod_lt _ (by decide)
  have h4 : n / 81 < 9 := by omega
  have eA : ent7 AT (Nat.add (Nat.mul 81 (m / 81)) (n % 81)) = actQ (m / 81) (n % 81) :=
    Nat.eq_of_beq_eq_true (allN_spec (allN_spec hA _ h2) _ h3)
  have eV : ent7 VT (Nat.add (Nat.mul 81 (m % 81)) (actQ (m / 81) (n % 81))) =
      vadd (m % 81) (actQ (m / 81) (n % 81)) :=
    Nat.eq_of_beq_eq_true (allN_spec (allN_spec hV _ h1) _ (actQ_lt _ h3))
  have eQ : ent4 QT (Nat.add (Nat.mul 9 (m / 81)) (n / 81)) = qadd (m / 81) (n / 81) :=
    Nat.eq_of_beq_eq_true (allN_spec (allN_spec hQ _ h2) _ h4)
  have e : pmulT VT AT QT m n = Nat.add (ent7 VT (Nat.add (Nat.mul 81 (m % 81))
      (ent7 AT (Nat.add (Nat.mul 81 (m / 81)) (n % 81)))))
        (Nat.mul 81 (ent4 QT (Nat.add (Nat.mul 9 (m / 81)) (n / 81)))) := rfl
  rw [e, eA, eV, eQ]
  rfl

theorem pmulT_lt (ht : tabChk VT AT QT = true) {m n : ℕ} (hm : m < 729) (hn : n < 729) :
    pmulT VT AT QT m n < 729 := by
  rw [pmulT_eq ht hm hn]
  exact pmul_lt m n

theorem om_spec (ht : tabChk VT AT QT = true) (ho : omChk VT AT QT OM = true) {v : ℕ}
    (hv : v < 729) (h0 : v ≠ 0) (h3 : pmul (pmul v v) v = 0) : bitB OM v = true := by
  have h := allN_spec ho v hv
  rw [pmulT_eq ht hv hv, pmulT_eq ht (pmul_lt v v) hv, h3] at h
  simpa [h0] using h

theorem ord3B_spec (ht : tabChk VT AT QT = true) {m : ℕ} (h : ord3B VT AT QT m = true) :
    m < 729 ∧ pmul (pmul m m) m = 0 := by
  simp only [ord3B, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hm, h3⟩ := h
  rw [pmulT_eq ht hm hm, pmulT_eq ht (pmul_lt m m) hm] at h3
  exact ⟨hm, Nat.eq_of_beq_eq_true h3⟩

theorem rep_spec (ht : tabChk VT AT QT = true) (hr : repChk VT AT QT PR = true) {r : ℕ}
    (hr67 : r < 67) :
    aR PR r < 729 ∧ pmul (pmul (aR PR r) (aR PR r)) (aR PR r) = 0 ∧ bR PR r < 729 ∧
      pmul (pmul (bR PR r) (bR PR r)) (bR PR r) = 0 ∧
      pmul (aR PR r) (bR PR r) = pmul (bR PR r) (aR PR r) := by
  have h := allN_spec hr r hr67
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨ha, hb⟩, hab⟩ := h
  obtain ⟨ha1, ha2⟩ := ord3B_spec ht ha
  obtain ⟨hb1, hb2⟩ := ord3B_spec ht hb
  rw [pmulT_eq ht ha1 hb1, pmulT_eq ht hb1 ha1] at hab
  exact ⟨ha1, ha2, hb1, hb2, Nat.eq_of_beq_eq_true hab⟩

theorem scan_spec {u u2 U : ℕ} (h : scanB VT AT QT OM u u2 U = true) {v : ℕ} (hv : v < 729)
    (ho : bitB OM v = true) (hc : pmulT VT AT QT u v = pmulT VT AT QT v u) (hu : v ≠ u)
    (hu2 : v ≠ u2) : bitB U v = true := by
  have h' := allN_spec h v hv
  simpa [ho, hc, hu, hu2] using h'

theorem rows_spec {u : ℕ} {rows : List (ℕ × ℕ × ℕ)} (h : rowsB VT AT QT OM PR u rows = true) :
    u < 729 ∧ (∀ row ∈ rows, rowB VT AT QT PR u row = true) ∧
      ∀ v, v < 729 → bitB OM v = true → pmulT VT AT QT u v = pmulT VT AT QT v u → v ≠ u →
        v ≠ pmulT VT AT QT u u → bitB (rowsMask VT AT QT PR rows) v = true := by
  simp only [rowsB, Bool.and_eq_true, Nat.blt_eq, strictB_eq] at h
  obtain ⟨⟨hu, hrows⟩, hs⟩ := h
  exact ⟨hu, allL_spec hrows, fun v hv ho hc h1 h2 => scan_spec hs hv ho hc h1 h2⟩

theorem row_spec {u : ℕ} {row : ℕ × ℕ × ℕ} (h : rowB VT AT QT PR u row = true) :
    row.1 < 67 ∧ row.2.1 < 729 ∧ row.2.2 < 729 ∧ pmulT VT AT QT row.2.1 row.2.2 = 0 ∧
      bitB (rowMask VT AT QT PR row) u = true := by
  simp only [rowB, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, Nat.eq_of_beq_eq_true h4, h5⟩

variable {G : Type*} [Group G]

theorem card_closure_pair_le {x y : G} (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    Nat.card (closure ({x, y} : Set G)) ≤ 9 := by
  have hc : Commute x y := hxy
  have hmul : ∀ i j k l : ℕ, x ^ i * y ^ j * (x ^ k * y ^ l) = x ^ (i + k) * y ^ (j + l) := by
    intro i j k l
    have e : y ^ j * x ^ k = x ^ k * y ^ j := ((Commute.pow_pow hc k j).eq).symm
    calc x ^ i * y ^ j * (x ^ k * y ^ l) = x ^ i * (y ^ j * x ^ k) * y ^ l := by
          simp only [mul_assoc]
      _ = x ^ (i + k) * y ^ (j + l) := by
          rw [e, pow_add, pow_add]
          simp only [mul_assoc]
  have hS : ∀ g ∈ closure ({x, y} : Set G), ∃ i j : ℕ, x ^ i * y ^ j = g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul g h _ _ ihg ihh =>
      obtain ⟨i, j, rfl⟩ := ihg
      obtain ⟨k, l, rfl⟩ := ihh
      exact ⟨i + k, j + l, (hmul i j k l).symm⟩
    | inv g _ ih =>
      obtain ⟨i, j, rfl⟩ := ih
      refine ⟨2 * i, 2 * j, (inv_eq_of_mul_eq_one_right ?_).symm⟩
      have e1 : i + 2 * i = 3 * i := by ring
      have e2 : j + 2 * j = 3 * j := by ring
      rw [hmul, e1, e2, pow_mul, pow_mul, hx, hy, one_pow, one_pow, mul_one]
  have hF : ∀ g : closure ({x, y} : Set G), ∃ p : Fin 3 × Fin 3, x ^ (p.1 : ℕ) * y ^ (p.2 : ℕ) = g :=
    fun g => by
      obtain ⟨i, j, e⟩ := hS g g.2
      refine ⟨(⟨i % 3, Nat.mod_lt _ (by decide)⟩, ⟨j % 3, Nat.mod_lt _ (by decide)⟩), ?_⟩
      rw [pow_mod3 hx, pow_mod3 hy, e]
  choose F hF using hF
  have hinj : Function.Injective F := fun g h e => Subtype.ext (by rw [← hF g, ← hF h, e])
  calc Nat.card (closure ({x, y} : Set G)) ≤ Nat.card (Fin 3 × Fin 3) :=
        Nat.card_le_card_of_injective F hinj
    _ = 9 := by simp

@[expose] def planeR (s : Fin 4 → G) (g4 g5 : G) (PR r : ℕ) : Subgroup G :=
  closure {phi s g4 g5 (aR PR r), phi s g4 g5 (bR PR r)}

section Pres

variable {s : Fin 4 → G} {g4 g5 : G} (hp : Pres s g4 g5)
include hp

theorem phi_mem_P' (m : ℕ) : phi s g4 g5 m ∈ closure (gensP s g4 g5) := by
  have hs : fS s (m % 81) ∈ closure (gensP s g4 g5) := T_le_P s g4 g5 (fS_mem_T s _)
  have h4m : g4 ∈ closure (gensP s g4 g5) := subset_closure (Or.inr (Or.inl rfl))
  have h5m : g5 ∈ closure (gensP s g4 g5) := subset_closure (Or.inr (Or.inr rfl))
  exact mul_mem hs (mul_mem (pow_mem h4m _) (pow_mem h5m _))

theorem card_planeR_le (ht : tabChk VT AT QT = true) (hr : repChk VT AT QT PR = true) (hm : ModelOK)
    {r : ℕ} (hr67 : r < 67) : Nat.card (planeR s g4 g5 PR r) ≤ 9 := by
  obtain ⟨ha, ha3, hb, hb3, hab⟩ := rep_spec ht hr hr67
  have e3 : ∀ m, m < 729 → pmul (pmul m m) m = 0 → phi s g4 g5 m ^ 3 = 1 := fun m _ h => by
    rw [pow_succ, pow_two, ← phi_pmul hp, ← phi_pmul hp, h, phi_zero hp]
  refine card_closure_pair_le ?_ (e3 _ ha ha3) (e3 _ hb hb3)
  rw [← phi_pmul hp, ← phi_pmul hp, hab]

theorem planeL_mem (ht : tabChk VT AT QT = true) {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    ∀ e ∈ planeL VT AT QT a b, e < 729 ∧
      phi s g4 g5 e ∈ closure ({phi s g4 g5 a, phi s g4 g5 b} : Set G) := by
  set C := closure ({phi s g4 g5 a, phi s g4 g5 b} : Set G)
  have key : ∀ {m n : ℕ}, (m < 729 ∧ phi s g4 g5 m ∈ C) → (n < 729 ∧ phi s g4 g5 n ∈ C) →
      pmulT VT AT QT m n < 729 ∧ phi s g4 g5 (pmulT VT AT QT m n) ∈ C := by
    intro m n hm hn
    rw [pmulT_eq ht hm.1 hn.1, phi_pmul hp]
    exact ⟨pmul_lt m n, mul_mem hm.2 hn.2⟩
  have k0 : 0 < 729 ∧ phi s g4 g5 0 ∈ C := ⟨by decide, by rw [phi_zero hp]; exact one_mem C⟩
  have ka : a < 729 ∧ phi s g4 g5 a ∈ C := ⟨ha, subset_closure (Or.inl rfl)⟩
  have kb : b < 729 ∧ phi s g4 g5 b ∈ C := ⟨hb, subset_closure (Or.inr rfl)⟩
  have ka2 := key ka ka
  have kb2 := key kb kb
  intro e he
  simp only [planeL, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k0
  · exact ka
  · exact ka2
  · exact kb
  · exact key ka kb
  · exact key ka2 kb
  · exact kb2
  · exact key ka kb2
  · exact key ka2 kb2

theorem phi_conjT (ht : tabChk VT AT QT = true) {y yi e : ℕ} (hy : y < 729) (hyi : yi < 729)
    (he : e < 729) (h1 : pmulT VT AT QT y yi = 0) :
    phi s g4 g5 (conjT VT AT QT y yi e) = phi s g4 g5 y * phi s g4 g5 e * (phi s g4 g5 y)⁻¹ := by
  have hinv : phi s g4 g5 yi = (phi s g4 g5 y)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← phi_pmul hp, ← pmulT_eq ht hy hyi, h1, phi_zero hp]
  have e1 : conjT VT AT QT y yi e = pmul (pmul y e) yi := by
    rw [conjT, pmulT_eq ht hy he, pmulT_eq ht (pmul_lt y e) hyi]
  rw [e1, phi_pmul hp, phi_pmul hp, hinv]

theorem plane_conj [Finite G] (hm : ModelOK) {reps tgt : List ℕ} {cover : List (ℕ × ℕ)}
    (hcov : coverChk reps tgt cover = true) {rows : List (List (ℕ × ℕ × ℕ))}
    (ht : tabChk VT AT QT = true) (ho : omChk VT AT QT OM = true) (hr : repChk VT AT QT PR = true)
    (hk : ∀ k, k < 48 → rowK VT AT QT OM PR reps rows k = true) {E : Subgroup G}
    (hE : E ≤ closure (gensP s g4 g5)) (h3 : ∀ x ∈ E, x ^ 3 = 1) (h9 : Nat.card E = 9) :
    ∃ r, r < 67 ∧ ∃ z ∈ closure (gensP s g4 g5),
      E = (planeR s g4 g5 PR r).map (MulAut.conj z).toMonoidHom := by
  set P := closure (gensP s g4 g5)
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    rcases E.bot_or_exists_ne_one with h | h
    · rw [h, Subgroup.card_bot] at h9
      exact absurd h9 (by decide)
    · exact h
  obtain ⟨m, hm729, rfl⟩ := mem_P hp (hE hxE)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hx1 (phi_zero hp)
  have hmc : pmul (pmul m m) m = 0 := by
    refine phi_injOn hp hm (pmul_lt _ _) (by decide : (0 : ℕ) < 729) ?_
    rw [phi_pmul hp, phi_pmul hp, phi_zero hp, ← h3 _ hxE, pow_succ, pow_two]
  obtain ⟨hk48, hcu⟩ := cover_spec hcov hm729 hm0 hmc
  set c := (cover.getD m (0, 0)).1
  set k := (cover.getD m (0, 0)).2
  set u := reps.getD k 0
  obtain ⟨hu729, hrowsk, hscan⟩ := rows_spec (u := u) (rows := rows.getD k []) (hk k hk48)
  set C := phi s g4 g5 c
  set f := (MulAut.conj C).toMonoidHom
  have hf : ∀ g, f g = C * g * C⁻¹ := fun g => rfl
  have hfu : f (phi s g4 g5 m) = phi s g4 g5 u := by
    rw [hf, ← phi_pmul hp, hcu, phi_pmul hp, mul_inv_cancel_right]
  set E' := E.map f
  have hCP : C ∈ P := phi_mem_P' hp c
  have hE'P : E' ≤ P := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hf]
    exact mul_mem (mul_mem hCP (hE hg)) (inv_mem hCP)
  have hE'3 : ∀ g ∈ E', g ^ 3 = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, h3 g hg, map_one]
  have hE'9 : Nat.card E' = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj C).injective, h9]
  have huE : phi s g4 g5 u ∈ E' := by
    rw [← hfu]
    exact mem_map_of_mem f hxE
  have hu3 : phi s g4 g5 u ^ 3 = 1 := hE'3 _ huE
  have hu1 : phi s g4 g5 u ≠ 1 := by
    rw [← hfu]
    intro h
    exact hx1 ((MulAut.conj C).injective (h.trans (map_one f).symm))
  have hzu : Nat.card (zpowers (phi s g4 g5 u)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu3 hu1]
  obtain ⟨v, hvE, hvz⟩ : ∃ v ∈ E', v ∉ zpowers (phi s g4 g5 u) := by
    by_contra hno
    push Not at hno
    have := Subgroup.card_le_of_le (fun g hg => hno g hg : E' ≤ zpowers (phi s g4 g5 u))
    rw [hE'9, hzu] at this
    exact absurd this (by decide)
  obtain ⟨n, hn729, rfl⟩ := mem_P hp (hE'P hvE)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hvz (by rw [phi_zero hp]; exact one_mem _)
  have hnc : pmul (pmul n n) n = 0 := by
    refine phi_injOn hp hm (pmul_lt _ _) (by decide : (0 : ℕ) < 729) ?_
    rw [phi_pmul hp, phi_pmul hp, phi_zero hp, ← hE'3 _ hvE, pow_succ, pow_two]
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (hE'9.trans (by norm_num))
  have huv : phi s g4 g5 u * phi s g4 g5 n = phi s g4 g5 n * phi s g4 g5 u :=
    congrArg Subtype.val (hcomm.is_comm.comm (⟨_, huE⟩ : E') ⟨_, hvE⟩)
  have hnu : n ≠ u := by
    rintro rfl
    exact hvz (mem_zpowers _)
  have hnu2 : n ≠ pmul u u := by
    rintro rfl
    rw [phi_pmul hp] at hvz
    exact hvz (mul_mem (mem_zpowers _) (mem_zpowers _))
  have hbit := hscan n hn729 (om_spec ht ho hn729 hn0 hnc)
    (by
      rw [pmulT_eq ht hu729 hn729, pmulT_eq ht hn729 hu729]
      refine phi_injOn hp hm (pmul_lt _ _) (pmul_lt _ _) ?_
      rw [phi_pmul hp, phi_pmul hp, huv])
    hnu (by rw [pmulT_eq ht hu729 hu729]; exact hnu2)
  obtain ⟨row, hrow, hrn⟩ := mem_of_rowsMask (testBit_of_bitB hbit)
  obtain ⟨hr67, hy, hyi, hyy, hru⟩ := row_spec (hrowsk row hrow)
  obtain ⟨ha, -, hb, -, -⟩ := rep_spec ht hr hr67
  have hpl := planeL_mem hp ht ha hb
  obtain ⟨e2, he2, hce2⟩ : ∃ e ∈ planeL VT AT QT (aR PR row.1) (bR PR row.1),
      conjT VT AT QT row.2.1 row.2.2 e = n := mem_of_maskC hrn
  obtain ⟨e1, he1, hce1⟩ : ∃ e ∈ planeL VT AT QT (aR PR row.1) (bR PR row.1),
      conjT VT AT QT row.2.1 row.2.2 e = u := mem_of_maskC (testBit_of_bitB hru)
  set Y := phi s g4 g5 row.2.1
  set g := (MulAut.conj Y).toMonoidHom
  have hg : ∀ w, g w = Y * w * Y⁻¹ := fun w => rfl
  set R' := (planeR s g4 g5 PR row.1).map g
  have huR : phi s g4 g5 u ∈ R' := by
    rw [← hce1, phi_conjT hp ht hy hyi (hpl e1 he1).1 hyy, ← hg]
    exact mem_map_of_mem g (hpl e1 he1).2
  have hvR : phi s g4 g5 n ∈ R' := by
    rw [← hce2, phi_conjT hp ht hy hyi (hpl e2 he2).1 hyy, ← hg]
    exact mem_map_of_mem g (hpl e2 he2).2
  have hpair := CFSG.KD.SporCov.eq_closure_pair (p := 3) Nat.prime_three hu3 hu1 hE'9 huE hvE hvz
  have hE'R : E' ≤ R' := by
    rw [← hpair, closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact huR
    · exact hvR
  have hR9 : Nat.card R' ≤ 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj Y).injective]
    exact card_planeR_le hp ht hr hm hr67
  have hER : E' = R' := eq_of_le_of_card_ge hE'R (by rw [hE'9]; exact hR9)
  refine ⟨row.1, hr67, C⁻¹ * Y, mul_mem (inv_mem hCP) (phi_mem_P' hp _), ?_⟩
  ext w
  constructor
  · intro hw
    have h1 : f w ∈ R' := hER ▸ mem_map_of_mem f hw
    obtain ⟨w', hw', e⟩ := mem_map.1 h1
    refine mem_map.2 ⟨w', hw', ?_⟩
    rw [hg, hf] at e
    change C⁻¹ * Y * w' * (C⁻¹ * Y)⁻¹ = w
    calc C⁻¹ * Y * w' * (C⁻¹ * Y)⁻¹ = C⁻¹ * (Y * w' * Y⁻¹) * C := by group
      _ = w := by rw [e]; group
  · intro hw
    obtain ⟨w', hw', rfl⟩ := mem_map.1 hw
    have h1 : g w' ∈ E' := hER ▸ mem_map_of_mem g hw'
    obtain ⟨w'', hw'', e⟩ := mem_map.1 h1
    rw [hg, hf] at e
    have e2 : (MulAut.conj (C⁻¹ * Y)).toMonoidHom w' = w'' := by
      change C⁻¹ * Y * w' * (C⁻¹ * Y)⁻¹ = w''
      calc C⁻¹ * Y * w' * (C⁻¹ * Y)⁻¹ = C⁻¹ * (Y * w' * Y⁻¹) * C := by group
        _ = w'' := by rw [← e]; group
    rw [e2]
    exact hw''

end Pres

end CFSG.KC.F4Planes

end
