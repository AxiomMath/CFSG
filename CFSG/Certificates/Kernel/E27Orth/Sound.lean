module

public import Certificates.Data.Kernel.E27Orth.Defs
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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

public section

namespace CFSG.KD.E27Orth

open CFSG.KC.Enum CFSG.KC.E27Orth Subgroup

theorem sB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bRec_ite (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem blt_iff (i k : ℕ) : Nat.blt i k = true ↔ i < k := by
  rw [Nat.blt_eq]

theorem beq_iff (i k : ℕ) : Nat.beq i k = true ↔ i = k :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h, Nat.beq_refl]⟩

theorem baseI_spec {cn : ℕ → Bool} {one m : ℕ} {G : ℕ → ℕ} (h : baseI cn one m G = true) :
    cn one = true ∧ ∀ j < m, cn (G j) = true := by
  unfold baseI at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  exact ⟨h1, CFSG.KS.allN_spec h2⟩

theorem treeI_spec {mul : ℕ → ℕ → ℕ} {cn : ℕ → Bool} {one m : ℕ} {G E Tr : ℕ → ℕ} {i : ℕ}
    (h : treeI mul cn one m G E Tr i = true) :
    cn (E i) = true ∧ (i = 0 → E i = one) ∧
      (i ≠ 0 → ∃ p j, p < i ∧ j < m ∧ E i = mul (G j) (E p)) := by
  unfold treeI at h
  simp only [sB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  rw [bRec_ite] at h2
  refine ⟨h1, fun h0 => ?_, fun h0 => ?_⟩
  · subst h0
    simpa [beq_iff] using h2
  · have hb : Nat.beq i 0 = false := by
      rw [Bool.eq_false_iff]
      exact fun e => h0 ((beq_iff _ _).1 e)
    rw [hb] at h2
    simp only [Bool.false_eq_true, ↓reduceIte] at h2
    obtain ⟨hp, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
    obtain ⟨hj, he⟩ := (CFSG.KS.bAnd_iff _ _).1 h3
    exact ⟨_, _, (blt_iff _ _).1 hp, (blt_iff _ _).1 hj, (beq_iff _ _).1 he⟩

theorem leftI_spec {mul : ℕ → ℕ → ℕ} {N : ℕ} {G E Lf : ℕ → ℕ} {j i : ℕ} (hi : i < N)
    (h : leftI mul N G E Lf (N * j + i) = true) :
    Lf (N * j + i) < N ∧ mul (G j) (E i) = E (Lf (N * j + i)) := by
  unfold leftI at h
  rw [sB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  have hN : 0 < N := by omega
  have e1 : Nat.div (N * j + i) N = j := by
    change (N * j + i) / N = j
    rw [Nat.mul_add_div hN, Nat.div_eq_of_lt hi, Nat.add_zero]
  have e2 : Nat.mod (N * j + i) N = i := by
    change (N * j + i) % N = i
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  rw [e1, e2] at h2
  exact ⟨(blt_iff _ _).1 h1, (beq_iff _ _).1 h2⟩

theorem keyI_spec {N : ℕ} {E S : ℕ → ℕ} {k : ℕ} (h : keyI N E S k = true) :
    S k < N ∧ (k + 1 < N → E (S k) < E (S (k + 1))) := by
  unfold keyI at h
  rw [sB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨(blt_iff _ _).1 h1, fun hk => ?_⟩
  rw [bRec_ite, if_pos ((blt_iff _ _).2 hk)] at h2
  exact (blt_iff _ _).1 h2

theorem conjI_spec {mul : ℕ → ℕ → ℕ} {N nR : ℕ} {E Rp W : ℕ → ℕ} {i : ℕ}
    (h : conjI mul N nR E Rp W i = true) :
    ∃ w r, w < N ∧ r < nR ∧ mul (E w) (E i) = mul (E (Rp r)) (E w) := by
  unfold conjI at h
  simp only [sB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
  exact ⟨_, _, (blt_iff _ _).1 h1, (blt_iff _ _).1 h3, (beq_iff _ _).1 h4⟩

theorem repI_spec {mul : ℕ → ℕ → ℕ} {cn : ℕ → Bool} {one N c0 : ℕ} {E Rp Cm : ℕ → ℕ} {r : ℕ}
    (h : repI mul cn one N c0 E Rp Cm r = true) :
    Rp r < N ∧
      (mul (E (Rp r)) (mul (E (Rp r)) (E (Rp r))) = one →
        ∀ t < c0, Cm (c0 * r + t) < N ∧
          (t + 1 < c0 → Cm (c0 * r + t) < Cm (c0 * r + (t + 1))) ∧
          mul (E (Cm (c0 * r + t))) (E (Rp r)) = mul (E (Rp r)) (E (Cm (c0 * r + t)))) ∧
      (mul (E (Rp r)) (mul (E (Rp r)) (E (Rp r))) ≠ one →
        cn (mul (E (Rp r)) (E (Rp r))) = true ∧
          cn (mul (E (Rp r)) (mul (E (Rp r)) (E (Rp r)))) = true) := by
  unfold repI at h
  simp only [sB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  rw [bRec_ite] at h2
  refine ⟨(blt_iff _ _).1 h1, fun hy t ht => ?_, fun hy => ?_⟩
  · rw [if_pos ((beq_iff _ _).2 hy)] at h2
    have hall := CFSG.KS.allN_spec h2
    have hs : ∀ u < c0, Cm (c0 * r + u) < N ∧
        (u ≠ 0 → Cm (c0 * r + u - 1) < Cm (c0 * r + u)) ∧
        mul (E (Cm (c0 * r + u))) (E (Rp r)) = mul (E (Rp r)) (E (Cm (c0 * r + u))) := by
      intro u hu
      have e := hall u hu
      obtain ⟨e1, e2⟩ := (CFSG.KS.bAnd_iff _ _).1 e
      obtain ⟨e3, e4⟩ := (CFSG.KS.bAnd_iff _ _).1 e2
      refine ⟨(blt_iff _ _).1 e1, fun hu0 => ?_, (beq_iff _ _).1 e4⟩
      have hb : Nat.beq u 0 = false := by
        rw [Bool.eq_false_iff]
        exact fun e => hu0 ((beq_iff _ _).1 e)
      rw [bRec_ite, hb] at e3
      simp only [Bool.false_eq_true, ↓reduceIte] at e3
      exact (blt_iff _ _).1 e3
    obtain ⟨a1, -, a3⟩ := hs t ht
    refine ⟨a1, fun ht1 => ?_, a3⟩
    have := (hs (t + 1) ht1).2.1 (by omega)
    simpa [Nat.add_assoc] using this
  · have hb : Nat.beq (mul (E (Rp r)) (mul (E (Rp r)) (E (Rp r)))) one = false := by
      rw [Bool.eq_false_iff]
      exact fun e => hy ((beq_iff _ _).1 e)
    rw [hb] at h2
    simp only [Bool.false_eq_true, ↓reduceIte] at h2
    exact (CFSG.KS.bAnd_iff _ _).1 h2

theorem inj_of_keys {N : ℕ} {E S : ℕ → ℕ} (h : ∀ k < N, keyI N E S k = true) :
    ∀ i < N, ∀ k < N, E i = E k → i = k := by
  have hS := fun k hk => keyI_spec (h k hk)
  have mono : ∀ a b, a < b → b < N → E (S a) < E (S b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      have hstep := (hS b (by omega)).2 hb
      rcases Nat.lt_or_ge a b with h' | h'
      · exact lt_trans (ih h' (by omega)) hstep
      · have : a = b := by omega
        subst this
        exact hstep
  have hinjS : ∀ a < N, ∀ b < N, S a = S b → a = b := by
    intro a ha b hb e
    rcases Nat.lt_trichotomy a b with h' | h' | h'
    · exact absurd (congrArg E e) (Nat.ne_of_lt (mono a b h' hb))
    · exact h'
    · exact absurd (congrArg E e).symm (Nat.ne_of_lt (mono b a h' ha))
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range N) (t := Finset.range N)
    (fun a _ => S a) (fun a ha => Finset.mem_range.2 (hS a (Finset.mem_range.1 ha)).1)
    (fun a b ha hb e => hinjS a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e) le_rfl
  intro i hi k hk e
  obtain ⟨a, ha, rfl⟩ := hsurj i (Finset.mem_range.2 hi)
  obtain ⟨b, hb, rfl⟩ := hsurj k (Finset.mem_range.2 hk)
  rw [Finset.mem_range] at ha hb
  rw [hinjS a ha b hb (by
    rcases Nat.lt_trichotomy a b with h' | h' | h'
    · exact absurd e (Nat.ne_of_lt (mono a b h' hb))
    · rw [h']
    · exact absurd e.symm (Nat.ne_of_lt (mono b a h' ha)))]

section Tab

variable {H : Type*} [Group H] {M : Type*} [Monoid M]

structure Enc (dec : ℕ → M) (mul : ℕ → ℕ → ℕ) (cn : ℕ → Bool) : Prop where
  hmul : ∀ a b, cn a = true → cn b = true → dec (mul a b) = dec a * dec b
  hinj : ∀ a b, cn a = true → cn b = true → dec a = dec b → a = b

abbrev gS (m : ℕ) (g : ℕ → H) : Subgroup H := Subgroup.closure {x | ∃ j < m, g j = x}

variable {ρ : H →* M} {dec : ℕ → M} {mul : ℕ → ℕ → ℕ} {cn : ℕ → Bool} {one m N : ℕ}
  {g : ℕ → H} {G E Tr S : ℕ → ℕ}

theorem tab_tree (henc : Enc dec mul cn) (hρ : Function.Injective ρ) (hone : dec one = 1)
    (hg : ∀ j < m, ρ (g j) = dec (G j)) (hbase : baseI cn one m G = true)
    (htree : ∀ i < N, treeI mul cn one m G E Tr i = true) (hkey : ∀ k < N, keyI N E S k = true) :
    ∃ X : ℕ → H, (∀ i < N, X i ∈ gS m g ∧ ρ (X i) = dec (E i)) ∧
      ∀ i < N, ∀ k < N, X i = X k → i = k := by
  have hcnG := (baseI_spec hbase).2
  have hex : ∀ i < N, ∃ x ∈ gS m g, ρ x = dec (E i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      obtain ⟨-, h0, hs⟩ := treeI_spec (htree i hi)
      by_cases hi0 : i = 0
      · refine ⟨1, one_mem _, ?_⟩
        rw [map_one, h0 hi0, hone]
      · obtain ⟨p, j, hp, hj, he⟩ := hs hi0
        obtain ⟨x, hx, hxe⟩ := ih p hp (by omega)
        refine ⟨g j * x, mul_mem (subset_closure ⟨j, hj, rfl⟩) hx, ?_⟩
        rw [map_mul, hg j hj, hxe, he, henc.hmul _ _ (hcnG j hj) (treeI_spec (htree p (by omega))).1]
  classical
  refine ⟨fun i => if h : i < N then (hex i h).choose else 1, fun i hi => ?_, fun i hi k hk e => ?_⟩
  · simp only [dif_pos hi]
    exact (hex i hi).choose_spec
  · simp only [dif_pos hi, dif_pos hk] at e
    have e2 : dec (E i) = dec (E k) := by
      rw [← (hex i hi).choose_spec.2, ← (hex k hk).choose_spec.2, e]
    exact inj_of_keys hkey i hi k hk (henc.hinj _ _ (treeI_spec (htree i hi)).1
      (treeI_spec (htree k hk)).1 e2)

theorem tab_left [Finite H] {Lf : ℕ → ℕ} (henc : Enc dec mul cn) (hρ : Function.Injective ρ)
    (hone : dec one = 1) (hN : 0 < N)
    (hg : ∀ j < m, ρ (g j) = dec (G j)) (hbase : baseI cn one m G = true)
    (htree : ∀ i < N, treeI mul cn one m G E Tr i = true)
    (hleft : ∀ j < m, ∀ i < N, leftI mul N G E Lf (N * j + i) = true) {X : ℕ → H}
    (hX : ∀ i < N, X i ∈ gS m g ∧ ρ (X i) = dec (E i)) :
    ∀ x ∈ gS m g, ∃ i < N, X i = x := by
  have hcnG := (baseI_spec hbase).2
  let P : H → Prop := fun y => ∃ i < N, ρ y = dec (E i)
  have hstep : ∀ j < m, ∀ y, P y → P (g j * y) := by
    rintro j hj y ⟨i, hi, hy⟩
    obtain ⟨hk, he⟩ := leftI_spec hi (hleft j hj i hi)
    refine ⟨_, hk, ?_⟩
    rw [map_mul, hg j hj, hy, ← he, henc.hmul _ _ (hcnG j hj) (treeI_spec (htree i hi)).1]
  have hpow : ∀ j < m, ∀ y, P y → ∀ k : ℕ, P (g j ^ k * y) := by
    intro j hj y hy k
    induction k with
    | zero => simpa using hy
    | succ k ih =>
      rw [pow_succ', mul_assoc]
      exact hstep j hj _ ih
  intro x hx
  have hP : P x := by
    induction hx using Subgroup.closure_induction_left with
    | one => exact ⟨0, hN, by rw [map_one, (treeI_spec (htree 0 hN)).2.1 rfl, hone]⟩
    | mul_left a ha y _ ih =>
      obtain ⟨j, hj, rfl⟩ := ha
      exact hstep j hj y ih
    | inv_mul_cancel a ha y _ ih =>
      obtain ⟨j, hj, rfl⟩ := ha
      have e : (g j)⁻¹ = g j ^ (orderOf (g j) - 1) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos _),
          pow_orderOf_eq_one]
      rw [e]
      exact hpow j hj y ih _
  obtain ⟨i, hi, hxe⟩ := hP
  exact ⟨i, hi, hρ ((hX i hi).2.trans hxe.symm)⟩

theorem tab_bound [Finite H] {T : Subgroup H} {X : ℕ → H} (hcard : Nat.card T ≤ N)
    (hX : ∀ i < N, X i ∈ T) (hinj : ∀ i < N, ∀ k < N, X i = X k → i = k) :
    ∀ x ∈ T, ∃ i < N, X i = x := by
  let f : Fin N → T := fun i => ⟨X i, hX i i.2⟩
  have hf : Function.Injective f := fun a b e =>
    Fin.ext (hinj a a.2 b b.2 (congrArg Subtype.val e))
  have hb := hf.bijective_of_nat_card_le (by simpa using hcard)
  intro x hx
  obtain ⟨i, hi⟩ := hb.2 ⟨x, hx⟩
  exact ⟨i, i.2, congrArg Subtype.val hi⟩

theorem card_of_tab {T : Subgroup H} {X : ℕ → H} (hX : ∀ i < N, X i ∈ T)
    (hinj : ∀ i < N, ∀ k < N, X i = X k → i = k) (hsurj : ∀ x ∈ T, ∃ i < N, X i = x) :
    Nat.card T = N := by
  have hb : Function.Bijective fun i : Fin N => (⟨X i, hX i i.2⟩ : T) := by
    refine ⟨fun a b e => Fin.ext (hinj a a.2 b b.2 (congrArg Subtype.val e)), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨i, hi, rfl⟩ := hsurj x hx
    exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_cent_conj {T : Subgroup H} {u x y : H} (hu : u ∈ T) (e : u * x = y * u) :
    Nat.card ↥(T ⊓ centralizer ({x} : Set H)) = Nat.card ↥(T ⊓ centralizer ({y} : Set H)) := by
  have hy : y = u * x * u⁻¹ := by rw [e, mul_inv_cancel_right]
  subst hy
  refine Nat.card_congr
    { toFun := fun z => ⟨u * z * u⁻¹, ?_⟩
      invFun := fun z => ⟨u⁻¹ * z * u, ?_⟩
      left_inv := fun z => by ext; simp [mul_assoc]
      right_inv := fun z => by ext; simp [mul_assoc] }
  · obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.1 z.2
    refine Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem hu hzT) (T.inv_mem hu), ?_⟩
    rw [mem_centralizer_singleton_iff] at hzC ⊢
    calc u * z * u⁻¹ * (u * x * u⁻¹) = u * (z * x) * u⁻¹ := by group
      _ = u * (x * z) * u⁻¹ := by rw [hzC]
      _ = u * x * u⁻¹ * (u * z * u⁻¹) := by group
  · obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.1 z.2
    refine Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem (T.inv_mem hu) hzT) hu, ?_⟩
    rw [mem_centralizer_singleton_iff] at hzC ⊢
    calc u⁻¹ * z * u * x = u⁻¹ * (z * (u * x * u⁻¹)) * u := by group
      _ = u⁻¹ * (u * x * u⁻¹ * z) * u := by rw [hzC]
      _ = x * (u⁻¹ * z * u) := by group

theorem kill_sound [Finite H] {T : Subgroup H} {X : ℕ → H} {nR c0 : ℕ} {Rp W Cm : ℕ → ℕ}
    (henc : Enc dec mul cn) (hρ : Function.Injective ρ) (hone : dec one = 1)
    (hcone : cn one = true) (hcnE : ∀ i < N, cn (E i) = true)
    (hX : ∀ i < N, X i ∈ T ∧ ρ (X i) = dec (E i)) (hinj : ∀ i < N, ∀ k < N, X i = X k → i = k)
    (hsurj : ∀ x ∈ T, ∃ i < N, X i = x)
    (hconj : ∀ i < N, conjI mul N nR E Rp W i = true)
    (hrep : ∀ r < nR, repI mul cn one N c0 E Rp Cm r = true) :
    ∀ s ∈ T, s ^ 3 = 1 → c0 ≤ Nat.card ↥(T ⊓ centralizer ({s} : Set H)) := by
  have hρmul : ∀ i < N, ∀ k < N, ρ (X i * X k) = dec (mul (E i) (E k)) := by
    intro i hi k hk
    rw [map_mul, (hX i hi).2, (hX k hk).2, henc.hmul _ _ (hcnE i hi) (hcnE k hk)]
  have hmulEq : ∀ a < N, ∀ b < N, ∀ c < N, ∀ d < N, mul (E a) (E b) = mul (E c) (E d) →
      X a * X b = X c * X d := by
    intro a ha b hb c hc d hd e
    exact hρ (by rw [hρmul a ha b hb, hρmul c hc d hd, e])
  intro s hs hs3
  obtain ⟨i, hi, rfl⟩ := hsurj s hs
  obtain ⟨w, r, hw, hr, he⟩ := conjI_spec (hconj i hi)
  obtain ⟨ha, hcube, hncube⟩ := repI_spec (hrep r hr)
  set a := Rp r
  have hc := hmulEq w hw i hi a ha w hw he
  rw [card_cent_conj (hX w hw).1 hc]
  have ha3 : X a ^ 3 = 1 := by
    have : X a = X w * X i * (X w)⁻¹ := by rw [hc, mul_inv_cancel_right]
    rw [this, conj_pow, hs3, mul_one, mul_inv_cancel]
  by_cases hy : mul (E a) (mul (E a) (E a)) = one
  · have hw' := hcube hy
    let f : Fin c0 → ↥(T ⊓ centralizer ({X a} : Set H)) := fun t =>
      ⟨X (Cm (c0 * r + t)), Subgroup.mem_inf.2 ⟨(hX _ (hw' t t.2).1).1,
        mem_centralizer_singleton_iff.2 (hmulEq _ (hw' t t.2).1 _ ha _ ha _ (hw' t t.2).1
          (hw' t t.2).2.2)⟩⟩
    have mono : ∀ t t', t < t' → t' < c0 → Cm (c0 * r + t) < Cm (c0 * r + t') := by
      intro t t' htt ht'
      induction t' with
      | zero => omega
      | succ t' ih =>
        have hstep := (hw' t' (by omega)).2.1 ht'
        rcases Nat.lt_or_ge t t' with h' | h'
        · exact lt_trans (ih h' (by omega)) hstep
        · have : t = t' := by omega
          subst this
          exact hstep
    have hf : Function.Injective f := by
      intro t t' e
      have e' := hinj _ (hw' t t.2).1 _ (hw' t' t'.2).1 (congrArg Subtype.val e)
      apply Fin.ext
      rcases Nat.lt_trichotomy t.val t'.val with h' | h' | h'
      · exact absurd e' (Nat.ne_of_lt (mono _ _ h' t'.2))
      · exact h'
      · exact absurd e'.symm (Nat.ne_of_lt (mono _ _ h' t.2))
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  · obtain ⟨hc2, hc3⟩ := hncube hy
    exfalso
    apply hy
    refine henc.hinj _ _ hc3 hcone ?_
    rw [henc.hmul _ _ (hcnE a ha) hc2, henc.hmul _ _ (hcnE a ha) (hcnE a ha), hone,
      ← (hX a ha).2, ← map_mul, ← map_mul, ← pow_three, ha3, map_one]

theorem dvd81_of_le {T K : Subgroup H} {k : ℕ} (hT : Nat.card T = 3 ^ k) (hK : K ≤ T)
    (h81 : 81 ≤ Nat.card K) : 81 ∣ Nat.card K := by
  have hd : Nat.card K ∣ 3 ^ k := hT ▸ Subgroup.card_dvd_of_le hK
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  rw [ha] at h81 ⊢
  have h4 : 4 ≤ a := by
    by_contra h
    have : 3 ^ a ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (Nat.pow_dvd_pow 3 h4 : 3 ^ 4 ∣ 3 ^ a)

end Tab

open CFSG.KC.Misc.Spec (pkMat pkMat_mulF2) in
theorem pkMat_inj {n a b : ℕ} (ha : a < 2 ^ (n * n)) (hb : b < 2 ^ (n * n))
    (h : pkMat n a = pkMat n b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rcases Nat.lt_or_ge k (n * n) with hk | hk
  · have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        simp at hk
      · exact h0
    have hi : k / n < n := by
      rw [Nat.div_lt_iff_lt_mul hn]
      exact hk
    have hj : k % n < n := Nat.mod_lt _ hn
    have e := congrFun (congrFun h ⟨k / n, hi⟩) ⟨k % n, hj⟩
    simp only [pkMat, Matrix.of_apply, Nat.div_add_mod] at e
    by_cases h1 : a.testBit k <;> by_cases h2 : b.testBit k <;> simp_all
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hk)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hk))]

theorem cnF2_iff (n x : ℕ) : cnF2 n x = true ↔ x < 2 ^ (n * n) := by
  unfold cnF2
  rw [blt_iff, CFSG.KC.Misc.Spec.shl1_eq, Nat.mul_eq]

theorem encF2 (n : ℕ) :
    Enc (CFSG.KC.Misc.Spec.pkMat n) (CFSG.KC.Misc.G24.mulF2 n) (cnF2 n) where
  hmul a b _ _ := CFSG.KC.Misc.Spec.pkMat_mulF2 n a b
  hinj a b ha hb h := pkMat_inj ((cnF2_iff n a).1 ha) ((cnF2_iff n b).1 hb) h

end CFSG.KD.E27Orth

end
