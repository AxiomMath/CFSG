module

public import Certificates.Data.Kernel.Misc.Coset.ActOrbit
public import CFSG.Certificates.Kernel.Common.ChainBound
public import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Bitwise
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.MiscCoset.Act

open Equiv

theorem orb_andB {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem forceB_eq (y : ℕ) (k : ℕ → Bool) : forceB y k = k y := by
  cases y <;> rfl

theorem memB_spec {c : ℕ} : ∀ {l : List ℕ}, memB c l = true → c ∈ l
  | [], h => absurd h Bool.false_ne_true
  | a :: l, h => by
    change Bool.rec (memB c l) true (Nat.beq a c) = true at h
    cases hb : Nat.beq a c
    · rw [hb] at h
      exact List.mem_cons_of_mem _ (memB_spec h)
    · rw [Nat.eq_of_beq_eq_true hb]
      exact List.mem_cons_self

theorem bitB_iff (s q : ℕ) : bitB s q = true ↔ s.testBit q = true := by
  have e : Nat.land (Nat.shiftRight s q) 1 = s / 2 ^ q % 2 := by
    rw [← Nat.shiftRight_eq_div_pow]
    exact Nat.and_one_is_mod _
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff, ← e, bitB]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h]; rfl⟩

theorem testBit_set (s p q : ℕ) :
    (Nat.lor s (Nat.shiftLeft 1 p)).testBit q = true ↔ s.testBit q = true ∨ q = p := by
  have e : Nat.lor s (Nat.shiftLeft 1 p) = s ||| 2 ^ p := by
    rw [← one_mul (2 ^ p), ← Nat.shiftLeft_eq]
    rfl
  rw [e, Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_iff]
  exact or_congr Iff.rfl eq_comm

theorem testBit_one_shiftLeft (p q : ℕ) : (Nat.shiftLeft 1 p).testBit q = true ↔ q = p := by
  have e : Nat.shiftLeft 1 p = 2 ^ p := by
    rw [← one_mul (2 ^ p), ← Nat.shiftLeft_eq]
    rfl
  rw [e, Nat.testBit_two_pow, decide_eq_true_iff, eq_comm]

theorem fixPts_spec {A : ℕ → ℕ} {L c : ℕ} : ∀ {bs : List ℕ},
    List.rec (motive := fun _ => Bool) true
      (fun b _ ih2 => andB (Nat.beq (step A L b c) b) ih2) bs = true →
    ∀ b ∈ bs, step A L b c = b
  | [], _, b, hb => absurd hb List.not_mem_nil
  | b' :: bs, h, b, hb => by
    obtain ⟨h1, h2⟩ := orb_andB h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact Nat.eq_of_beq_eq_true h1
    · exact fixPts_spec h2 b hb

theorem lvFix_spec {A : ℕ → ℕ} {L : ℕ} {bs : List ℕ} : ∀ {J : List ℕ},
    lvFix A L J bs = true → ∀ c ∈ J, c < L ∧ ∀ b ∈ bs, step A L b c = b
  | [], _, c, hc => absurd hc List.not_mem_nil
  | c' :: J, h, c, hc => by
    obtain ⟨h1, h⟩ := orb_andB h
    obtain ⟨h2, h3⟩ := orb_andB h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨Nat.le_of_ble_eq_true h1, fixPts_spec h2⟩
    · exact lvFix_spec h3 c hc

theorem rowsOK_spec {A B : ℕ → ℕ} {L M x : ℕ} : ∀ {ws : List (List ℕ)} {k : ℕ},
    rowsOK A L B M ws x k = true → ∀ j (hj : j < ws.length), walk A L ws[j] x = B (x * M + (k + j))
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | w :: ws, k, h, j, hj => by
    obtain ⟨h1, h2⟩ := orb_andB h
    cases j with
    | zero => exact Nat.eq_of_beq_eq_true h1
    | succ j =>
      rw [List.getElem_cons_succ, rowsOK_spec h2 j (by simpa using hj)]
      congr 1
      omega

variable {N L : ℕ} {A : ℕ → ℕ} {G : Type*} [Group G]
  (χ : G →* (Perm {c : ℕ // c < N})ᵐᵒᵖ) (σ : ℕ → G)

@[expose] def FixK (bs : List ℕ) : Set (Perm {c : ℕ // c < N})ᵐᵒᵖ :=
  {v | v ∈ χ.range ∧ ∀ x : {c : ℕ // c < N}, x.1 ∈ bs → v.unop x = x}

theorem one_mem_fixK (bs : List ℕ) : 1 ∈ FixK χ bs := ⟨χ.range.one_mem, fun _ _ => rfl⟩

theorem mul_mem_fixK {bs : List ℕ} {v w : (Perm {c : ℕ // c < N})ᵐᵒᵖ} (hv : v ∈ FixK χ bs)
    (hw : w ∈ FixK χ bs) : v * w ∈ FixK χ bs :=
  ⟨χ.range.mul_mem hv.1 hw.1, fun x hx => by
    rw [MulOpposite.unop_mul, Perm.mul_apply, hv.2 x hx, hw.2 x hx]⟩

@[expose] def Reach (bs : List ℕ) {b : ℕ} (hb : b < N) (q : ℕ) : Prop :=
  q < N ∧ ∃ v ∈ FixK χ bs, (v.unop ⟨b, hb⟩).1 = q

variable {χ σ}

theorem recOK_spec (hL : 0 < L)
    (hσ : ∀ c < L, ∀ x : {c : ℕ // c < N}, ((χ (σ c)).unop x).1 = A (x.1 * L + c))
    {J bs : List ℕ} (hJ : ∀ c ∈ J, χ (σ c) ∈ FixK χ bs) {b : ℕ} (hb : b < N) :
    ∀ (O : List ℕ) (s : ℕ), recOK A L N J O s = true →
      (∀ q, s.testBit q = true → Reach χ bs hb q) →
      ∃ ps : List ℕ, ps.length = O.length ∧ ps.Nodup ∧ (∀ q ∈ ps, s.testBit q = false) ∧
        ∀ q ∈ ps, Reach χ bs hb q
  | [], _, _, _ => ⟨[], rfl, List.nodup_nil, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩
  | e :: O, s, h, hs => by
    change forceB (A e) (fun p => andB (memB (Nat.mod e L) J) (andB (bitB s (Nat.div e L))
      (andB (Nat.blt p N) (andB (notB (bitB s p))
        (forceB (Nat.lor s (Nat.shiftLeft 1 p)) (recOK A L N J O)))))) = true at h
    rw [forceB_eq] at h
    beta_reduce at h
    rw [forceB_eq] at h
    obtain ⟨h1, h⟩ := orb_andB h
    obtain ⟨h2, h⟩ := orb_andB h
    obtain ⟨h3, h⟩ := orb_andB h
    obtain ⟨h4, h5⟩ := orb_andB h
    have hc : e % L ∈ J := memB_spec h1
    obtain ⟨hpN, v, hv, hvb⟩ := hs _ ((bitB_iff _ _).1 h2)
    have heN : A e < N := Nat.le_of_ble_eq_true h3
    have h4' : s.testBit (A e) = false := by
      cases hh : bitB s (A e)
      · cases ht : s.testBit (A e)
        · rfl
        · rw [(bitB_iff _ _).2 ht] at hh
          exact absurd hh (by decide)
      · rw [hh] at h4
        exact absurd h4 Bool.false_ne_true
    have hre : Reach χ bs hb (A e) := by
      refine ⟨heN, v * χ (σ (e % L)), mul_mem_fixK χ hv (hJ _ hc), ?_⟩
      rw [MulOpposite.unop_mul, Perm.mul_apply]
      have hx : v.unop ⟨b, hb⟩ = ⟨e / L, hpN⟩ := Subtype.ext hvb
      rw [hx, hσ _ (Nat.mod_lt _ hL), Nat.div_add_mod']
    obtain ⟨ps, hlen, hnd, hav, hr⟩ := recOK_spec hL hσ hJ hb O _ h5 (fun q hq => by
      rcases (testBit_set _ _ _).1 hq with hq | rfl
      · exact hs q hq
      · exact hre)
    refine ⟨A e :: ps, by rw [List.length_cons, List.length_cons, hlen], ?_, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩
      have := hav _ hm
      rw [(testBit_set _ _ _).2 (Or.inr rfl)] at this
      exact absurd this (by decide)
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h4'
      · have := hav q hq
        cases hh : s.testBit q
        · rfl
        · rw [(testBit_set _ _ _).2 (Or.inl hh)] at this
          exact absurd this (by decide)
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hre
      · exact hr q hq

@[expose] def actOp (g : (Perm {c : ℕ // c < N})ᵐᵒᵖ) (x : {c : ℕ // c < N}) :
    {c : ℕ // c < N} :=
  (g⁻¹).unop x

theorem actOp_mul (g h : (Perm {c : ℕ // c < N})ᵐᵒᵖ) (x : {c : ℕ // c < N}) :
    actOp (g * h) x = actOp g (actOp h x) := by
  rw [actOp, actOp, actOp, mul_inv_rev, MulOpposite.unop_mul, Perm.mul_apply]

theorem actOp_one (x : {c : ℕ // c < N}) : actOp 1 x = x := rfl

theorem levelsOK_spec (hL : 0 < L)
    (hσ : ∀ c < L, ∀ x : {c : ℕ // c < N}, ((χ (σ c)).unop x).1 = A (x.1 * L + c)) :
    ∀ (levels : List (ℕ × List ℕ × List ℕ)) (bs : List ℕ), levelsOK A L N levels bs = true →
      ∃ Lst : List ({c : ℕ // c < N} × List (Perm {c : ℕ // c < N})ᵐᵒᵖ),
        Lst.map (fun l => l.2.length) = levels.map (fun l => l.2.2.length + 1) ∧
        StabChain.ChainOK actOp χ.range Lst ∧
        ∀ l ∈ Lst, ∀ t ∈ l.2, ∀ x : {c : ℕ // c < N}, x.1 ∈ bs → actOp t x = x
  | [], _, _ => ⟨[], rfl, trivial, fun _ h => absurd h List.not_mem_nil⟩
  | (b, J, O) :: levels, bs, h => by
    classical
    change andB (Nat.blt b N) (andB (lvFix A L J bs)
      (andB (recOK A L N J O (Nat.shiftLeft 1 b)) (levelsOK A L N levels (b :: bs)))) = true at h
    obtain ⟨h1, h⟩ := orb_andB h
    obtain ⟨h2, h⟩ := orb_andB h
    obtain ⟨h3, h4⟩ := orb_andB h
    have hb : b < N := Nat.le_of_ble_eq_true h1
    have hJ : ∀ c ∈ J, χ (σ c) ∈ FixK χ bs := fun c hc => by
      obtain ⟨hcL, hfix⟩ := lvFix_spec h2 c hc
      exact ⟨⟨σ c, rfl⟩, fun x hx => Subtype.ext ((hσ c hcL x).trans (hfix _ hx))⟩
    have hb0 : Reach χ bs hb b := ⟨hb, 1, one_mem_fixK χ bs, rfl⟩
    obtain ⟨ps, hlen, hnd, hav, hr⟩ := recOK_spec hL hσ hJ hb O _ h3 (fun q hq => by
      rw [(testBit_one_shiftLeft _ _).1 hq]
      exact hb0)
    obtain ⟨Lst, hLlen, hLc, hLfix⟩ := levelsOK_spec hL hσ levels (b :: bs) h4
    have hreach : ∀ q ∈ b :: ps, Reach χ bs hb q := fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hb0
      · exact hr q hq
    let pick : ℕ → (Perm {c : ℕ // c < N})ᵐᵒᵖ := fun q =>
      if h : Reach χ bs hb q then Classical.choose h.2 else 1
    have hpick : ∀ q ∈ b :: ps, pick q ∈ FixK χ bs ∧ ((pick q).unop ⟨b, hb⟩).1 = q :=
      fun q hq => by
        have h := hreach q hq
        simp only [pick, dif_pos h]
        exact Classical.choose_spec h.2
    have hact : ∀ q, actOp (pick q)⁻¹ = (pick q).unop := fun q => by
      funext x
      rw [actOp, inv_inv]
    let T := (b :: ps).map fun q => (pick q)⁻¹
    refine ⟨(⟨b, hb⟩, T) :: Lst, ?_, ⟨?_, ?_, ?_, hLc⟩, ?_⟩
    · rw [List.map_cons, List.map_cons, hLlen, List.length_map, List.length_cons, hlen]
    · intro t ht
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ht
      exact χ.range.inv_mem (hpick q hq).1.1
    · refine List.Nodup.of_map Subtype.val ?_
      have e : ((T.map fun t => actOp t ⟨b, hb⟩).map Subtype.val) = b :: ps := by
        rw [List.map_map, List.map_map]
        conv_rhs => rw [← List.map_id (b :: ps)]
        refine List.map_congr_left fun q hq => ?_
        simp only [Function.comp_apply, hact, id]
        exact (hpick q hq).2
      rw [e]
      have hb' : b ∉ ps := fun hm => by
        have := hav b hm
        rw [(testBit_one_shiftLeft _ _).2 rfl] at this
        exact absurd this (by decide)
      exact List.nodup_cons.2 ⟨hb', hnd⟩
    · intro l hl t ht
      exact hLfix l hl t ht ⟨b, hb⟩ List.mem_cons_self
    · intro l hl t ht x hx
      rcases List.mem_cons.1 hl with rfl | hl
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ht
        rw [hact]
        exact (hpick q hq).1.2 x hx
      · exact hLfix l hl t ht x (List.mem_cons_of_mem _ hx)

theorem finite_subtype_lt (N : ℕ) : Finite {c : ℕ // c < N} :=
  Finite.of_equiv _ Fin.equivSubtype

theorem le_card_range_of_levelsOK (hL : 0 < L)
    (hσ : ∀ c < L, ∀ x : {c : ℕ // c < N}, ((χ (σ c)).unop x).1 = A (x.1 * L + c))
    (levels : List (ℕ × List ℕ × List ℕ)) (h : levelsOK A L N levels [] = true) :
    (levels.map fun l => l.2.2.length + 1).prod ≤ Nat.card χ.range := by
  have := finite_subtype_lt N
  have : Finite (Perm {c : ℕ // c < N})ᵐᵒᵖ := Finite.of_equiv _ MulOpposite.opEquiv
  obtain ⟨Lst, hlen, hc, -⟩ := levelsOK_spec hL hσ levels [] h
  have := StabChain.prod_le_card_of_chainOK actOp actOp_mul actOp_one χ.range Lst hc
  rwa [hlen] at this

end CFSG.KC.MiscCoset.Act

end
