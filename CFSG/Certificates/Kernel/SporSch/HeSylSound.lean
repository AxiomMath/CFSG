module

public import Certificates.Data.Kernel.SporSch.HeSyl
public import CFSG.Certificates.Kernel.Spor.Loops
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

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

variable {P : Nat → Nat → Nat} {bs : List Nat}

theorem sylValB_spec {V : Nat → Bool} {m NF CJ : Nat} (h : sylValB V m NF CJ = true) :
    ∀ i < m, V (sylF80 NF i) = true ∧ V (sylF80 CJ i) = true :=
  fun i hi => (bAnd_iff _ _).1 (allN_spec h i hi)

theorem sylRngB_spec {m MT PAR GEN GI R : Nat} (h : sylRngB m MT PAR GEN GI R = true) :
    (∀ k < 3 * m, sylF5 MT k < m) ∧ (∀ i < m, sylF5 PAR i < m ∧ sylF5 GEN i < 3) ∧
      (∀ j < 3, sylF5 GI j < m) ∧ R < m := by
  unfold sylRngB at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h3
  refine ⟨fun k hk => Nat.le_of_ble_eq_true (allN_spec h1 k hk), fun i hi => ?_,
    fun j hj => Nat.le_of_ble_eq_true (allN_spec h3 j hj), Nat.le_of_ble_eq_true h4⟩
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec h2 i hi)
  exact ⟨Nat.le_of_ble_eq_true a, Nat.le_of_ble_eq_true b⟩

theorem sylMulB_spec {m NF MT GI j : Nat} (h : sylMulB P bs m NF MT GI j = true) :
    ∀ i < m, eqOnL bs (P (sylF80 NF (sylF5 MT (m * j + i))))
      (fun b => P (sylF80 NF i) (P (sylF80 NF (sylF5 GI j)) b)) = true :=
  fun i hi => allN_spec h i hi

theorem sylRootB_spec {NF R : Nat} (h : sylRootB P bs NF R = true) :
    eqOnL bs (P (sylF80 NF R)) (fun b => b) = true := h

theorem sylKey_congr {f g : Nat → Nat} (h : ∀ b ∈ bs, f b = g b) :
    sylKey bs f = sylKey bs g := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change Nat.lor (f b) (Nat.shiftLeft (sylKey bs f) 14) =
      Nat.lor (g b) (Nat.shiftLeft (sylKey bs g) 14)
    rw [h b List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem sylKeyB_lt {c NF : Nat} (h : sylKeyB P bs c NF = true) {i j : Nat} (hij : i < j)
    (hj : j ≤ c) : sylKey bs (P (sylF80 NF i)) < sylKey bs (P (sylF80 NF j)) := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hs : sylKey bs (P (sylF80 NF j)) < sylKey bs (P (sylF80 NF (j + 1))) :=
      Nat.le_of_ble_eq_true (allN_spec h j (by omega))
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h1 | rfl
    · exact (ih h1 (by omega)).trans hs
    · exact hs

theorem sylBeq_false {i R : Nat} (h : i ≠ R) : Nat.beq i R = false := by
  cases h' : Nat.beq i R
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true h') h

theorem sylTreeB_spec{m MT PAR GEN DEP R : Nat} (h : sylTreeB m MT PAR GEN DEP R = true) :
    ∀ i < m, i ≠ R → sylF5 DEP (sylF5 PAR i) < sylF5 DEP i ∧
      sylF5 MT (m * sylF5 GEN i + sylF5 PAR i) = i := by
  intro i hi hR
  have h1 := allN_spec h i hi
  beta_reduce at h1
  rw [sylBeq_false hR] at h1
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 h1
  exact ⟨Nat.le_of_ble_eq_true a, Nat.eq_of_beq_eq_true b⟩

theorem sylConjB_spec {YA YB : Nat → Nat} {m NF CJ CL R : Nat}
    (h : sylConjB P bs YA YB m NF CJ CL R = true) : ∀ i < m, i ≠ R →
      eqOnL bs (fun b => P (sylF80 CJ i) (P (sylF80 NF i) b))
          (fun b => YA (P (sylF80 CJ i) b)) = true ∨
        eqOnL bs (fun b => P (sylF80 CJ i) (P (sylF80 NF i) b))
          (fun b => YB (P (sylF80 CJ i) b)) = true := by
  intro i hi hR
  have h1 := allN_spec h i hi
  beta_reduce at h1
  rw [sylBeq_false hR] at h1
  revert h1
  generalize Nat.beq (fld(CL, i, nat_lit 1)) (nat_lit 1) = c
  cases c
  · exact Or.inl
  · exact Or.inr

section Group

variable {G : Type*} [Group G] [Finite G]

theorem exists_subgroup_of_tab {m r : ℕ} {T : ℕ → G} {g par gen dep : ℕ → ℕ} {M : ℕ → ℕ → ℕ}
    (hM : ∀ j < 3, ∀ i < m, M j i < m ∧ T i * T (g j) = T (M j i)) (hr : r < m) (h1 : T r = 1)
    (htree : ∀ i < m, i ≠ r → par i < m ∧ gen i < 3 ∧ dep (par i) < dep i ∧
      T i = T (par i) * T (g (gen i))) :
    ∃ S : Subgroup G, ∀ x, x ∈ S ↔ ∃ i < m, T i = x := by
  have hA : ∀ x, (∃ i < m, T i = x) → ∀ j < 3, ∃ k < m, T k = x * T (g j) := by
    rintro x ⟨i, hi, rfl⟩ j hj
    exact ⟨M j i, (hM j hj i hi).1, (hM j hj i hi).2.symm⟩
  have hB : ∀ d, ∀ i < m, dep i = d → ∀ y, (∃ k < m, T k = y) → ∃ k < m, T k = y * T i := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hi hd y hy
      by_cases hir : i = r
      · rw [hir, h1, mul_one]
        exact hy
      · obtain ⟨hp, hg, hdep, e⟩ := htree i hi hir
        obtain ⟨k, hk, ek⟩ := ih _ (by omega) (par i) hp rfl y hy
        obtain ⟨k', hk', ek'⟩ := hA _ ⟨k, hk, ek⟩ (gen i) hg
        exact ⟨k', hk', by rw [ek', e, mul_assoc]⟩
  have hmul : ∀ x y, (∃ i < m, T i = x) → (∃ i < m, T i = y) → ∃ i < m, T i = x * y := by
    rintro x y hx ⟨i, hi, rfl⟩
    exact hB _ i hi rfl x hx
  have hpow : ∀ x, (∃ i < m, T i = x) → ∀ n : ℕ, ∃ i < m, T i = x ^ n := by
    intro x hx n
    induction n with
    | zero => exact ⟨r, hr, by rw [h1, pow_zero]⟩
    | succ n ih => exact pow_succ x n ▸ hmul _ _ ih hx
  refine ⟨{ carrier := {x | ∃ i < m, T i = x}
            mul_mem' := fun hx hy => hmul _ _ hx hy
            one_mem' := ⟨r, hr, h1⟩
            inv_mem' := fun {x} hx => ?_ }, fun x => Iff.rfl⟩
  have e : x ^ (orderOf x - 1) = x⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
  change ∃ i < m, T i = x⁻¹
  rw [← e]
  exact hpow x hx _

theorem card_of_tab {m : ℕ} {T : ℕ → G} {S : Subgroup G} (hS : ∀ x, x ∈ S ↔ ∃ i < m, T i = x)
    (hinj : ∀ i < m, ∀ j < m, T i = T j → i = j) : Nat.card S = m := by
  have hb : Function.Bijective (fun i : Fin m => (⟨T i, (hS _).2 ⟨i, i.2, rfl⟩⟩ : S)) := by
    refine ⟨fun i j e => Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val e)), fun x => ?_⟩
    obtain ⟨i, hi, e⟩ := (hS x).1 x.2
    exact ⟨⟨i, hi⟩, Subtype.ext e⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fin]

end Group

end CFSG.KS.SporSch

end
