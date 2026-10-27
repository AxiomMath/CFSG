module

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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.Lin2.OddRank

open Matrix

theorem dvd_sq_sub_one_of_dvd_pow_sub_one {q ℓ k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2)
    (h : ℓ ∣ q ^ k - 1) : ℓ ∣ q ^ 2 - 1 := by
  obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
  · exact h.trans (by simpa using Nat.sub_one_dvd_pow_sub_one q 2)
  · exact h

section Fix

variable {F : Type} [Field F]

theorem gl_smul_def (g : GL (Fin 3) F) (v : Fin 3 → F) :
    g • v = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v := rfl

@[expose] def fixSpace (T : Subgroup (GL (Fin 3) F)) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ g ∈ T, g • v = v}
  zero_mem' := fun g _ => by rw [gl_smul_def, mulVec_zero]
  add_mem' := fun {a b} ha hb g hg => by
    rw [gl_smul_def, mulVec_add, ← gl_smul_def, ← gl_smul_def, ha g hg, hb g hg]
  smul_mem' := fun c v hv g hg => by
    rw [gl_smul_def, mulVec_smul, ← gl_smul_def, hv g hg]

@[expose] def fixVec (y : GL (Fin 3) F) : Submodule F (Fin 3 → F) where
  carrier := {v | y • v = v}
  zero_mem' := by
    show y • (0 : Fin 3 → F) = 0
    rw [gl_smul_def, mulVec_zero]
  add_mem' := fun {a b} ha hb => by
    have ha' : y • a = a := ha
    have hb' : y • b = b := hb
    show y • (a + b) = a + b
    rw [gl_smul_def, mulVec_add, ← gl_smul_def, ← gl_smul_def, ha', hb']
  smul_mem' := fun c v hv => by
    have hv' : y • v = v := hv
    show y • (c • v) = c • v
    rw [gl_smul_def, mulVec_smul, ← gl_smul_def, hv']

theorem eq_one_of_forall_smul_eq {g : GL (Fin 3) F} (h : ∀ v : Fin 3 → F, g • v = v) : g = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have := congrFun (h (Pi.single j 1)) i
  rw [gl_smul_def, mulVec_single_one] at this
  simpa [Units.val_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

end Fix

section Count

variable {F : Type} [Field F] [Finite F]

theorem natCard_modEq_fixVec {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {y : GL (Fin 3) F} (hy : y ^ ℓ = 1)
    (S : Submodule F (Fin 3 → F)) (hS : ∀ v ∈ S, y • v ∈ S) :
    Nat.card S ≡ Nat.card ↥(S ⊓ fixVec y) [MOD ℓ] := by
  classical
  have := Fintype.ofFinite S
  let f : Function.End S := fun w => ⟨y • w.1, hS _ w.2⟩
  have hf : ∀ k : ℕ, ∀ w : S, ((f ^ k : Function.End S) w).1 = (y ^ k) • w.1 := by
    intro k
    induction k with
    | zero =>
      intro w
      show w.1 = (y ^ 0) • w.1
      rw [pow_zero, one_smul]
    | succ k ih =>
      intro w
      show ((f^[k + 1]) w).1 = (y ^ (k + 1)) • w.1
      rw [Function.iterate_succ_apply', pow_succ', mul_smul]
      exact congrArg (fun u : Fin 3 → F => y • u) (ih w)
  have hfl : f ^ ℓ ^ 1 = 1 := by
    funext w
    apply Subtype.ext
    rw [pow_one]
    show ((f ^ ℓ : Function.End S) w).1 = w.1
    rw [hf, hy, one_smul]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := ℓ) (n := 1) hfl
  have hcard : Fintype.card f.fixedPoints = Nat.card ↥(S ⊓ fixVec y) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ?_
    refine
      { toFun := fun w => ⟨w.1.1, w.1.2, ?_⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, ?_⟩
        left_inv := fun w => rfl
        right_inv := fun v => rfl }
    · have := w.2
      exact congrArg Subtype.val this
    · exact Subtype.ext v.2.2
  have h1 : Nat.card S = Fintype.card S := Nat.card_eq_fintype_card
  rw [h1, ← hcard]
  exact hmod

end Count

section Main

variable {F : Type} [Field F] [Finite F]

theorem dvd_two_pow_sub_one_of_normalizes {m : ℕ} (hq : Nat.card F = 2 ^ m) (hm : 1 ≤ m) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {T : Subgroup (GL (Fin 3) F)} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    {y : GL (Fin 3) F} (hy1 : y ≠ 1) (hyℓ : y ^ ℓ = 1) (hn' : ∀ g ∈ T, y⁻¹ * g * y ∈ T) :
    ℓ ∣ 2 ^ (2 * m) - 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime ℓ (2 ^ m) :=
    Nat.Coprime.pow_right m ((Nat.coprime_primes hℓ Nat.prime_two).mpr hℓ2)
  have hq2 : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by rw [← pow_mul, mul_comm]
  have hcard : ∀ S : Submodule F (Fin 3 → F), Nat.card S = (2 ^ m) ^ Module.finrank F S := by
    intro S
    rw [Module.natCard_eq_pow_finrank (K := F) (V := S), hq]
  have hV : Module.finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
  set W := fixSpace T with hW
  obtain ⟨w, hwW, hw0⟩ : ∃ w ∈ W, w ≠ 0 := by
    have hdvd : 2 ∣ Nat.card (Fin 3 → F) := by
      rw [Nat.card_fun, hq, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have h0 : (0 : Fin 3 → F) ∈ MulAction.fixedPoints T (Fin 3 → F) := by
      intro g
      show (g : GL (Fin 3) F) • (0 : Fin 3 → F) = 0
      rw [gl_smul_def, mulVec_zero]
    obtain ⟨b, hb, hne⟩ :=
      hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 3 → F) hdvd h0
    exact ⟨b, fun g hg => hb ⟨g, hg⟩, fun h => hne h.symm⟩
  have hWtop : W < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hT1
    apply hg1
    apply Subtype.ext
    refine eq_one_of_forall_smul_eq (fun v => ?_)
    have : v ∈ W := by rw [htop]; trivial
    exact this g g.2
  have hWinv : ∀ v ∈ W, y • v ∈ W := by
    intro v hv g hg
    have h1 : g • (y • v) = y • ((y⁻¹ * g * y) • v) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      group
    rw [h1, hv _ (hn' g hg)]
  have hd1 : 1 ≤ Module.finrank F W := by
    have : Nontrivial W := ⟨⟨⟨w, hwW⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  have hd2 : Module.finrank F W ≤ 2 := by
    have := Submodule.finrank_lt hWtop.ne
    omega
  have hmain : ∀ k : ℕ, 1 ≤ k → k ≤ 2 → ℓ ∣ (2 ^ m) ^ k - 1 → ℓ ∣ 2 ^ (2 * m) - 1 :=
    fun k hk1 hk2 h => hq2 ▸ dvd_sq_sub_one_of_dvd_pow_sub_one hk1 hk2 h
  by_cases hfix : ∃ v : Fin 3 → F, v ≠ 0 ∧ y • v = v
  ·
    obtain ⟨v, hv0, hvy⟩ := hfix
    have hmod := natCard_modEq_fixVec hyℓ ⊤ (fun _ _ => trivial)
    rw [top_inf_eq] at hmod
    have hcardTop : Nat.card (⊤ : Submodule F (Fin 3 → F)) = (2 ^ m) ^ 3 := by
      rw [hcard, finrank_top, hV]
    rw [hcardTop, hcard] at hmod
    set e := Module.finrank F (fixVec y) with he
    have he1 : 1 ≤ e := by
      have : Nontrivial (fixVec y) :=
        ⟨⟨⟨v, hvy⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
      exact Module.finrank_pos
    have he2 : e ≤ 2 := by
      have hlt : fixVec y < ⊤ := by
        refine lt_top_iff_ne_top.mpr fun htop => hy1 (eq_one_of_forall_smul_eq (fun u => ?_))
        have : u ∈ fixVec y := by rw [htop]; trivial
        exact this
      have := Submodule.finrank_lt hlt.ne
      omega
    have hle : (2 ^ m) ^ e ≤ (2 ^ m) ^ 3 :=
      Nat.pow_le_pow_right (Nat.two_pow_pos m) (by omega)
    have hdvd : ℓ ∣ (2 ^ m) ^ 3 - (2 ^ m) ^ e := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have hfac : (2 ^ m) ^ 3 - (2 ^ m) ^ e = (2 ^ m) ^ e * ((2 ^ m) ^ (3 - e) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, show e + (3 - e) = 3 by omega]
    rw [hfac] at hdvd
    have hdvd' : ℓ ∣ (2 ^ m) ^ (3 - e) - 1 :=
      (Nat.Coprime.pow_right e hcop).dvd_of_dvd_mul_left hdvd
    exact hmain (3 - e) (by omega) (by omega) hdvd'
  ·
    have hmod := natCard_modEq_fixVec hyℓ W hWinv
    have hbot : W ⊓ fixVec y = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
      by_contra hv0
      exact hfix ⟨v, hv0, hv.2⟩
    rw [hbot, hcard] at hmod
    have h1 : Nat.card (⊥ : Submodule F (Fin 3 → F)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨inferInstance, inferInstance⟩
    rw [h1] at hmod
    have hle : 1 ≤ (2 ^ m) ^ Module.finrank F W :=
      Nat.one_le_pow _ _ (Nat.two_pow_pos m)
    have hdvd : ℓ ∣ (2 ^ m) ^ Module.finrank F W - 1 := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    exact hmain _ hd1 hd2 hdvd

end Main

end CFSG.QuasithinUnique.Lin2.OddRank
