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
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public noncomputable section

namespace CFSG.LieType.Chevalley.ExteriorCube

open exteriorPower Set

variable {R : Type*} [CommRing R] {n k : ℕ}

abbrev wedgeBasis (I : powersetCard (Fin n) k) : ⋀[R]^k (Fin n → R) :=
  ιMulti_family R k (fun i : Fin n => (Pi.single i 1 : Fin n → R)) I

theorem wedgeBasis_eq_basis (I : powersetCard (Fin n) k) :
    wedgeBasis (R := R) I = (Pi.basisFun R (Fin n)).exteriorPower k I := by
  have h : (fun i : Fin n => (Pi.single i 1 : Fin n → R)) = ⇑(Pi.basisFun R (Fin n)) := by
    funext i
    exact (Pi.basisFun_apply R (Fin n) i).symm
  rw [exteriorPower.basis_apply, ← h]

abbrev transvLin (a b : Fin n) (c : R) : (Fin n → R) →ₗ[R] (Fin n → R) :=
  Matrix.toLin' (Matrix.transvection a b c)

theorem transvLin_single (a b m : Fin n) (c : R) :
    transvLin a b c (Pi.single m 1) = Pi.single m 1 + if m = b then c • Pi.single a 1 else 0 := by
  rw [Matrix.toLin'_apply, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_single_one]
  congr 1
  funext i
  by_cases hm : m = b
  · subst hm
    by_cases hi : i = a
    · subst hi
      simp
    · simp [Ne.symm hi, hi]
  · simp [hm, Ne.symm hm]

abbrev enum (I : powersetCard (Fin n) k) : Fin k ↪o Fin n :=
  powersetCard.ofFinEmbEquiv.symm I

theorem enum_mem (I : powersetCard (Fin n) k) (t : Fin k) : enum I t ∈ I.val :=
  (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I _).mp ⟨t, rfl⟩

theorem exists_enum_eq {I : powersetCard (Fin n) k} {b : Fin n} (hb : b ∈ I.val) :
    ∃ t, enum I t = b := by
  obtain ⟨t, ht⟩ := (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I b).mpr hb
  exact ⟨t, ht⟩

theorem card_insert_erase {I : powersetCard (Fin n) k} {a b : Fin n} (hb : b ∈ I.val)
    (ha : a ∉ I.val) : (insert a (I.val.erase b)).card = k := by
  rw [Finset.card_insert_of_notMem (fun h => ha (Finset.mem_of_mem_erase h)),
    Finset.card_erase_of_mem hb, I.prop]
  have : 0 < k := by
    rw [← I.prop]
    exact Finset.card_pos.mpr ⟨b, hb⟩
  omega

abbrev replace (I : powersetCard (Fin n) k) {a b : Fin n} (hb : b ∈ I.val) (ha : a ∉ I.val) :
    powersetCard (Fin n) k :=
  ⟨insert a (I.val.erase b), card_insert_erase hb ha⟩

theorem update_enum_eq {I : powersetCard (Fin n) k} {a b : Fin n}
    (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val) (hb : b ∈ I.val) (ha : a ∉ I.val) {t₀ : Fin k}
    (ht₀ : enum I t₀ = b) : Function.update (enum I) t₀ a = enum (replace I hb ha) := by
  have hmono : StrictMono (Function.update (enum I) t₀ a) := by
    intro s t hst
    have hσ := (enum I).strictMono hst
    by_cases hs : s = t₀ <;> by_cases ht : t = t₀
    · exact absurd (hs.trans ht.symm) hst.ne
    · subst hs
      rw [Function.update_self, Function.update_of_ne ht]
      rw [ht₀] at hσ
      have hne : enum I t ≠ a := fun h => ha (h ▸ enum_mem I t)
      rcases hab with h | h
      · exact lt_of_lt_of_le (Fin.lt_def.mpr (by omega)) (le_of_lt hσ)
      · refine lt_of_le_of_ne ?_ (Ne.symm hne)
        rw [Fin.le_def]
        have := Fin.lt_def.mp hσ
        omega
    · subst ht
      rw [Function.update_self, Function.update_of_ne hs]
      rw [ht₀] at hσ
      have hne : enum I s ≠ a := fun h => ha (h ▸ enum_mem I s)
      rcases hab with h | h
      · refine lt_of_le_of_ne ?_ hne
        rw [Fin.le_def]
        have := Fin.lt_def.mp hσ
        omega
      · exact lt_of_lt_of_le hσ (le_of_lt (Fin.lt_def.mpr (by omega)))
    · rw [Function.update_of_ne hs, Function.update_of_ne ht]
      exact hσ
  have hmem : ∀ t, Function.update (enum I) t₀ a t ∈ (replace I hb ha).val := by
    intro t
    by_cases ht : t = t₀
    · subst ht
      rw [Function.update_self]
      exact Finset.mem_insert_self a _
    · rw [Function.update_of_ne ht]
      refine Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨?_, enum_mem I t⟩)
      rw [← ht₀]
      exact fun h => ht ((enum I).injective h)
  have := Finset.orderEmbOfFin_unique' (replace I hb ha).prop
    (f := OrderEmbedding.ofStrictMono _ hmono) hmem
  exact congrArg DFunLike.coe this

theorem map_transvection_wedgeBasis {a b : Fin n} (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (c : R) (I : powersetCard (Fin n) k) :
    exteriorPower.map k (transvLin a b c) (wedgeBasis I) =
      if h : b ∈ I.val ∧ a ∉ I.val then wedgeBasis I + c • wedgeBasis (replace I h.1 h.2)
      else wedgeBasis I := by
  have hab' : a ≠ b := by
    rintro rfl
    omega
  rw [map_apply_ιMulti_family]
  simp only [ιMulti_family]
  set v : Fin k → Fin n → R := (fun i : Fin n => (Pi.single i 1 : Fin n → R)) ∘ enum I
    with hv
  by_cases hb : b ∈ I.val
  · obtain ⟨t₀, ht₀⟩ := exists_enum_eq hb
    have hcomp : (transvLin a b c ∘ fun i : Fin n => (Pi.single i 1 : Fin n → R)) ∘ enum I =
        Function.update v t₀ (Pi.single b 1 + c • Pi.single a 1) := by
      funext t
      by_cases ht : t = t₀
      · subst ht
        rw [Function.update_self]
        change transvLin a b c (Pi.single (enum I t) 1) = _
        rw [transvLin_single, ht₀]
        simp
      · rw [Function.update_of_ne ht]
        have hne : enum I t ≠ b := fun h => ht ((enum I).injective (h.trans ht₀.symm))
        change transvLin a b c (Pi.single (enum I t) 1) = v t
        rw [transvLin_single]
        simp [hne, hv]
    rw [hcomp, AlternatingMap.map_update_add, AlternatingMap.map_update_smul]
    have hself : Function.update v t₀ (Pi.single b 1) = v := by
      rw [← ht₀]
      exact Function.update_eq_self t₀ v
    rw [hself]
    by_cases ha : a ∈ I.val
    · rw [dite_eq_right (by simp [ha])]
      obtain ⟨t₁, ht₁⟩ := exists_enum_eq ha
      have hne : t₀ ≠ t₁ := fun h => hab' (by rw [← ht₁, ← ht₀, h])
      have hzero : ιMulti R k (Function.update v t₀ (Pi.single a 1)) = 0 := by
        refine AlternatingMap.map_eq_zero_of_eq _ _ (i := t₀) (j := t₁) ?_ hne
        rw [Function.update_self, Function.update_of_ne hne.symm]
        simp [hv, ht₁]
      rw [hzero, smul_zero, add_zero]
    · rw [dite_eq_left (show b ∈ I.val ∧ a ∉ I.val from ⟨hb, ha⟩)]
      have hvec : Function.update v t₀ (Pi.single a 1) =
          (fun i : Fin n => (Pi.single i 1 : Fin n → R)) ∘ enum (replace I hb ha) := by
        rw [← update_enum_eq hab hb ha ht₀]
        funext t
        by_cases ht : t = t₀
        · subst ht
          simp
        · simp [Function.update_of_ne ht, hv]
      rw [hvec]
  · rw [dite_eq_right (by simp [hb])]
    have hvec : (transvLin a b c ∘ fun i : Fin n => (Pi.single i 1 : Fin n → R)) ∘ enum I = v := by
      funext t
      have hne : enum I t ≠ b := fun h => hb (h ▸ enum_mem I t)
      change transvLin a b c (Pi.single (enum I t) 1) = v t
      rw [transvLin_single]
      simp [hne, hv]
    rw [hvec]

end CFSG.LieType.Chevalley.ExteriorCube
