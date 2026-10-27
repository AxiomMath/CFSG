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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
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

public section

namespace CFSG.CGT.PushingUpLit.Glue

open Matrix

section SL

variable {F : Type*} [Field F]

private theorem det_lower (a b : F) (ha : a ≠ 0) : (!![a, 0; b, a⁻¹] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [Matrix.det_fin_two_of]
  field_simp
  ring

private theorem det_anti (b : F) (hb : b ≠ 0) :
    (!![0, -b⁻¹; b, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [Matrix.det_fin_two_of]
  field_simp
  ring

theorem exists_sl2_mulVec_eq (v : Fin 2 → F) (hv : v ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = v := by
  by_cases ha : v 0 = 0
  · have hb : v 1 ≠ 0 := by
      intro hb
      apply hv
      ext i
      fin_cases i
      · exact ha
      · exact hb
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], det_anti _ hb⟩, ?_⟩
    ext i
    fin_cases i
    · simp [ha]
    · simp
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], det_lower _ _ ha⟩, ?_⟩
    ext i
    fin_cases i
    · simp
    · simp

theorem exists_sl2_mulVec_eq_of_ne_zero {v w : Fin 2 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = w := by
  obtain ⟨gv, hgv⟩ := exists_sl2_mulVec_eq v hv
  obtain ⟨gw, hgw⟩ := exists_sl2_mulVec_eq w hw
  refine ⟨gw * gv⁻¹, ?_⟩
  have h1 : (gv⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec v = ![1, 0] := by
    rw [← hgv, Matrix.mulVec_mulVec]
    have : ((gv⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (gv : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      rfl
    rw [this, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hgw]

theorem sl2_invariant_eq_bot_or_top (N : AddSubgroup (Fin 2 → F))
    (hN : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F), v ∈ N →
      (g : Matrix (Fin 2) (Fin 2) F).mulVec v ∈ N) : N = ⊥ ∨ N = ⊤ := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨v, hvN, hv0⟩ : ∃ v ∈ N, v ≠ 0 := by
      by_contra h
      push Not at h
      exact hbot ((AddSubgroup.eq_bot_iff_forall N).mpr h)
    rw [eq_top_iff]
    intro w _
    by_cases hw : w = 0
    · rw [hw]; exact N.zero_mem
    · obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq_of_ne_zero hv0 hw
      rw [← hg]
      exact hN g v hvN

end SL

section Alt

variable {n : ℕ}

@[expose] def evenWeight (n : ℕ) : AddSubgroup (Fin n → ZMod 2) :=
  AddMonoidHom.ker (∑ i : Fin n, Pi.evalAddMonoidHom (fun _ : Fin n => ZMod 2) i)

theorem mem_evenWeight_iff (v : Fin n → ZMod 2) : v ∈ evenWeight n ↔ ∑ i, v i = 0 := by
  simp [evenWeight, AddMonoidHom.mem_ker]

@[expose] def permVec (σ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => v (σ⁻¹ i)

theorem permVec_add (σ : Equiv.Perm (Fin n)) (v w : Fin n → ZMod 2) :
    permVec σ (v + w) = permVec σ v + permVec σ w := rfl

theorem permVec_single (σ : Equiv.Perm (Fin n)) (a : Fin n) :
    permVec σ (Pi.single a 1) = Pi.single (σ a) 1 := by
  funext x
  simp only [permVec, Pi.single_apply]
  congr 1
  simp only [eq_iff_iff]
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [h]
    simp

theorem swap_mul_swap_mem_alternatingGroup {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) :
    Equiv.swap a b * Equiv.swap b c ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hbc]
  rfl

theorem threeCycle_apply {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (Equiv.swap a b * Equiv.swap b c) a = b ∧ (Equiv.swap a b * Equiv.swap b c) b = c ∧
      (Equiv.swap a b * Equiv.swap b c) c = a := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac]
  · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  · simp [Equiv.Perm.mul_apply]

@[expose] def pairVec (a b : Fin n) : Fin n → ZMod 2 := Pi.single a 1 + Pi.single b 1

theorem pairVec_comm (a b : Fin n) : pairVec a b = pairVec b a := add_comm _ _

theorem pairVec_mem_evenWeight (a b : Fin n) : pairVec a b ∈ evenWeight n := by
  rw [mem_evenWeight_iff]
  simp [pairVec, Finset.sum_add_distrib]
  decide

section Pairs

variable {N : AddSubgroup (Fin n → ZMod 2)}
  (hN : ∀ σ ∈ alternatingGroup (Fin n), ∀ v ∈ N, permVec σ v ∈ N)

include hN in
theorem pairVec_mem_of_threeCycle {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : pairVec a b ∈ N) : pairVec b c ∈ N := by
  have hσ := swap_mul_swap_mem_alternatingGroup hab hbc
  obtain ⟨h1, h2, -⟩ := threeCycle_apply hab hac hbc
  have := hN _ hσ _ h
  unfold pairVec at this ⊢
  rwa [permVec_add, permVec_single, permVec_single, h1, h2] at this

include hN in
theorem pairVec_mem_of_ne {x y z : Fin n} (hxy : x ≠ y) (hzx : z ≠ x)
    (h : pairVec x y ∈ N) : pairVec x z ∈ N := by
  by_cases hzy : z = y
  · rw [hzy]; exact h
  · rw [pairVec_comm] at h
    exact pairVec_mem_of_threeCycle hN hxy.symm (Ne.symm hzy) hzx.symm h

include hN in
theorem pairVec_mem_all {j k : Fin n} (hjk : j ≠ k) (h : pairVec j k ∈ N) :
    ∀ a b : Fin n, a ≠ b → pairVec a b ∈ N := by
  intro a b hab
  have hA : ∀ z, z ≠ j → pairVec j z ∈ N := fun z hz => pairVec_mem_of_ne hN hjk hz h
  by_cases haj : a = j
  · rw [haj]
    exact hA b (haj ▸ hab.symm)
  · have h1 : pairVec a j ∈ N := by
      rw [pairVec_comm]
      exact hA a haj
    exact pairVec_mem_of_ne hN haj hab.symm h1

include hN in
theorem exists_pairVec_mem (hodd : Odd n) {v : Fin n → ZMod 2} (hv : v ∈ N)
    (hΔ : v ∈ evenWeight n) (hv0 : v ≠ 0) : ∃ j k : Fin n, j ≠ k ∧ pairVec j k ∈ N := by
  have hz : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [mem_evenWeight_iff] at hΔ
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hi1 : v i = 1 := hz _ hi
  obtain ⟨k, hki, hk⟩ : ∃ k, k ≠ i ∧ v k = 1 := by
    by_contra h
    push Not at h
    have h0 : ∀ k, k ≠ i → v k = 0 := fun k hk => by
      by_contra h'
      exact h k hk (hz _ h')
    have hsum : ∑ x, v x = 1 := by
      rw [Finset.sum_eq_single i (fun k _ hk => h0 k hk) (by simp)]
      exact hi1
    rw [hΔ] at hsum
    exact absurd hsum (by decide)
  obtain ⟨j, hj⟩ : ∃ j, v j = 0 := by
    by_contra h
    push Not at h
    have h1 : ∀ x, v x = 1 := fun x => hz _ (h x)
    have hsum : ∑ x, v x = (n : ZMod 2) := by simp [h1]
    rw [hΔ] at hsum
    have hn1 : (n : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hodd
    rw [hn1] at hsum
    exact absurd hsum (by decide)
  have hij : i ≠ j := fun h => by
    rw [h] at hi1
    rw [hi1] at hj
    exact one_ne_zero hj
  have hjk : j ≠ k := fun h => by
    rw [h] at hj
    rw [hj] at hk
    exact zero_ne_one hk
  have hik : i ≠ k := hki.symm
  have hσ := swap_mul_swap_mem_alternatingGroup hij hjk
  obtain ⟨h1, h2', h3⟩ := threeCycle_apply hij hik hjk
  have hw := N.add_mem hv (hN _ hσ _ hv)
  refine ⟨j, k, hjk, ?_⟩
  convert hw using 1
  funext x
  simp only [pairVec, Pi.add_apply, Pi.single_apply, permVec]
  by_cases hxi : x = i
  · subst hxi
    have : ((Equiv.swap x j * Equiv.swap j k)⁻¹) x = k := Equiv.Perm.inv_eq_iff_eq.mpr h3.symm
    rw [this, hi1, hk]
    simp [hij, hik]
    exact (h2 1).symm
  · by_cases hxj : x = j
    · subst hxj
      have : ((Equiv.swap i x * Equiv.swap x k)⁻¹) x = i := Equiv.Perm.inv_eq_iff_eq.mpr h1.symm
      rw [this, hj, hi1]
      simp [hjk]
    · by_cases hxk : x = k
      · subst hxk
        have : ((Equiv.swap i j * Equiv.swap j x)⁻¹) x = j :=
          Equiv.Perm.inv_eq_iff_eq.mpr h2'.symm
        rw [this, hk, hj]
        simp [hjk.symm]
      · have hfix : (Equiv.swap i j * Equiv.swap j k) x = x := by
          simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxj hxk,
            Equiv.swap_apply_of_ne_of_ne hxi hxj]
        have : ((Equiv.swap i j * Equiv.swap j k)⁻¹) x = x :=
          Equiv.Perm.inv_eq_iff_eq.mpr hfix.symm
        rw [this]
        simp [hxj, hxk]
        exact (h2 _).symm

end Pairs

theorem evenWeight_le_of_pairVec {N : AddSubgroup (Fin n → ZMod 2)} (hn : 0 < n)
    (hP : ∀ a b : Fin n, a ≠ b → pairVec a b ∈ N) : evenWeight n ≤ N := by
  intro v hv
  rw [mem_evenWeight_iff] at hv
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  have key : v = ∑ i, v i • pairVec i i0 := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, pairVec, Pi.add_apply, Pi.single_apply, mul_add,
      Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    by_cases hx : x = i0
    · rw [hx]
      simp [hv]
    · simp [hx]
  rw [key]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  by_cases hi : i = i0
  · rw [hi]
    have : pairVec i0 i0 = 0 := by
      funext x
      simp only [pairVec, Pi.add_apply, Pi.zero_apply]
      generalize (Pi.single i0 1 : Fin n → ZMod 2) x = y
      revert y
      decide
    rw [this, smul_zero]
    exact N.zero_mem
  · rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (v i) with h | h
    · rw [h, zero_smul]
      exact N.zero_mem
    · rw [h, one_smul]
      exact hP i i0 hi

theorem altInvariant_eq_bot_or_evenWeight (hodd : Odd n) (hn : 3 ≤ n)
    (N : AddSubgroup (Fin n → ZMod 2)) (hNΔ : N ≤ evenWeight n)
    (hN : ∀ σ ∈ alternatingGroup (Fin n), ∀ v ∈ N, permVec σ v ∈ N) :
    N = ⊥ ∨ N = evenWeight n := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨v, hvN, hv0⟩ : ∃ v ∈ N, v ≠ 0 := by
      by_contra h
      push Not at h
      exact hbot ((AddSubgroup.eq_bot_iff_forall N).mpr h)
    obtain ⟨j, k, hjk, hjkN⟩ := exists_pairVec_mem hN hodd hvN (hNΔ hvN) hv0
    exact le_antisymm hNΔ (evenWeight_le_of_pairVec (by omega) (pairVec_mem_all hN hjk hjkN))

end Alt

end CFSG.CGT.PushingUpLit.Glue
