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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.CGT.Timmesfeld75

open scoped commutatorElement

theorem normal_pSubgroup_bot_of_pSubgroups_central {K : Type*} [Group K] [Finite K] (p : ℕ)
    [Fact p.Prime] (h : ∀ P : Subgroup K, P.Normal → IsPGroup p P → P ≤ Subgroup.center K)
    (A : Subgroup (K ⧸ Subgroup.center K)) (hA : A.Normal) (hAp : IsPGroup p A) : A = ⊥ := by
  set π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hπ
  set N : Subgroup K := A.comap π with hN
  have : N.Normal := hA.comap π
  have hmemN : ∀ x : K, x ∈ N ↔ π x ∈ A := fun x => Iff.rfl
  let f : ↥N →* ↥A := MonoidHom.codRestrict (π.comp N.subtype) A (fun x => x.2)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (a : K ⧸ Subgroup.center K)
    refine ⟨⟨k, (hmemN k).2 (by
      have : π k = (a : K ⧸ Subgroup.center K) := hk
      rw [this]; exact a.2)⟩, ?_⟩
    apply Subtype.ext
    exact hk
  have hker : f.ker ≤ Subgroup.center ↥N := by
    intro x hx
    have h1 : π (x : K) = 1 := by
      have := (MonoidHom.mem_ker).1 hx
      exact congrArg Subtype.val this
    have hxz : (x : K) ∈ Subgroup.center K := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hxz y
  have : Group.IsNilpotent ↥A := hAp.isNilpotent
  have : Group.IsNilpotent ↥N := Subgroup.isNilpotent_of_ker_le_center f hker
  let P : Sylow p ↥N := Sylow.nonempty.some
  have hPn : (P : Subgroup ↥N).Normal := inferInstance
  have hchar : (P : Subgroup ↥N).Characteristic := Sylow.characteristic_of_normal P hPn
  let S : Subgroup K := (P : Subgroup ↥N).map N.subtype
  have hSn : S.Normal := by
    refine ⟨fun x hx k => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    have hφ : MulAut.conjNormal (H := N) k y ∈ (P : Subgroup ↥N) := by
      have h1 := hchar.fixed (MulAut.conjNormal (H := N) k)
      rw [← h1] at hy
      exact Subgroup.mem_comap.1 hy
    refine ⟨_, hφ, ?_⟩
    simp
  have hSp : IsPGroup p S := P.isPGroup'.map N.subtype
  have hSz : S ≤ Subgroup.center K := h S hSn hSp
  have hPA : (P.mapSurjective hf : Subgroup ↥A) = ⊤ := by
    have hAtop : IsPGroup p (⊤ : Subgroup ↥A) := hAp.of_equiv Subgroup.topEquiv.symm
    exact ((P.mapSurjective hf).is_maximal' hAtop le_top).symm
  rw [eq_bot_iff]
  intro a ha
  have : (⟨a, ha⟩ : ↥A) ∈ (P.mapSurjective hf : Subgroup ↥A) := by rw [hPA]; trivial
  obtain ⟨y, hy, hya⟩ := this
  have hyS : (y : K) ∈ S := ⟨y, hy, rfl⟩
  have h1 : π (y : K) = 1 := (QuotientGroup.eq_one_iff _).2 (hSz hyS)
  have h2 : f y = ⟨a, ha⟩ := hya
  have h3 : π (y : K) = a := congrArg Subtype.val h2
  rw [← h3, h1]
  exact Subgroup.one_mem _

theorem solvable_normal_bot_of_pSubgroups_central {K : Type*} [Group K] [Finite K]
    (h : ∀ (p : ℕ), p.Prime → ∀ P : Subgroup K, P.Normal → IsPGroup p P →
      P ≤ Subgroup.center K) :
    ∀ R : Subgroup (K ⧸ Subgroup.center K), R.Normal → Group.IsSolvable R → R = ⊥ := by
  intro R hR hRs
  by_contra hRne
  let ℳ : Set (Subgroup (K ⧸ Subgroup.center K)) := {A | A.Normal ∧ A ≤ R ∧ A ≠ ⊥}
  obtain ⟨A, ⟨hAn, hAR, hAne⟩, hAmin⟩ :=
    wellFounded_lt.has_min ℳ ⟨R, hR, le_rfl, hRne⟩
  have hmin : ∀ B : Subgroup (K ⧸ Subgroup.center K), B.Normal → B ≤ A → B ≠ ⊥ → B = A := by
    intro B hB hBA hBne
    by_contra hne
    exact hAmin B ⟨hB, hBA.trans hAR, hBne⟩ (lt_of_le_of_ne hBA hne)
  have hcomm : ⁅A, A⁆ = ⊥ := by
    by_contra hne
    have hcn : (⁅A, A⁆).Normal := inferInstance
    have hcle : ⁅A, A⁆ ≤ A := Subgroup.commutator_le_left A A
    have heq : ⁅A, A⁆ = A := hmin _ hcn hcle hne
    have hH : A.subgroupOf R ≠ ⊥ := by
      intro hbot
      apply hAne
      have := congrArg (Subgroup.map R.subtype) hbot
      rw [Subgroup.map_subgroupOf_eq_of_le hAR, Subgroup.map_bot] at this
      exact this
    have hlt := Group.IsSolvable.commutator_lt_of_ne_bot (G := ↥R) hH
    have hmap : (⁅A.subgroupOf R, A.subgroupOf R⁆).map R.subtype = ⁅A, A⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAR]
    have hlt' := (Subgroup.map_lt_map_iff_of_injective R.subtype_injective).2 hlt
    rw [hmap, Subgroup.map_subgroupOf_eq_of_le hAR, heq] at hlt'
    exact lt_irrefl _ hlt'
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have : ⁅x, y⁆ ∈ ⁅A, A⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hcard : Nat.card A ≠ 1 := by
    intro h1
    apply hAne
    rw [Subgroup.eq_bot_iff_card, h1]
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcard
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) p hpd
  have ha1 : (a : K ⧸ Subgroup.center K) ≠ 1 := by
    intro h1
    have : a = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ha
    exact hp.one_lt.ne ha
  have hap : (a : K ⧸ Subgroup.center K) ^ p = 1 := by
    have := pow_orderOf_eq_one a
    rw [ha] at this
    exact congrArg Subtype.val this
  let E : Subgroup (K ⧸ Subgroup.center K) :=
    { carrier := {x | x ∈ A ∧ x ^ p = 1}
      mul_mem' := fun {x y} hx hy => ⟨A.mul_mem hx.1 hy.1, by
        rw [(show Commute x y from hAab x hx.1 y hy.1).mul_pow, hx.2, hy.2, mul_one]⟩
      one_mem' := ⟨A.one_mem, one_pow p⟩
      inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hEn : E.Normal := by
    refine ⟨fun x hx g => ⟨hAn.conj_mem x hx.1 g, ?_⟩⟩
    show (g * x * g⁻¹) ^ p = 1
    rw [conj_pow, hx.2]; simp
  have hEA : E ≤ A := fun x hx => hx.1
  have hEne : E ≠ ⊥ := by
    intro hbot
    apply ha1
    have : (a : K ⧸ Subgroup.center K) ∈ E := ⟨a.2, hap⟩
    rw [hbot] at this
    exact this
  have hEeq : E = A := hmin E hEn hEA hEne
  have hAp : IsPGroup p A := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have : (x : K ⧸ Subgroup.center K) ∈ E := by rw [hEeq]; exact x.2
    simpa using this.2
  exact hAne (normal_pSubgroup_bot_of_pSubgroups_central p (h p hp) A hAn hAp)

end CFSG.CGT.Timmesfeld75
