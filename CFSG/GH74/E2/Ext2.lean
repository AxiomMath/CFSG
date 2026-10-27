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
public import Mathlib.GroupTheory.IndexNormal
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
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.E2

structure Ext2Data (M : Type*) [Group M] where
  α : MulAut M
  w : M
  fix : α w = w
  sq : ∀ m : M, α (α m) = w * m * w⁻¹

@[ext] structure Ext2 (M : Type*) [Group M] (d : Ext2Data M) where
  base : M
  bit : Bool

namespace Ext2

variable {M : Type*} [Group M] {d : Ext2Data M}

instance instMulExt2 : Mul (Ext2 M d) where
  mul
    | ⟨m₁, false⟩, ⟨m₂, false⟩ => ⟨m₁ * m₂, false⟩
    | ⟨m₁, false⟩, ⟨m₂, true⟩ => ⟨m₁ * m₂, true⟩
    | ⟨m₁, true⟩, ⟨m₂, false⟩ => ⟨m₁ * d.α m₂, true⟩
    | ⟨m₁, true⟩, ⟨m₂, true⟩ => ⟨m₁ * d.α m₂ * d.w, false⟩

instance instOneExt2 : One (Ext2 M d) := ⟨⟨1, false⟩⟩

instance instInvExt2 : Inv (Ext2 M d) where
  inv
    | ⟨m, false⟩ => ⟨m⁻¹, false⟩
    | ⟨m, true⟩ => ⟨d.w⁻¹ * (d.α m)⁻¹, true⟩

@[simp] theorem mk_mul_mk_ff (m₁ m₂ : M) :
    (⟨m₁, false⟩ : Ext2 M d) * ⟨m₂, false⟩ = ⟨m₁ * m₂, false⟩ := rfl

@[simp] theorem mk_mul_mk_ft (m₁ m₂ : M) :
    (⟨m₁, false⟩ : Ext2 M d) * ⟨m₂, true⟩ = ⟨m₁ * m₂, true⟩ := rfl

@[simp] theorem mk_mul_mk_tf (m₁ m₂ : M) :
    (⟨m₁, true⟩ : Ext2 M d) * ⟨m₂, false⟩ = ⟨m₁ * d.α m₂, true⟩ := rfl

@[simp] theorem mk_mul_mk_tt (m₁ m₂ : M) :
    (⟨m₁, true⟩ : Ext2 M d) * ⟨m₂, true⟩ = ⟨m₁ * d.α m₂ * d.w, false⟩ := rfl

@[simp] theorem one_def : (1 : Ext2 M d) = ⟨1, false⟩ := rfl

@[simp] theorem inv_mk_f (m : M) : (⟨m, false⟩ : Ext2 M d)⁻¹ = ⟨m⁻¹, false⟩ := rfl

@[simp] theorem inv_mk_t (m : M) : (⟨m, true⟩ : Ext2 M d)⁻¹ = ⟨d.w⁻¹ * (d.α m)⁻¹, true⟩ := rfl

instance instGroupExt2 : Group (Ext2 M d) where
  mul_assoc := by
    rintro ⟨m₁, b₁⟩ ⟨m₂, b₂⟩ ⟨m₃, b₃⟩
    cases b₁ <;> cases b₂ <;> cases b₃ <;>
      simp only [mk_mul_mk_ff, mk_mul_mk_ft, mk_mul_mk_tf, mk_mul_mk_tt, Ext2.mk.injEq, and_true,
        map_mul, d.fix, d.sq] <;> group
  one_mul := by
    rintro ⟨m, b⟩
    cases b <;> simp
  mul_one := by
    rintro ⟨m, b⟩
    cases b <;> simp
  inv_mul_cancel := by
    rintro ⟨m, b⟩
    cases b
    · simp
    · simp only [inv_mk_t, mk_mul_mk_tt, one_def, Ext2.mk.injEq, and_true]
      group

instance instDecidableEqExt2 [DecidableEq M] : DecidableEq (Ext2 M d) := fun x y =>
  decidable_of_iff (x.base = y.base ∧ x.bit = y.bit)
    ⟨fun h => Ext2.ext h.1 h.2, fun h => h ▸ ⟨rfl, rfl⟩⟩

@[expose] def equivProd : Ext2 M d ≃ M × Bool where
  toFun x := (x.base, x.bit)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFiniteExt2 [Finite M] : Finite (Ext2 M d) := Finite.of_equiv _ equivProd.symm

instance instFintypeExt2 [Fintype M] : Fintype (Ext2 M d) :=
  Fintype.ofEquiv _ equivProd.symm

theorem card_eq : Nat.card (Ext2 M d) = 2 * Nat.card M := by
  rw [Nat.card_congr equivProd, Nat.card_prod]
  simp [mul_comm]

@[expose] def inl : M →* Ext2 M d where
  toFun m := ⟨m, false⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem inl_apply (m : M) : (inl m : Ext2 M d) = ⟨m, false⟩ := rfl

theorem inl_injective : Function.Injective (inl : M →* Ext2 M d) := fun _ _ h =>
  congrArg Ext2.base h

@[expose] def n : Ext2 M d := ⟨1, true⟩

theorem inl_mul_n (m : M) : (inl m : Ext2 M d) * n = ⟨m, true⟩ := by
  simp [n]

theorem n_mul_inl (m : M) : (n : Ext2 M d) * inl m = ⟨d.α m, true⟩ := by
  simp [n]

theorem n_mul_inl_mul_inv_n (m : M) : (n : Ext2 M d) * inl m * n⁻¹ = inl (d.α m) := by
  have h : (n : Ext2 M d) * inl m = inl (d.α m) * n := by
    rw [n_mul_inl, inl_mul_n]
  rw [h, mul_inv_cancel_right]

theorem n_mul_n : (n : Ext2 M d) * n = inl d.w := by
  simp [n]

theorem eq_inl_or_eq_inl_mul_n (x : Ext2 M d) :
    (∃ m : M, x = inl m) ∨ ∃ m : M, x = inl m * n := by
  obtain ⟨m, b⟩ := x
  cases b
  · exact Or.inl ⟨m, rfl⟩
  · exact Or.inr ⟨m, by rw [inl_mul_n]⟩

theorem mem_range_inl_iff (x : Ext2 M d) : x ∈ (inl : M →* Ext2 M d).range ↔ x.bit = false := by
  constructor
  · rintro ⟨m, rfl⟩
    rfl
  · intro h
    exact ⟨x.base, Ext2.ext rfl h.symm⟩

theorem bit_mul_n (x : Ext2 M d) : (x * n).bit = !x.bit := by
  obtain ⟨m, b⟩ := x
  cases b <;> rfl

theorem index_range_inl : (inl : M →* Ext2 M d).range.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨n, fun x => ?_⟩
  rw [mem_range_inl_iff, mem_range_inl_iff, bit_mul_n]
  cases x.bit <;> simp

end Ext2

section Recognition

private theorem mul_inv_mem_of_index_two {P : Type*} [Group P] {M : Subgroup P}
    (hM : M.index = 2) {p n : P} (hp : p ∉ M) (hn : n ∉ M) : p * n⁻¹ ∈ M := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hM
  have h1 : p * a ∈ M := by
    rcases ha p with ⟨h, -⟩ | ⟨h, h'⟩
    · exact h
    · exact absurd h hp
  have h2 : n * a ∈ M := by
    rcases ha n with ⟨h, -⟩ | ⟨h, h'⟩
    · exact h
    · exact absurd h hn
  have := M.mul_mem h1 (M.inv_mem h2)
  simpa [mul_assoc] using this

theorem ext2_of_index_two {P : Type*} [Group P] (M : Subgroup P) (hM : M.index = 2) {n : P}
    (hn : n ∉ M) :
    ∃ d : Ext2Data ↥M, (∀ m : ↥M, ((d.α m : ↥M) : P) = n * m * n⁻¹) ∧
      ((d.w : ↥M) : P) = n * n ∧
        ∃ e : P ≃* Ext2 ↥M d, (∀ m : ↥M, e m = Ext2.inl m) ∧ e n = Ext2.n := by
  have hnorm : M.Normal := Subgroup.normal_of_index_eq_two hM
  have hn2 : n * n ∈ M := Subgroup.mul_self_mem_of_index_two hM n
  let α : MulAut ↥M := MulAut.conjNormal n
  have hα : ∀ m : ↥M, ((α m : ↥M) : P) = n * m * n⁻¹ := fun m => MulAut.conjNormal_apply n m
  let w : ↥M := ⟨n * n, hn2⟩
  have hfix : α w = w := by
    apply Subtype.ext
    rw [hα]
    show n * (n * n) * n⁻¹ = n * n
    group
  have hsq : ∀ m : ↥M, α (α m) = w * m * w⁻¹ := by
    intro m
    apply Subtype.ext
    rw [hα, hα]
    show n * (n * m * n⁻¹) * n⁻¹ = (n * n) * m * (n * n)⁻¹
    group
  let d : Ext2Data ↥M := ⟨α, w, hfix, hsq⟩
  refine ⟨d, hα, rfl, ?_⟩
  let f : Ext2 ↥M d →* P :=
    { toFun := fun x => match x with
        | ⟨m, false⟩ => (m : P)
        | ⟨m, true⟩ => (m : P) * n
      map_one' := rfl
      map_mul' := by
        rintro ⟨m₁, b₁⟩ ⟨m₂, b₂⟩
        cases b₁ <;> cases b₂
        · rfl
        · show ((m₁ * m₂ : ↥M) : P) * n = (m₁ : P) * ((m₂ : P) * n)
          simp [mul_assoc]
        · show ((m₁ * d.α m₂ : ↥M) : P) * n = ((m₁ : P) * n) * m₂
          rw [Subgroup.coe_mul, hα]
          group
        · show ((m₁ * d.α m₂ * w : ↥M) : P) = ((m₁ : P) * n) * ((m₂ : P) * n)
          rw [Subgroup.coe_mul, Subgroup.coe_mul, hα]
          show (m₁ : P) * (n * m₂ * n⁻¹) * (n * n) = ((m₁ : P) * n) * ((m₂ : P) * n)
          group }
  have hinj : Function.Injective f := by
    rintro ⟨m, b⟩ ⟨m', b'⟩ h
    cases b <;> cases b'
    · have h' : (m : P) = m' := h
      exact congrArg (fun x => (⟨x, false⟩ : Ext2 ↥M d)) (Subtype.ext h')
    · exfalso
      apply hn
      have h' : (m : P) = m' * n := h
      have : n = (m' : P)⁻¹ * m := by rw [h']; group
      rw [this]
      exact M.mul_mem (M.inv_mem m'.2) m.2
    · exfalso
      apply hn
      have h' : (m : P) * n = m' := h
      have : n = (m : P)⁻¹ * m' := by rw [← h']; group
      rw [this]
      exact M.mul_mem (M.inv_mem m.2) m'.2
    · have h' : (m : P) * n = m' * n := h
      exact congrArg (fun x => (⟨x, true⟩ : Ext2 ↥M d)) (Subtype.ext (mul_right_cancel h'))
  have hsurj : Function.Surjective f := by
    intro p
    by_cases hp : p ∈ M
    · exact ⟨⟨⟨p, hp⟩, false⟩, rfl⟩
    · have hpn : p * n⁻¹ ∈ M := mul_inv_mem_of_index_two hM hp hn
      refine ⟨⟨⟨p * n⁻¹, hpn⟩, true⟩, ?_⟩
      show p * n⁻¹ * n = p
      group
  refine ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm, fun m => ?_, ?_⟩
  · rw [MulEquiv.symm_apply_eq]
    rfl
  · rw [MulEquiv.symm_apply_eq]
    show n = ((1 : ↥M) : P) * n
    simp

end Recognition

section Transport

variable {M M' : Type*} [Group M] [Group M']

@[expose] def Ext2Data.map (e : M ≃* M') (d : Ext2Data M) : Ext2Data M' where
  α := e.symm.trans (d.α.trans e)
  w := e d.w
  fix := by
    show e (d.α (e.symm (e d.w))) = e d.w
    rw [MulEquiv.symm_apply_apply, d.fix]
  sq := by
    intro m'
    show e (d.α (e.symm (e (d.α (e.symm m'))))) = e d.w * m' * (e d.w)⁻¹
    rw [MulEquiv.symm_apply_apply, d.sq, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem Ext2Data.map_α (e : M ≃* M') (d : Ext2Data M) (m : M) :
    (d.map e).α (e m) = e (d.α m) := by
  show e (d.α (e.symm (e m))) = e (d.α m)
  rw [MulEquiv.symm_apply_apply]

theorem Ext2Data.map_w (e : M ≃* M') (d : Ext2Data M) : (d.map e).w = e d.w := rfl

@[expose] def Ext2.mapEquiv (e : M ≃* M') (d : Ext2Data M) : Ext2 M d ≃* Ext2 M' (d.map e) where
  toFun x := ⟨e x.base, x.bit⟩
  invFun y := ⟨e.symm y.base, y.bit⟩
  left_inv x := by
    obtain ⟨m, b⟩ := x
    simp
  right_inv y := by
    obtain ⟨m, b⟩ := y
    simp
  map_mul' := by
    rintro ⟨m₁, b₁⟩ ⟨m₂, b₂⟩
    cases b₁ <;> cases b₂
    · simp
    · simp
    · simp [Ext2Data.map_α]
    · simp [Ext2Data.map_α, Ext2Data.map_w]

theorem Ext2.mapEquiv_inl (e : M ≃* M') (d : Ext2Data M) (m : M) :
    Ext2.mapEquiv e d (Ext2.inl m) = Ext2.inl (e m) := rfl

theorem Ext2.mapEquiv_n (e : M ≃* M') (d : Ext2Data M) :
    Ext2.mapEquiv e d Ext2.n = Ext2.n := by
  show (⟨e 1, true⟩ : Ext2 M' (d.map e)) = ⟨1, true⟩
  simp

theorem exists_ext2_equiv {P : Type*} [Group P] (M : Subgroup P) (hM : M.index = 2) {n : P}
    (hn : n ∉ M) {M0 : Type*} [Group M0] (eM : ↥M ≃* M0) :
    ∃ d0 : Ext2Data M0, ∃ e : P ≃* Ext2 M0 d0,
      (∀ m : ↥M, e m = Ext2.inl (eM m)) ∧ e n = Ext2.n := by
  obtain ⟨d, -, -, e, he, hen⟩ := ext2_of_index_two M hM hn
  refine ⟨d.map eM, e.trans (Ext2.mapEquiv eM d), fun m => ?_, ?_⟩
  · show Ext2.mapEquiv eM d (e m) = _
    rw [he, Ext2.mapEquiv_inl]
  · show Ext2.mapEquiv eM d (e n) = _
    rw [hen, Ext2.mapEquiv_n]

end Transport

section Enumeration

variable {M : Type*} [Group M]

@[expose] def Ext2Data.equivSubtype :
    Ext2Data M ≃ {p : MulAut M × M // p.1 p.2 = p.2 ∧ ∀ m : M, p.1 (p.1 m) = p.2 * m * p.2⁻¹} where
  toFun d := ⟨(d.α, d.w), d.fix, d.sq⟩
  invFun p := ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeExt2Data [Fintype M] [DecidableEq M] : Fintype (Ext2Data M) :=
  Fintype.ofEquiv _ Ext2Data.equivSubtype.symm

end Enumeration

end CFSG.GH74.E2
