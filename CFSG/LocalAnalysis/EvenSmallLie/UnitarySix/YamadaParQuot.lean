module

public import Mathlib.Algebra.Module.StablyFree.Basic
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

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Subgroup

variable {G : Type*} [Group G]

structure ElemSec (D V : Subgroup G) : Prop where
  le : V ≤ D
  central : ∀ v ∈ V, ∀ x ∈ D, v * x = x * v
  comm : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ V
  sq : ∀ x ∈ D, x * x ∈ V

variable {D V : Subgroup G}

theorem ElemSec.normal (h : ElemSec D V) : (V.subgroupOf D).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have : (g : G) * n * (g : G)⁻¹ = n := by
    rw [← h.central n hn g g.2, mul_inv_cancel_right]
  simpa [this] using hn

instance ElemSec.instNormal [h : Fact (ElemSec D V)] : (V.subgroupOf D).Normal := h.out.normal

abbrev secQ (D V : Subgroup G) [Fact (ElemSec D V)] : Type _ := ↥D ⧸ V.subgroupOf D

variable [hDV : Fact (ElemSec D V)]

omit hDV in
theorem secQ_eq_iff [Fact (ElemSec D V)] (x y : D) : (x : secQ D V) = y ↔ (x : G)⁻¹ * y ∈ V := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

theorem secQ_mul_comm (a b : secQ D V) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with | H x => ?_
  induction b using QuotientGroup.induction_on with | H y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, secQ_eq_iff]
  have hc := hDV.out.comm ((y : G)⁻¹) (D.inv_mem y.2) ((x : G)⁻¹) (D.inv_mem x.2)
  have : ((x : G) * y)⁻¹ * (y * x) = (y : G)⁻¹ * (x : G)⁻¹ * ((y : G)⁻¹)⁻¹ * ((x : G)⁻¹)⁻¹ := by
    group
  simp only [Subgroup.coe_mul]
  rw [this]
  exact hc

theorem secQ_mul_self (a : secQ D V) : a * a = 1 := by
  induction a using QuotientGroup.induction_on with | H x => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_one, secQ_eq_iff]
  simpa using V.inv_mem (hDV.out.sq x x.2)

instance secQ.commGroup : CommGroup (secQ D V) where
  mul_comm := secQ_mul_comm

abbrev secW (D V : Subgroup G) [Fact (ElemSec D V)] : Type _ := Additive (secQ D V)

theorem secW_two_nsmul (w : secW D V) : 2 • w = 0 := by
  rw [two_nsmul]
  exact secQ_mul_self (Additive.toMul w)

noncomputable instance secW.module : Module (ZMod 2) (secW D V) :=
  AddCommGroup.zmodModule secW_two_nsmul

@[expose] def secMk (x : D) : secW D V := Additive.ofMul (x : secQ D V)

theorem secMk_mul (x y : D) : secMk (V := V) (x * y) = secMk x + secMk y := rfl

theorem secMk_eq_iff (x y : D) : secMk (V := V) x = secMk y ↔ (x : G)⁻¹ * y ∈ V :=
  (Additive.ofMul.injective.eq_iff).trans (secQ_eq_iff x y)

theorem secMk_surjective : Function.Surjective (secMk (D := D) (V := V)) := by
  intro w
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
  exact ⟨x, by rw [secMk, hx]; rfl⟩

@[expose] def conjD (n : G) (hn : n ∈ normalizer (D : Set G)) : D →* D where
  toFun x := ⟨n * x * n⁻¹, (mem_normalizer_iff.mp hn x).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit hDV in
theorem conjD_le (n : G) (hn : n ∈ normalizer (D : Set G)) (hnV : n ∈ normalizer (V : Set G)) :
    V.subgroupOf D ≤ (V.subgroupOf D).comap (conjD n hn) := by
  intro x hx
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
  exact (mem_normalizer_iff.mp hnV x).mp hx

@[expose] noncomputable def secAct (n : G) (hn : n ∈ normalizer (D : Set G))
    (hnV : n ∈ normalizer (V : Set G)) : secW D V →ₗ[ZMod 2] secW D V :=
  AddMonoidHom.toZModLinearMap 2
    (MonoidHom.toAdditive (QuotientGroup.map _ _ (conjD n hn) (conjD_le n hn hnV)))

theorem secAct_mk (n : G) (hn : n ∈ normalizer (D : Set G)) (hnV : n ∈ normalizer (V : Set G))
    (x : D) : secAct n hn hnV (secMk x) = secMk (conjD n hn x) := rfl

theorem secAct_mul (n m : G) (hn : n ∈ normalizer (D : Set G)) (hnV : n ∈ normalizer (V : Set G))
    (hm : m ∈ normalizer (D : Set G)) (hmV : m ∈ normalizer (V : Set G)) :
    secAct (n * m) (mul_mem hn hm) (mul_mem hnV hmV) = secAct n hn hnV ∘ₗ secAct m hm hmV := by
  apply LinearMap.ext
  intro w
  obtain ⟨x, rfl⟩ := secMk_surjective w
  rw [LinearMap.comp_apply, secAct_mk, secAct_mk, secAct_mk]
  congr 1
  apply Subtype.ext
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
  group

theorem secAct_one : secAct (D := D) (V := V) 1 (one_mem _) (one_mem _) = LinearMap.id := by
  apply LinearMap.ext
  intro w
  obtain ⟨x, rfl⟩ := secMk_surjective w
  rw [secAct_mk, LinearMap.id_apply]
  congr 1
  apply Subtype.ext
  simp [conjD]

@[expose] noncomputable def secRep (N : Subgroup G) (hN : N ≤ normalizer (D : Set G))
    (hNV : N ≤ normalizer (V : Set G)) : N →* (secW D V →ₗ[ZMod 2] secW D V) where
  toFun n := secAct n (hN n.2) (hNV n.2)
  map_one' := secAct_one
  map_mul' n m := (secAct_mul (n : G) (m : G) (hN n.2) (hNV n.2) (hN m.2) (hNV m.2)).trans
    (Module.End.mul_eq_comp _ _).symm

theorem secRep_mk (N : Subgroup G) (hN : N ≤ normalizer (D : Set G))
    (hNV : N ≤ normalizer (V : Set G)) (n : N) (x : D) :
    secRep N hN hNV n (secMk x) = secMk (V := V) (conjD (D := D) n (hN n.2) x) := rfl

theorem secRep_of_mem (N : Subgroup G) (hN : N ≤ normalizer (D : Set G))
    (hNV : N ≤ normalizer (V : Set G)) (n : N) (hn : (n : G) ∈ D) : secRep N hN hNV n = 1 := by
  apply LinearMap.ext
  intro w
  obtain ⟨x, rfl⟩ := secMk_surjective w
  rw [secRep_mk, Module.End.one_apply, secMk_eq_iff]
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
  have := hDV.out.comm n hn ((x : G)⁻¹) (D.inv_mem x.2)
  convert this using 1
  group

@[expose] noncomputable def gamRep (N : Subgroup G) (hN : N ≤ normalizer (D : Set G))
    (hNV : N ≤ normalizer (V : Set G)) [(D.subgroupOf N).Normal] :
    (↥N ⧸ D.subgroupOf N) →* (secW D V →ₗ[ZMod 2] secW D V) :=
  QuotientGroup.lift (D.subgroupOf N) (secRep N hN hNV) fun n hn => by
    rw [MonoidHom.mem_ker]
    exact secRep_of_mem N hN hNV n (Subgroup.mem_subgroupOf.mp hn)

theorem comm_mem_V {x y : G} (hx : x ∈ D) (hy : y ∈ D) : x * y * x⁻¹ * y⁻¹ ∈ V :=
  hDV.out.comm x hx y hy

@[expose] def secComm (x y : D) : V := ⟨x * y * (x : G)⁻¹ * (y : G)⁻¹, comm_mem_V x.2 y.2⟩

theorem secComm_mul_right (x y y' : D) : secComm (V := V) x (y * y') = secComm x y * secComm x y' := by
  apply Subtype.ext
  simp only [secComm, Subgroup.coe_mul]
  have hc := hDV.out.central _ (comm_mem_V (V := V) x.2 y'.2) (y : G) y.2
  calc (x : G) * (y * y') * (x : G)⁻¹ * ((y : G) * y')⁻¹
      = (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ * ((y : G) * ((x : G) * y' * (x : G)⁻¹ * (y' : G)⁻¹) *
          (y : G)⁻¹) := by group
    _ = _ := by rw [← hc, mul_inv_cancel_right]

theorem secComm_mul_left (x x' y : D) : secComm (V := V) (x * x') y = secComm x' y * secComm x y := by
  apply Subtype.ext
  simp only [secComm, Subgroup.coe_mul]
  have hc := hDV.out.central _ (comm_mem_V (V := V) x'.2 y.2) (x : G) x.2
  calc (x : G) * x' * y * ((x : G) * x')⁻¹ * (y : G)⁻¹
      = ((x : G) * ((x' : G) * y * (x' : G)⁻¹ * (y : G)⁻¹) * (x : G)⁻¹) *
          ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) := by group
    _ = _ := by rw [← hc, mul_inv_cancel_right]

theorem secComm_of_mem_right (x y : D) (hy : (y : G) ∈ V) : secComm (V := V) x y = 1 := by
  apply Subtype.ext
  simp only [secComm, OneMemClass.coe_one]
  rw [mul_assoc (x : G) y, hDV.out.central y hy _ (D.inv_mem x.2)]
  group

theorem secComm_of_mem_left (x y : D) (hx : (x : G) ∈ V) : secComm (V := V) x y = 1 := by
  apply Subtype.ext
  simp only [secComm, OneMemClass.coe_one]
  rw [hDV.out.central x hx y y.2]
  group

variable (f : V →* Multiplicative (ZMod 2))

@[expose] noncomputable def formRowQ (x : D) : secQ D V →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift (V.subgroupOf D)
    { toFun := fun y => f (secComm x y)
      map_one' := by rw [secComm_of_mem_right x 1 V.one_mem, map_one]
      map_mul' := fun y y' => by rw [secComm_mul_right, map_mul] }
    fun y hy => by
      rw [MonoidHom.mem_ker]
      change f (secComm x y) = 1
      rw [secComm_of_mem_right x y (Subgroup.mem_subgroupOf.mp hy), map_one]

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

@[expose] noncomputable def formRow (x : D) : secW D V →ₗ[ZMod 2] ZMod 2 :=
  { toFun := MonoidHom.toAdditiveLeft (formRowQ f x)
    map_add' := (MonoidHom.toAdditiveLeft (formRowQ f x)).map_add
    map_smul' := fun c w => by rcases zmod2_cases c with rfl | rfl <;> simp }

theorem formRow_mk (x y : D) : formRow f x (secMk y) = Multiplicative.toAdd (f (secComm x y)) :=
  rfl

theorem formRow_mul (x x' : D) : formRow f (x * x') = formRow f x' + formRow f x := by
  apply LinearMap.ext
  intro w
  obtain ⟨y, rfl⟩ := secMk_surjective w
  rw [LinearMap.add_apply, formRow_mk, formRow_mk, formRow_mk, secComm_mul_left, map_mul]
  rfl

theorem formRow_of_mem (x : D) (hx : (x : G) ∈ V) : formRow f x = 0 := by
  apply LinearMap.ext
  intro w
  obtain ⟨y, rfl⟩ := secMk_surjective w
  rw [formRow_mk, secComm_of_mem_left x y hx, map_one, LinearMap.zero_apply]
  rfl

@[expose] noncomputable def formQ : secQ D V →* Multiplicative (secW D V →ₗ[ZMod 2] ZMod 2) :=
  QuotientGroup.lift (V.subgroupOf D)
    { toFun := fun x => Multiplicative.ofAdd (formRow f x)
      map_one' := by rw [formRow_of_mem f 1 V.one_mem]; rfl
      map_mul' := fun x x' => by rw [formRow_mul, add_comm]; rfl }
    fun x hx => by
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd (formRow f x) = 1
      rw [formRow_of_mem f x (Subgroup.mem_subgroupOf.mp hx)]; rfl

@[expose] noncomputable def secForm : secW D V →ₗ[ZMod 2] secW D V →ₗ[ZMod 2] ZMod 2 :=
  { toFun := MonoidHom.toAdditiveLeft (formQ f)
    map_add' := (MonoidHom.toAdditiveLeft (formQ f)).map_add
    map_smul' := fun c w => by rcases zmod2_cases c with rfl | rfl <;> simp }

theorem secForm_mk (x y : D) :
    secForm f (secMk x) (secMk y) = Multiplicative.toAdd (f (secComm x y)) := rfl

theorem secForm_self (w : secW D V) : secForm f w w = 0 := by
  obtain ⟨x, rfl⟩ := secMk_surjective w
  rw [secForm_mk]
  have : secComm (V := V) x x = 1 := Subtype.ext (by simp [secComm])
  rw [this, map_one]; rfl

theorem secForm_secAct (n : G) (hn : n ∈ normalizer (D : Set G)) (hnV : n ∈ normalizer (V : Set G))
    (hc : ∀ v ∈ V, n * v * n⁻¹ = v) (w w' : secW D V) :
    secForm f (secAct n hn hnV w) (secAct n hn hnV w') = secForm f w w' := by
  obtain ⟨x, rfl⟩ := secMk_surjective w
  obtain ⟨y, rfl⟩ := secMk_surjective w'
  rw [secAct_mk, secAct_mk, secForm_mk, secForm_mk]
  congr 2
  apply Subtype.ext
  have h1 := hc _ (comm_mem_V (V := V) x.2 y.2)
  simp only [secComm, conjD, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← h1]
  group

omit hDV in
theorem exists_hom_ne_one {E : Subgroup G} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) {c : G} (hc : c ∈ E) (hc1 : c ≠ 1) :
    ∃ φ : E →* Multiplicative (ZMod 2), φ ⟨c, hc⟩ ≠ 1 := by
  let _ : CommGroup E := { mul_comm := fun x y => Subtype.ext (hcomm x x.2 y y.2) }
  have h2 : ∀ x : Additive E, 2 • x = 0 := fun x => by
    rw [two_nsmul]
    exact Subtype.ext (hsq _ (Additive.toMul x).2)
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule h2
  have hne : Additive.ofMul (⟨c, hc⟩ : E) ≠ 0 := fun h => hc1 (congrArg Subtype.val
    (Additive.ofMul.injective h))
  have : ∃ ψ : Module.Dual (ZMod 2) (Additive E), ψ (Additive.ofMul ⟨c, hc⟩) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp h)
  obtain ⟨ψ, hψ⟩ := this
  refine ⟨MonoidHom.toAdditiveLeft.symm ψ.toAddMonoidHom, ?_⟩
  intro h
  apply hψ
  exact congrArg Multiplicative.toAdd h

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
