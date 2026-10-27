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
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.OutcomeLocal

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod2_add_self {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (v : M) : v + v = 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  calc v + v = (1 + 1 : ZMod 2) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [h, zero_smul]

theorem zmod2_neg {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (v : M) : -v = v :=
  neg_eq_of_add_eq_zero_left (zmod2_add_self v)

theorem zmod2_scalar_add_self (c : ZMod 2) : c + c = 0 := by
  revert c
  decide

theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem exists_apply_eq_one {φ : Dual (ZMod 2) V} (hφ : φ ≠ 0) : ∃ v, φ v = 1 := by
  by_contra hall
  refine hφ (LinearMap.ext fun v => ?_)
  rcases zmod2_eq_zero_or_one (φ v) with h | h
  · exact h
  · exact absurd ⟨v, h⟩ hall

@[expose] def commutatorSpace (t : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    Submodule (ZMod 2) V :=
  LinearMap.range (LinearMap.id + (t : V →ₗ[ZMod 2] V))

@[expose] def IsF2Transvection (t : LinearMap.GeneralLinearGroup (ZMod 2) V) : Prop :=
  t ≠ 1 ∧ finrank (ZMod 2) (commutatorSpace t) = 1

@[expose] def tv (φ : Dual (ZMod 2) V) (a : V) (h : φ a = 0) :
    LinearMap.GeneralLinearGroup (ZMod 2) V :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection h)

theorem tv_apply (φ : Dual (ZMod 2) V) (a : V) (h : φ a = 0) (v : V) :
    (tv φ a h : V →ₗ[ZMod 2] V) v = v + φ v • a :=
  rfl

theorem tv_ext {g h : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hgh : ∀ v, (g : V →ₗ[ZMod 2] V) v = (h : V →ₗ[ZMod 2] V) v) : g = h :=
  Units.ext (LinearMap.ext hgh)

theorem tv_zero_left (a : V) (h : (0 : Dual (ZMod 2) V) a = 0) : tv 0 a h = 1 :=
  tv_ext fun v => by simp [tv_apply]

theorem tv_zero_right (φ : Dual (ZMod 2) V) (h : φ 0 = 0) : tv φ 0 h = 1 :=
  tv_ext fun v => by simp [tv_apply]

theorem tv_mul_tv_center (φ ψ : Dual (ZMod 2) V) (a : V) (h : φ a = 0) (h' : ψ a = 0)
    (h'' : (φ + ψ) a = 0) : tv φ a h * tv ψ a h' = tv (φ + ψ) a h'' :=
  tv_ext fun v => by
    change (tv φ a h : V →ₗ[ZMod 2] V) ((tv ψ a h' : V →ₗ[ZMod 2] V) v) = _
    rw [tv_apply, tv_apply, tv_apply, map_add, LinearMap.map_smul, h, smul_zero, add_zero,
      LinearMap.add_apply, add_smul]
    abel

theorem tv_mul_tv_axis (φ : Dual (ZMod 2) V) (a b : V) (h : φ a = 0) (h' : φ b = 0)
    (h'' : φ (a + b) = 0) : tv φ a h * tv φ b h' = tv φ (a + b) h'' :=
  tv_ext fun v => by
    change (tv φ a h : V →ₗ[ZMod 2] V) ((tv φ b h' : V →ₗ[ZMod 2] V) v) = _
    rw [tv_apply, tv_apply, tv_apply, map_add, LinearMap.map_smul, h', smul_zero, add_zero,
      smul_add]
    abel

theorem tv_mul_self (φ : Dual (ZMod 2) V) (a : V) (h : φ a = 0) : tv φ a h * tv φ a h = 1 :=
  tv_ext fun v => by
    change (tv φ a h : V →ₗ[ZMod 2] V) ((tv φ a h : V →ₗ[ZMod 2] V) v) = v
    rw [tv_apply, tv_apply, map_add, LinearMap.map_smul, h, smul_zero, add_zero, add_assoc,
      zmod2_add_self, add_zero]

theorem tv_inv (φ : Dual (ZMod 2) V) (a : V) (h : φ a = 0) : (tv φ a h)⁻¹ = tv φ a h :=
  inv_eq_of_mul_eq_one_right (tv_mul_self φ a h)

theorem conj_tv (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (φ : Dual (ZMod 2) V) (a : V)
    (h : φ a = 0) (h' : (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V)) ((g : V →ₗ[ZMod 2] V) a) = 0) :
    g * tv φ a h * g⁻¹ = tv (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V)) ((g : V →ₗ[ZMod 2] V) a) h' :=
  tv_ext fun v => by
    change (g : V →ₗ[ZMod 2] V) ((tv φ a h : V →ₗ[ZMod 2] V)
      (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v)) = _
    rw [tv_apply, tv_apply, map_add, map_smul, LinearMap.comp_apply]
    congr 1
    change ((g * g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = v
    rw [mul_inv_cancel]
    rfl

theorem comp_tv (ψ χ : Dual (ZMod 2) V) (c : V) (h : χ c = 0) :
    ψ ∘ₗ (tv χ c h : V →ₗ[ZMod 2] V) = ψ + ψ c • χ := by
  ext v
  simp only [LinearMap.comp_apply, tv_apply, map_add, map_smul, smul_eq_mul, LinearMap.add_apply,
    LinearMap.smul_apply, mul_comm]

theorem tv_ne_one {φ : Dual (ZMod 2) V} {a : V} (h : φ a = 0) (hφ : φ ≠ 0) (ha : a ≠ 0) :
    tv φ a h ≠ 1 := by
  intro h1
  obtain ⟨v, hv1⟩ := exists_apply_eq_one hφ
  have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
    (g : V →ₗ[ZMod 2] V) v) h1
  simp only [tv_apply, hv1, one_smul] at this
  exact ha (by simpa using this)

theorem commutatorSpace_tv {φ : Dual (ZMod 2) V} {a : V} (h : φ a = 0) (hφ : φ ≠ 0) :
    commutatorSpace (tv φ a h) = Submodule.span (ZMod 2) {a} := by
  obtain ⟨v, hv1⟩ := exists_apply_eq_one hφ
  have happ : ∀ w, ((LinearMap.id + (tv φ a h : V →ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)) w =
      φ w • a := fun w => by
    rw [LinearMap.add_apply, LinearMap.id_apply, tv_apply, ← add_assoc, zmod2_add_self,
      zero_add]
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    rw [happ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨v, by rw [happ, hv1, one_smul]⟩

theorem isF2Transvection_iff (t : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    IsF2Transvection t ↔ ∃ (φ : Dual (ZMod 2) V) (a : V) (h : φ a = 0), φ ≠ 0 ∧ a ≠ 0 ∧
      t = tv φ a h := by
  constructor
  · rintro ⟨ht1, hrank⟩
    have hne : commutatorSpace t ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hrank
      exact zero_ne_one hrank
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hrank ha ha0
    set T : V →ₗ[ZMod 2] V := LinearMap.id + (t : V →ₗ[ZMod 2] V) with hT
    have hmem : ∀ w, T w ∈ Submodule.span (ZMod 2) {a} := fun w => by
      rw [← hspan]
      exact ⟨w, rfl⟩
    let e := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V a ha0
    let φ : Dual (ZMod 2) V := e.symm.toLinearMap ∘ₗ T.codRestrict _ hmem
    have hφ : ∀ w, T w = φ w • a := fun w => by
      have h1 := e.apply_symm_apply ⟨T w, hmem w⟩
      have h2 := congrArg Subtype.val h1
      rw [LinearEquiv.toSpanNonzeroSingleton_apply] at h2
      exact h2.symm
    have htw : ∀ w, (t : V →ₗ[ZMod 2] V) w = w + φ w • a := fun w => by
      have := hφ w
      rw [hT, LinearMap.add_apply, LinearMap.id_apply] at this
      calc (t : V →ₗ[ZMod 2] V) w = w + (w + (t : V →ₗ[ZMod 2] V) w) := by
            rw [← add_assoc, zmod2_add_self, zero_add]
        _ = w + φ w • a := by rw [this]
    have hφa : φ a = 0 := by
      rcases zmod2_eq_zero_or_one (φ a) with h0 | h1
      · exact h0
      · exfalso
        have hta : (t : V →ₗ[ZMod 2] V) a = 0 := by rw [htw, h1, one_smul, zmod2_add_self]
        have hinj : Function.Injective (t : V →ₗ[ZMod 2] V) := by
          intro x y hxy
          have := congrArg (((t⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
            V →ₗ[ZMod 2] V)) hxy
          simpa [← Module.End.mul_apply, ← Units.val_mul] using this
        exact ha0 (hinj (by rw [hta, map_zero]))
    have htv : t = tv φ a hφa := tv_ext fun w => by rw [htw, tv_apply]
    refine ⟨φ, a, hφa, fun hφ0 => ht1 (htv.trans (tv_ext fun w => ?_)), ha0, htv⟩
    rw [tv_apply, hφ0]
    simp
  · rintro ⟨φ, a, h, hφ, ha, rfl⟩
    refine ⟨tv_ne_one h hφ ha, ?_⟩
    rw [commutatorSpace_tv h hφ, finrank_span_singleton ha]

theorem tv_eq_tv_iff {φ ψ : Dual (ZMod 2) V} {a b : V} (h : φ a = 0) (h' : ψ b = 0)
    (hφ : φ ≠ 0) (ha : a ≠ 0) : tv φ a h = tv ψ b h' ↔ φ = ψ ∧ a = b := by
  constructor
  · intro heq
    have happ : ∀ v, φ v • a = ψ v • b := fun v => by
      have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
        (g : V →ₗ[ZMod 2] V) v) heq
      simpa [tv_apply] using this
    obtain ⟨v, hv1⟩ := exists_apply_eq_one hφ
    have hψv : ψ v = 1 := by
      rcases zmod2_eq_zero_or_one (ψ v) with h0 | h1
      · exfalso
        have := happ v
        rw [hv1, h0, one_smul, zero_smul] at this
        exact ha this
      · exact h1
    have hab : a = b := by
      have := happ v
      rwa [hv1, hψv, one_smul, one_smul] at this
    subst hab
    refine ⟨LinearMap.ext fun w => ?_, rfl⟩
    have := happ w
    rcases zmod2_eq_zero_or_one (φ w) with h0 | h1 <;>
      rcases zmod2_eq_zero_or_one (ψ w) with h0' | h1'
    · rw [h0, h0']
    · rw [h0, h1', zero_smul, one_smul] at this
      exact absurd this.symm ha
    · rw [h1, h0', zero_smul, one_smul] at this
      exact absurd this ha
    · rw [h1, h1']
  · rintro ⟨rfl, rfl⟩
    rfl

@[expose] def InG (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (φ : Dual (ZMod 2) V) (a : V) : Prop :=
  ∃ h : φ a = 0, tv φ a h ∈ G

variable {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}

theorem InG.apply_eq_zero {φ : Dual (ZMod 2) V} {a : V} (hφa : InG G φ a) : φ a = 0 :=
  hφa.1

theorem inG_zero_left (a : V) : InG G 0 a :=
  ⟨by simp, by rw [tv_zero_left]; exact G.one_mem⟩

theorem inG_zero_right (φ : Dual (ZMod 2) V) : InG G φ 0 :=
  ⟨by simp, by rw [tv_zero_right]; exact G.one_mem⟩

theorem InG.add_left {φ ψ : Dual (ZMod 2) V} {a : V} (hφ : InG G φ a) (hψ : InG G ψ a) :
    InG G (φ + ψ) a := by
  obtain ⟨h, hmem⟩ := hφ
  obtain ⟨h', hmem'⟩ := hψ
  have h'' : (φ + ψ) a = 0 := by simp [h, h']
  exact ⟨h'', tv_mul_tv_center φ ψ a h h' h'' ▸ G.mul_mem hmem hmem'⟩

theorem InG.add_right {φ : Dual (ZMod 2) V} {a b : V} (ha : InG G φ a) (hb : InG G φ b) :
    InG G φ (a + b) := by
  obtain ⟨h, hmem⟩ := ha
  obtain ⟨h', hmem'⟩ := hb
  have h'' : φ (a + b) = 0 := by simp [h, h']
  exact ⟨h'', tv_mul_tv_axis φ a b h h' h'' ▸ G.mul_mem hmem hmem'⟩

theorem InG.conj {φ : Dual (ZMod 2) V} {a : V} (hφa : InG G φ a)
    {g : LinearMap.GeneralLinearGroup (ZMod 2) V} (hg : g ∈ G) :
    InG G (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V))
      ((g : V →ₗ[ZMod 2] V) a) := by
  obtain ⟨h, hmem⟩ := hφa
  have h' : (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V))
      ((g : V →ₗ[ZMod 2] V) a) = 0 := by
    change φ (((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) a) = 0
    rw [inv_mul_cancel]
    exact h
  exact ⟨h', conj_tv g φ a h h' ▸ G.mul_mem (G.mul_mem hg hmem) (G.inv_mem hg)⟩

theorem InG.conj_tv {φ χ : Dual (ZMod 2) V} {a c : V} (hφa : InG G φ a) (hχc : InG G χ c) :
    InG G (φ + φ c • χ) (a + χ a • c) := by
  obtain ⟨hc, hmem⟩ := hχc
  have h := hφa.conj hmem
  rwa [tv_inv, comp_tv, tv_apply] at h

theorem InG.of_dihedral {φ ψ : Dual (ZMod 2) V} {a b : V} (hφa : InG G φ a) (hψb : InG G ψ b)
    (hφb : φ b = 1) (hψa : ψ a = 0) : InG G ψ a := by
  have h := hφa.conj_tv hψb
  rw [hφb, one_smul, hψa, zero_smul, add_zero] at h
  have h2 := hφa.add_left h
  have hφφ : φ + φ = 0 := LinearMap.ext fun v => by
    rw [LinearMap.add_apply, LinearMap.zero_apply]
    exact zmod2_scalar_add_self (φ v)
  rwa [← add_assoc, hφφ, zero_add] at h2

@[expose] def centerForms (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) (a : V) :
    Submodule (ZMod 2) (Dual (ZMod 2) V) where
  carrier := {φ | InG G φ a}
  add_mem' := InG.add_left
  zero_mem' := inG_zero_left a
  smul_mem' c φ hφ := by
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul]
      exact inG_zero_left a
    · rwa [one_smul]

theorem mem_centerForms {a : V} {φ : Dual (ZMod 2) V} : φ ∈ centerForms G a ↔ InG G φ a :=
  Iff.rfl

@[expose] def axisVectors (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (φ : Dual (ZMod 2) V) : Submodule (ZMod 2) V where
  carrier := {a | InG G φ a}
  add_mem' := InG.add_right
  zero_mem' := inG_zero_right φ
  smul_mem' c a ha := by
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul]
      exact inG_zero_right φ
    · rwa [one_smul]

theorem mem_axisVectors {a : V} {φ : Dual (ZMod 2) V} : a ∈ axisVectors G φ ↔ InG G φ a :=
  Iff.rfl

end CFSG.ComponentClassification.OutcomeLocal
