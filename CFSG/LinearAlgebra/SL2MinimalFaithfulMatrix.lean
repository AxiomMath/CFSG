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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public section

open Matrix

namespace CFSG.SL2MinimalFaithful

section Unipotent

variable {F : Type*} [Field F]

@[expose] def unipotent (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_unipotent (t : F) :
    ((unipotent t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] :=
  rfl

theorem unipotent_add (s t : F) : unipotent (s + t) = unipotent s * unipotent t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipotent_zero : unipotent (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipotent]

theorem unipotent_injective :
    Function.Injective (unipotent : F → SpecialLinearGroup (Fin 2) F) := by
  intro s t h
  simpa [coe_unipotent] using
    congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h

@[expose] def unipotentHom : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun t := unipotent t.toAdd
  map_one' := unipotent_zero
  map_mul' s t := unipotent_add s.toAdd t.toAdd

theorem unipotentHom_injective : Function.Injective (unipotentHom (F := F)) := by
  intro s t h
  exact unipotent_injective (F := F) h

theorem map_unipotent (σ : F ≃+* F) (t : F) :
    SpecialLinearGroup.map σ.toRingHom (unipotent t) = unipotent (σ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipotent]

end Unipotent

theorem card_specialLinearGroup_fin_two (K : Type*) [Field K] [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

open scoped Pointwise in
theorem exists_conj_unipotent_mem {F : Type*} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ f) {U : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hU : Nat.card U = Nat.card F) :
    ∃ g : SpecialLinearGroup (Fin 2) F, ∀ t : F, g * unipotent t * g⁻¹ ∈ U := by
  have := Fact.mk hp
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcard
    omega
  have hpq : p ∣ Nat.card F := hcard ▸ dvd_pow_self p hf
  have hsyl : ∀ H : Subgroup (SpecialLinearGroup (Fin 2) F), Nat.card H = Nat.card F →
      IsPGroup p H ∧ ¬ p ∣ H.index := by
    intro H hH
    refine ⟨IsPGroup.of_card (hH.trans hcard), fun hdvd => ?_⟩
    have hind : H.index = Nat.card F ^ 2 - 1 := by
      have := H.card_mul_index
      rw [hH, card_specialLinearGroup_fin_two] at this
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : p ∣ Nat.card F ^ 2 - 1 + 1 := by
      rw [Nat.sub_add_cancel h1]
      exact dvd_pow hpq two_ne_zero
    rw [hind] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hdvd).mp h2))
  have hU₀ : Nat.card (unipotentHom (F := F)).range = Nat.card F :=
    (Nat.card_congr (MonoidHom.ofInjective unipotentHom_injective).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.toAdd)
  obtain ⟨hU1, hU2⟩ := hsyl U hU
  obtain ⟨h01, h02⟩ := hsyl _ hU₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) F)
    (h01.toSylow h02) (hU1.toSylow hU2)
  refine ⟨g, fun t => ?_⟩
  have hmem : MulAut.conj g • unipotent t ∈
      MulAut.conj g • ((h01.toSylow h02 : Sylow p _) : Subgroup (SpecialLinearGroup (Fin 2) F)) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ ⟨Multiplicative.ofAdd t, rfl⟩
  rwa [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe, MulAut.smul_def,
    MulAut.conj_apply] at hmem

theorem semilinear_centralizer_sylow {F : Type*} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ f) {U : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hU : Nat.card U = Nat.card F) (G : GL (Fin 2) F) (σ : F ≃+* F)
    (h : ∀ A ∈ U, G * SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom A) * G⁻¹ =
      SpecialLinearGroup.toGL A) :
    σ = RingEquiv.refl F ∧ ∃ A₀ ∈ U, ∃ c : Fˣ,
      G = GeneralLinearGroup.scalar (Fin 2) c * SpecialLinearGroup.toGL A₀ := by
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem hp hcard hU
  obtain ⟨G', hG'⟩ : ∃ G' : GL (Fin 2) F, G' = (SpecialLinearGroup.toGL g)⁻¹ * G *
      SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom g) := ⟨_, rfl⟩
  have key : ∀ t : F, G' * SpecialLinearGroup.toGL (unipotent (σ t)) =
      SpecialLinearGroup.toGL (unipotent t) * G' := by
    intro t
    have h1 := h _ (hg t)
    simp only [map_mul, map_inv, map_unipotent] at h1
    have e : SpecialLinearGroup.toGL (unipotent t) = (SpecialLinearGroup.toGL g)⁻¹ *
        (SpecialLinearGroup.toGL g * SpecialLinearGroup.toGL (unipotent t) *
          (SpecialLinearGroup.toGL g)⁻¹) * SpecialLinearGroup.toGL g := by
      group
    rw [e, ← h1, hG']
    group
  set M : Matrix (Fin 2) (Fin 2) F := (G' : Matrix (Fin 2) (Fin 2) F) with hM
  have km : ∀ t : F, M * !![1, σ t; 0, 1] = !![1, t; 0, 1] * M := by
    intro t
    simpa [coe_unipotent] using congrArg Units.val (key t)
  have e00 := congrFun (congrFun (km 1) 0) 0
  have e01 := congrFun (congrFun (km 1) 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have h11 : M 1 1 = M 0 0 := by linear_combination -e01
  have hdet : M.det ≠ 0 := by
    rw [hM, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hα : M 0 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [Matrix.det_fin_two, e00, h11, h0]
    ring
  have hσt : ∀ t, σ t = t := by
    intro t
    have e := congrFun (congrFun (km t) 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e
    apply mul_left_cancel₀ hα
    linear_combination e + t * h11
  have hσ : σ = RingEquiv.refl F := RingEquiv.ext hσt
  refine ⟨hσ, g * unipotent (M 0 1 / M 0 0) * g⁻¹, hg _, Units.mk0 (M 0 0) hα, ?_⟩
  have hmap : SpecialLinearGroup.map σ.toRingHom g = g := by
    ext i j
    simp [hσt]
  rw [hmap] at hG'
  have hG'' : G' = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (M 0 0) hα) *
      SpecialLinearGroup.toGL (unipotent (M 0 1 / M 0 0)) := by
    apply Units.ext
    show M = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two, e00, h11, mul_div_cancel₀ _ hα]
  have hcomm : ∀ X : GL (Fin 2) F, GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (M 0 0) hα) * X =
      X * GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (M 0 0) hα) := fun X =>
    Units.ext (by
      rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
      exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq)
  have hG : G = SpecialLinearGroup.toGL g * G' * (SpecialLinearGroup.toGL g)⁻¹ := by
    rw [hG']
    group
  rw [hG, hG'', map_mul, map_mul, map_inv, ← mul_assoc (SpecialLinearGroup.toGL g),
    ← hcomm (SpecialLinearGroup.toGL g)]
  simp only [mul_assoc]

theorem exists_not_commute_of_orderOf {F : Type*} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hcard : Nat.card F = p ^ f) (h3 : 3 < Nat.card F)
    {U : Subgroup (SpecialLinearGroup (Fin 2) F)} (hU : Nat.card U = Nat.card F)
    {t : SpecialLinearGroup (Fin 2) F} (ht : orderOf t = Nat.card F - 1) :
    ∃ A ∈ U, t * A ≠ A * t := by
  by_contra hcon
  push Not at hcon
  have hcond : ∀ A ∈ U, SpecialLinearGroup.toGL t *
      SpecialLinearGroup.toGL (SpecialLinearGroup.map (RingEquiv.refl F).toRingHom A) *
        (SpecialLinearGroup.toGL t)⁻¹ = SpecialLinearGroup.toGL A := by
    intro A hA
    change SpecialLinearGroup.toGL t * SpecialLinearGroup.toGL A *
      (SpecialLinearGroup.toGL t)⁻¹ = _
    rw [← map_mul, hcon A hA, map_mul, mul_inv_cancel_right]
  obtain ⟨-, A₀, hA₀, c, hc⟩ := semilinear_centralizer_sylow hp hcard hU _ _ hcond
  have hc2 : c ^ 2 = 1 := by
    have h := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F).det) hc
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.det_mul] at h
    change (t : Matrix (Fin 2) (Fin 2) F).det = _ * (A₀ : Matrix (Fin 2) (Fin 2) F).det at h
    rw [Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe, mul_one,
      Matrix.det_fin_two] at h
    simp [Matrix.scalar_apply] at h
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
    exact h.symm
  have hcomm : Commute (GeneralLinearGroup.scalar (Fin 2) c) (SpecialLinearGroup.toGL A₀) :=
    Units.ext (by
      rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
      exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq)
  have ht2 : t ^ 2 = A₀ ^ 2 := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow, map_pow, hc, hcomm.mul_pow, ← map_pow, hc2, map_one, one_mul]
  have hA₀ : A₀ ^ Nat.card F = 1 := by
    have h := Subgroup.orderOf_dvd_natCard U hA₀
    rw [hU] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have htq : t ^ (2 * Nat.card F) = 1 := by
    rw [pow_mul, ht2, ← pow_mul, mul_comm, pow_mul, hA₀, one_pow]
  have hdvd : Nat.card F - 1 ∣ 2 * Nat.card F := ht ▸ orderOf_dvd_of_pow_eq_one htq
  have hcop : Nat.Coprime (Nat.card F - 1) (Nat.card F) := by
    obtain ⟨k, hk⟩ : ∃ k, Nat.card F = k + 1 := ⟨Nat.card F - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right k)
  have := Nat.le_of_dvd two_pos (hcop.dvd_of_dvd_mul_right hdvd)
  omega

end CFSG.SL2MinimalFaithful
