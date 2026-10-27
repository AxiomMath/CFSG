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
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup

variable {G : Type*} [Group G]

theorem mem_map_conj {K : Subgroup G} {g a : G} :
    a ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * a * g ∈ K := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa [mul_assoc] using hb
  · intro h
    exact ⟨g⁻¹ * a * g, h, by simp [mul_assoc]⟩

theorem map_centralizer_singleton (e : G ≃* G) (a : G) :
    (centralizer ({a} : Set G)).map e.toMonoidHom = centralizer ({e a} : Set G) := by
  ext b
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [← map_mul, ← map_mul, hc]
  · intro hb
    refine ⟨e.symm b, ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hb

theorem card_conjOrbit_dvd (N : Subgroup G) (z : G) :
    Nat.card {t : G | ∃ n ∈ N, t = n * z * n⁻¹} ∣ Nat.card N := by
  let : MulAction N G := MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  have h : {t : G | ∃ n ∈ N, t = n * z * n⁻¹} = MulAction.orbit N z := by
    ext t
    simp only [Set.mem_ofPred_eq, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, by simp [MulAction.compHom_smul_def, ConjAct.smul_def]⟩
    · rintro ⟨⟨n, hn⟩, rfl⟩
      exact ⟨n, hn, by simp [MulAction.compHom_smul_def, ConjAct.smul_def]⟩
  rw [h, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

theorem card_mulAut_eq {E : Type*} [Group E] [Finite E] (hcomm : ∀ a b : E, a * b = b * a)
    (h2 : ∀ a : E, a ^ 2 = 1) {n : ℕ} (hcard : Nat.card E = 2 ^ n) :
    Nat.card (MulAut E) = Nat.card (GL (Fin n) (ZMod 2)) := by
  let : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  have hV : ∀ x : Additive E, (2 : ℕ) • x = 0 := fun x => by
    show Additive.ofMul (Additive.toMul x ^ 2) = 0
    rw [h2]
    rfl
  let : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule hV
  have : Module.Finite (ZMod 2) (Additive E) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 2) (Additive E) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    have h1 : Nat.card (Additive E) = Nat.card E := Nat.card_congr Additive.toMul
    rw [h1, hcard, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let toLin : (Additive E ≃+ Additive E) → (Additive E ≃ₗ[ZMod 2] Additive E) := fun f =>
    { toLinearMap := AddMonoidHom.toZModLinearMap 2 f.toAddMonoidHom
      invFun := f.symm
      left_inv := f.left_inv
      right_inv := f.right_inv }
  let e1 : MulAut E ≃ (Additive E ≃ₗ[ZMod 2] Additive E) :=
    { toFun := fun φ => toLin (MulEquiv.toAdditive φ)
      invFun := fun l => MulEquiv.toAdditive.symm l.toAddEquiv
      left_inv := fun φ => by ext a; rfl
      right_inv := fun l => by ext a; rfl }
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive E) hrank
  let e2 : (Additive E ≃ₗ[ZMod 2] Additive E) ≃ ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
    { toFun := fun l => b.equivFun.symm.trans (l.trans b.equivFun)
      invFun := fun l => b.equivFun.trans (l.trans b.equivFun.symm)
      left_inv := fun l => LinearEquiv.ext fun a => by
        simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      right_inv := fun l => LinearEquiv.ext fun a => by
        simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] }
  let e3 : GL (Fin n) (ZMod 2) ≃* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
    (Matrix.GeneralLinearGroup.toLin).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2))
  exact Nat.card_congr (e1.trans (e2.trans e3.toEquiv.symm))

theorem card_normalizer_dvd [Finite G] {E : Subgroup G}
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a ^ 2 = 1) {n : ℕ}
    (hcard : Nat.card E = 2 ^ n) (hcent : centralizer (E : Set G) ≤ E) :
    Nat.card (normalizer (E : Set G)) ∣ 2 ^ n * Nat.card (GL (Fin n) (ZMod 2)) := by
  let φ := E.normalizerMonoidHom
  have hker : Nat.card φ.ker ∣ 2 ^ n := by
    rw [← hcard]
    have hmem : ∀ g : φ.ker, ((g : normalizer (E : Set G)) : G) ∈ E := by
      intro g
      refine hcent ?_
      rw [mem_centralizer_iff]
      intro y hy
      have h := g.2
      rw [MonoidHom.mem_ker] at h
      have h' := congrArg (fun m : MulAut E => ((m ⟨y, hy⟩ : E) : G)) h
      simp only [φ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h'
      exact (mul_inv_eq_iff_eq_mul.1 h').symm
    let ι : φ.ker →* E :=
      { toFun := fun g => ⟨((g : normalizer (E : Set G)) : G), hmem g⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine card_dvd_of_injective ι fun g₁ g₂ h => ?_
    have := congrArg (fun e : E => (e : G)) h
    exact Subtype.ext (Subtype.ext this)
  have hrange : Nat.card φ.range ∣ Nat.card (GL (Fin n) (ZMod 2)) := by
    have hE : Nat.card (MulAut E) = Nat.card (GL (Fin n) (ZMod 2)) :=
      card_mulAut_eq (fun a b => Subtype.ext (hcomm a a.2 b b.2))
        (fun a => Subtype.ext (h2 a a.2)) hcard
    rw [← hE]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have hmul : Nat.card (normalizer (E : Set G)) = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker).trans (mul_comm _ _)
  rw [hmul]
  exact mul_dvd_mul hker hrange

theorem not_dvd_859_card : ¬ 859 ∣ 2 ^ 12 * Nat.card (GL (Fin 12) (ZMod 2)) := by
  rw [Matrix.card_GL_field, ZMod.card]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  norm_num

end CFSG.EvenSporadicStandard.TwoCo1
