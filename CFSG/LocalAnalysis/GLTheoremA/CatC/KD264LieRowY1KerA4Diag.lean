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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix

variable (K : Type) [Field K]

abbrev mu3 : Subgroup Kˣ := rootsOfUnity 3 K

theorem mem_mu3 {u : Kˣ} : u ∈ mu3 K ↔ (u : K) ^ 3 = 1 := by
  rw [mem_rootsOfUnity]
  constructor
  · intro h
    simpa using congrArg Units.val h
  · intro h
    exact Units.ext (by simpa using h)

@[expose] def dGroup : Subgroup (Fin 4 → Kˣ) where
  carrier := {d | (∀ i, d i ∈ mu3 K) ∧ ∏ i, d i = 1}
  one_mem' := ⟨fun _ => one_mem _, by simp⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨fun i => mul_mem (ha.1 i) (hb.1 i), by simp [Finset.prod_mul_distrib, ha.2, hb.2]⟩
  inv_mem' := fun {a} ha =>
    ⟨fun i => inv_mem (ha.1 i), by simp [Finset.prod_inv_distrib, ha.2]⟩

@[expose] def diagM (d : Fin 4 → Kˣ) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal fun i => (d i : K)

theorem det_diagM {d : Fin 4 → Kˣ} (h : ∏ i, d i = 1) : (diagM K d).det = 1 := by
  rw [diagM, Matrix.det_diagonal]
  have h' := congrArg (fun u : Kˣ => (u : K)) h
  simpa using h'

theorem diagM_one : diagM K (1 : Fin 4 → Kˣ) = 1 := by
  simp [diagM]

theorem diagM_mul (a b : Fin 4 → Kˣ) : diagM K (a * b) = diagM K a * diagM K b := by
  simp [diagM, Matrix.diagonal_mul_diagonal]

@[expose] def diagHom : dGroup K →* Matrix.SpecialLinearGroup (Fin 4) K where
  toFun d := ⟨diagM K d.1, det_diagM K d.2.2⟩
  map_one' := Subtype.ext (diagM_one K)
  map_mul' a b := Subtype.ext (diagM_mul K a.1 b.1)

theorem diagHom_apply_coe (d : dGroup K) :
    ((diagHom K d : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagM K d.1 := rfl

theorem diagHom_injective : Function.Injective (diagHom K) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  have h1 : ∀ i, ((d.1 i : Kˣ) : K) = 1 := by
    intro i
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 4) K =>
      (x : Matrix (Fin 4) (Fin 4) K) i i) hd
    simpa [diagHom_apply_coe, diagM, Matrix.diagonal_apply_eq] using this
  apply Subtype.ext
  funext i
  exact Units.ext (h1 i)

@[expose] def DiagSL : Subgroup (Matrix.SpecialLinearGroup (Fin 4) K) := (diagHom K).range

theorem diagHom_pow_three (d : dGroup K) : (diagHom K d) ^ 3 = 1 := by
  rw [← map_pow]
  have h3 : d ^ 3 = 1 := by
    apply Subtype.ext
    funext i
    have hi : (d.1 i) ^ 3 = 1 := Units.ext (by simpa using (mem_mu3 K).mp (d.2.1 i))
    simpa using hi
  rw [h3, map_one]

theorem card_mu3 {ζ : K} (hζ : IsPrimitiveRoot ζ 3) : Nat.card (mu3 K) = 3 :=
  hζ.card_rootsOfUnity

theorem card_dGroup_le [Finite K] (hμ : Nat.card (mu3 K) = 3) : Nat.card (dGroup K) ≤ 27 := by
  have hinj : Function.Injective (fun d : dGroup K =>
      (fun i : Fin 3 => (⟨d.1 i.castSucc, d.2.1 _⟩ : mu3 K))) := by
    intro d e hde
    have h3 : ∀ i : Fin 3, d.1 i.castSucc = e.1 i.castSucc := fun i => by
      have := congrArg (fun t : Fin 3 → mu3 K => ((t i : mu3 K) : Kˣ)) hde
      simpa using this
    have hd4 : d.1 (Fin.last 3) = (d.1 0 * d.1 1 * d.1 2)⁻¹ := by
      have h := d.2.2
      rw [Fin.prod_univ_four] at h
      exact eq_inv_of_mul_eq_one_right h
    have he4 : e.1 (Fin.last 3) = (e.1 0 * e.1 1 * e.1 2)⁻¹ := by
      have h := e.2.2
      rw [Fin.prod_univ_four] at h
      exact eq_inv_of_mul_eq_one_right h
    have key : ∀ i : Fin 4, d.1 i = e.1 i := by
      intro i
      refine Fin.lastCases ?_ (fun j => h3 j) i
      have h0 : d.1 0 = e.1 0 := h3 0
      have h1 : d.1 1 = e.1 1 := h3 1
      have h2 : d.1 2 = e.1 2 := h3 2
      rw [hd4, he4, h0, h1, h2]
    apply Subtype.ext
    exact funext key
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fun, hμ] at this
  simpa using this

@[expose] def F0d : Subgroup (dGroup K) where
  carrier := {d | d.1 0 = d.1 1}
  one_mem' := rfl
  mul_mem' := fun {a b} ha hb => by
    have ha' : a.1 0 = a.1 1 := ha
    have hb' : b.1 0 = b.1 1 := hb
    show (a.1 * b.1) 0 = (a.1 * b.1) 1
    rw [Pi.mul_apply, Pi.mul_apply, ha', hb']
  inv_mem' := fun {a} ha => by
    have ha' : a.1 0 = a.1 1 := ha
    show (a.1)⁻¹ 0 = (a.1)⁻¹ 1
    rw [Pi.inv_apply, Pi.inv_apply, ha']

theorem vec_mem (b c : mu3 K) :
    (![(b : Kˣ) * (c : Kˣ), (b : Kˣ) * (c : Kˣ), (b : Kˣ), (c : Kˣ)] : Fin 4 → Kˣ) ∈
      dGroup K := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · exact mul_mem b.2 c.2
    · exact mul_mem b.2 c.2
    · exact b.2
    · exact c.2
  · have hb := (mem_mu3 K).mp b.2
    have hc := (mem_mu3 K).mp c.2
    rw [Fin.prod_univ_four]
    apply Units.ext
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Units.val_mul, Units.val_one]
    linear_combination (((c : Kˣ) : K) ^ 3) * hb + hc

@[expose] def Φ0 (bc : mu3 K × mu3 K) : dGroup K :=
  ⟨![(bc.1 : Kˣ) * (bc.2 : Kˣ), (bc.1 : Kˣ) * (bc.2 : Kˣ), (bc.1 : Kˣ), (bc.2 : Kˣ)],
    vec_mem K bc.1 bc.2⟩

theorem Φ0_mem_F0d (bc : mu3 K × mu3 K) : Φ0 K bc ∈ F0d K := rfl

theorem Φ0_injective : Function.Injective (Φ0 K) := by
  intro x y hxy
  have h2 := congrArg (fun d : dGroup K => (d.1 2 : Kˣ)) hxy
  have h3 := congrArg (fun d : dGroup K => (d.1 3 : Kˣ)) hxy
  simp only [Φ0] at h2 h3
  exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)

theorem Φ0_surjective : Function.Surjective (fun bc : mu3 K × mu3 K =>
    (⟨Φ0 K bc, Φ0_mem_F0d K bc⟩ : F0d K)) := by
  rintro ⟨d, hd⟩
  have hd0 : d.1 0 = d.1 1 := hd
  obtain ⟨hmu, hprod⟩ := d.2
  have hb : d.1 2 ∈ mu3 K := hmu 2
  have hc : d.1 3 ∈ mu3 K := hmu 3
  refine ⟨(⟨d.1 2, hb⟩, ⟨d.1 3, hc⟩), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext i
  have hd0' : d.1 0 = d.1 2 * d.1 3 := by
    have hz0 := (mem_mu3 K).mp (hmu 0)
    have hprod' : d.1 0 * d.1 1 * d.1 2 * d.1 3 = 1 := by
      rw [← Fin.prod_univ_four]; exact hprod
    rw [← hd0] at hprod'
    apply Units.ext
    have hp := congrArg Units.val hprod'
    simp only [Units.val_mul, Units.val_one] at hp
    have hz := (mem_mu3 K).mp (hmu 0)
    simp only [Units.val_mul]
    linear_combination (-(((d.1 0 : Kˣ) : K))) * hp + (((d.1 2 : Kˣ) : K) * ((d.1 3 : Kˣ) : K)) * hz
  fin_cases i
  · simp [Φ0, hd0']
  · simp [Φ0, ← hd0, hd0']
  · simp [Φ0]
  · simp [Φ0]

theorem card_F0d {ζ : K} (hζ : IsPrimitiveRoot ζ 3) : Nat.card (F0d K) = 9 := by
  have hbij := Equiv.ofBijective (fun bc : mu3 K × mu3 K =>
      (⟨Φ0 K bc, Φ0_mem_F0d K bc⟩ : F0d K))
    ⟨fun x y h => Φ0_injective K (congrArg Subtype.val h), Φ0_surjective K⟩
  have h1 : Nat.card (mu3 K × mu3 K) = 9 := by
    rw [Nat.card_prod, card_mu3 K hζ]
  rw [← h1]
  exact Nat.card_congr hbij.symm

@[expose] def F0 : Subgroup (Matrix.SpecialLinearGroup (Fin 4) K) := (F0d K).map (diagHom K)

theorem card_F0 {ζ : K} (hζ : IsPrimitiveRoot ζ 3) : Nat.card (F0 K) = 9 := by
  rw [F0, Subgroup.card_map_of_injective (diagHom_injective K), card_F0d K hζ]

theorem F0_le_DiagSL : F0 K ≤ DiagSL K :=
  Subgroup.map_le_range _ _

theorem card_DiagSL_le [Finite K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    Nat.card (DiagSL K) ≤ 27 := by
  have h := Nat.card_congr (MonoidHom.ofInjective (diagHom_injective K)).symm.toEquiv
  rw [DiagSL, h]
  exact card_dGroup_le K (card_mu3 K hζ)

@[expose] def zmu {ζ : K} (hζ : IsPrimitiveRoot ζ 3) : mu3 K :=
  ⟨Units.mk0 ζ (hζ.ne_zero (by norm_num)), by
    rw [mem_mu3]
    simpa using hζ.pow_eq_one⟩

@[expose] def tElt {ζ : K} (hζ : IsPrimitiveRoot ζ 3) : Matrix.SpecialLinearGroup (Fin 4) K :=
  diagHom K (Φ0 K (zmu K hζ, zmu K hζ ^ 2))

theorem tElt_mem {ζ : K} (hζ : IsPrimitiveRoot ζ 3) : tElt K hζ ∈ F0 K :=
  Subgroup.mem_map_of_mem _ (Φ0_mem_F0d K _)

theorem tElt_apply {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (i : Fin 4) :
    ((tElt K hζ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i =
      (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) i := by
  unfold tElt
  rw [diagHom_apply_coe]
  have hz3 : ζ * ζ ^ 2 = 1 := by
    rw [← pow_succ']; simpa using hζ.pow_eq_one
  fin_cases i <;> simp [diagM, Φ0, zmu, hz3]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
