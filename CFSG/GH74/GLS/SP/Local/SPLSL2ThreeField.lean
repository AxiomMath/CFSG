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
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.GLS.SP.Local.SL2Three

open Matrix

variable {F : Type*} [Field F]

theorem eq_zero_of_sum_eq_zero (σ : F ≃+* F) (c : ℕ → F)
    (h : ∀ a : F, ∑ i ∈ Finset.range (orderOf σ), c i * (σ ^ i) a = 0) :
    ∀ i < orderOf σ, c i = 0 := by
  classical
  let f : Fin (orderOf σ) → (Fˣ →* F) := fun i =>
    ((σ ^ (i : ℕ) : F ≃+* F) : F →+* F).toMonoidHom.comp (Units.coeHom F)
  have hf : Function.Injective f := by
    intro i j hij
    have hx : ∀ x : F, (σ ^ (i : ℕ)) x = (σ ^ (j : ℕ)) x := by
      intro x
      by_cases hx0 : x = 0
      · simp [hx0]
      · exact DFunLike.congr_fun hij (Units.mk0 x hx0)
    have : σ ^ (i : ℕ) = σ ^ (j : ℕ) := RingEquiv.ext hx
    exact Fin.ext (pow_injOn_Iio_orderOf (by simp) (by simp) this)
  have hli : LinearIndependent F (fun i => (f i : Fˣ → F)) :=
    (linearIndependent_monoidHom Fˣ F).comp f hf
  intro i hi
  have key := Fintype.linearIndependent_iff.1 hli (fun j => c j) ?_ ⟨i, hi⟩
  · exact key
  · ext x
    have := h x
    rw [← Fin.sum_univ_eq_sum_range (fun i => c i * (σ ^ i) x)] at this
    simpa [f, Finset.sum_apply] using this

theorem exists_fixed_vector {ι : Type*} (σ : F ≃+* F) (hs0 : 0 < orderOf σ)
    (Φ : (ι → F) →+ (ι → F)) (hΦ : ∀ (a : F) (v : ι → F), Φ (a • v) = σ a • Φ v)
    (hΦs : (⇑Φ)^[orderOf σ] = id) (v : ι → F) (hv : v ≠ 0) :
    ∃ u : ι → F, u ≠ 0 ∧ Φ u = u := by
  have hiter : ∀ (i : ℕ) (a : F) (x : ι → F), (⇑Φ)^[i] (a • x) = (σ ^ i) a • (⇑Φ)^[i] x := by
    intro i
    induction i with
    | zero => intro a x; simp
    | succ i ih =>
      intro a x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hΦ, pow_succ']
      rfl
  let u : F → (ι → F) := fun a => ∑ i ∈ Finset.range (orderOf σ), (⇑Φ)^[i] (a • v)
  have hfix : ∀ a, Φ (u a) = u a := by
    intro a
    simp only [u, map_sum]
    have h1 := Finset.sum_range_succ' (fun i => (⇑Φ)^[i] (a • v)) (orderOf σ)
    have h2 := Finset.sum_range_succ (fun i => (⇑Φ)^[i] (a • v)) (orderOf σ)
    have h3 : (⇑Φ)^[orderOf σ] (a • v) = (⇑Φ)^[0] (a • v) := by rw [hΦs]; rfl
    have h4 : ∑ i ∈ Finset.range (orderOf σ), Φ ((⇑Φ)^[i] (a • v)) =
        ∑ i ∈ Finset.range (orderOf σ), (⇑Φ)^[i + 1] (a • v) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Function.iterate_succ_apply']
    rw [h4]
    rw [h1] at h2
    rw [h3] at h2
    exact add_right_cancel h2
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  by_contra hcon
  push Not at hcon
  have hu0 : ∀ a, u a = 0 := fun a => by
    by_contra hne
    exact hcon (u a) hne (hfix a)
  have hsum : ∀ a : F, ∑ i ∈ Finset.range (orderOf σ), ((⇑Φ)^[i] v j) * (σ ^ i) a = 0 := by
    intro a
    have := congrFun (hu0 a) j
    simp only [u, hiter, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have := eq_zero_of_sum_eq_zero σ (fun i => (⇑Φ)^[i] v j) hsum 0 hs0
  simp at this
  exact hj this

theorem exists_norm_mul_eq_one (σ : F ≃+* F) (hs : Odd (orderOf σ))
    (D l : F) (hl : l ≠ 0) (hσl : σ l = l)
    (hD : ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) D = l ^ 2) :
    ∃ c : F, c ≠ 0 ∧ (∏ i ∈ Finset.range (orderOf σ), (σ ^ i) c) * l = 1 := by
  obtain ⟨k, hk⟩ := hs
  have hfixl : ∀ i : ℕ, (σ ^ i) l = l := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', RingAut.mul_apply, ih, hσl]
  have hprod : (∏ i ∈ Finset.range (orderOf σ), (σ ^ i) (l⁻¹ * D ^ k)) * l = 1 := by
    have h1 : ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) (l⁻¹ * D ^ k) =
        (∏ i ∈ Finset.range (orderOf σ), (σ ^ i) l⁻¹) *
          (∏ i ∈ Finset.range (orderOf σ), (σ ^ i) D) ^ k := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_mul, map_pow]
    have h2 : ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) l⁻¹ = (l ^ orderOf σ)⁻¹ := by
      simp [map_inv₀, hfixl]
    rw [h1, h2, hD, hk]
    field_simp
    ring
  refine ⟨l⁻¹ * D ^ k, ?_, hprod⟩
  rintro hc
  rw [hc] at hprod
  have hs0 : 0 < orderOf σ := by omega
  have : ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) (0 : F) = 0 :=
    Finset.prod_eq_zero (i := 0) (Finset.mem_range.2 hs0) (by simp)
  rw [this] at hprod
  simp at hprod

@[expose] def Mseq (σ : F ≃+* F) (H : Matrix (Fin 2) (Fin 2) F) : ℕ → Matrix (Fin 2) (Fin 2) F
  | 0 => 1
  | k + 1 => H * (Mseq σ H k).map σ

theorem map_map_pow (σ : F ≃+* F) (M : Matrix (Fin 2) (Fin 2) F) (k : ℕ) :
    (M.map (σ ^ k)).map σ = M.map (σ ^ (k + 1)) := by
  ext i j
  simp [Matrix.map_apply, pow_succ']

theorem map_one_aut (M : Matrix (Fin 2) (Fin 2) F) : M.map (1 : F ≃+* F) = M := by
  ext i j
  simp [Matrix.map_apply]

theorem map_mul_aut (τ : F ≃+* F) (A B : Matrix (Fin 2) (Fin 2) F) :
    (A * B).map τ = A.map τ * B.map τ :=
  Matrix.map_mul (f := (τ : F →+* F))

theorem Mseq_succ' (σ : F ≃+* F) (H : Matrix (Fin 2) (Fin 2) F) (k : ℕ) :
    Mseq σ H (k + 1) = Mseq σ H k * H.map (σ ^ k) := by
  induction k with
  | zero => simp [Mseq]
  | succ k ih =>
    calc Mseq σ H (k + 1 + 1) = H * (Mseq σ H (k + 1)).map σ := rfl
      _ = H * ((Mseq σ H k * H.map (σ ^ k)).map σ) := by rw [ih]
      _ = H * ((Mseq σ H k).map σ * (H.map (σ ^ k)).map σ) := by rw [map_mul_aut]
      _ = (H * (Mseq σ H k).map σ) * H.map (σ ^ (k + 1)) := by rw [← mul_assoc, map_map_pow]
      _ = Mseq σ H (k + 1) * H.map (σ ^ (k + 1)) := rfl

theorem det_Mseq (σ : F ≃+* F) (H : Matrix (Fin 2) (Fin 2) F) (k : ℕ) :
    (Mseq σ H k).det = ∏ i ∈ Finset.range k, (σ ^ i) H.det := by
  induction k with
  | zero => simp [Mseq]
  | succ k ih =>
    have h1 : ((Mseq σ H k).map σ).det = σ (Mseq σ H k).det :=
      (RingHom.map_det (σ : F →+* F) _).symm
    rw [Mseq, Matrix.det_mul, h1, ih, Finset.prod_range_succ']
    have h2 : σ (∏ i ∈ Finset.range k, (σ ^ i) H.det) =
        ∏ i ∈ Finset.range k, (σ ^ (i + 1)) H.det := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [pow_succ', RingAut.mul_apply]
    rw [h2, mul_comm]
    simp

theorem Mseq_smul (σ : F ≃+* F) (H : Matrix (Fin 2) (Fin 2) F) (c : F) (k : ℕ) :
    Mseq σ (c • H) k = (∏ i ∈ Finset.range k, (σ ^ i) c) • Mseq σ H k := by
  induction k with
  | zero => simp [Mseq]
  | succ k ih =>
    have h2 : (Mseq σ (c • H) k).map σ =
        (∏ i ∈ Finset.range k, (σ ^ (i + 1)) c) • (Mseq σ H k).map σ := by
      rw [ih]
      ext i j
      simp [Matrix.map_apply, map_prod, pow_succ']
    rw [Mseq, h2, Finset.prod_range_succ', Mseq]
    simp [smul_smul, mul_comm]

@[expose] def twist (σ : F ≃+* F) (H : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) : Fin 2 → F :=
  H *ᵥ (fun j => σ (v j))

@[expose] def twistHom (σ : F ≃+* F) (H : Matrix (Fin 2) (Fin 2) F) : (Fin 2 → F) →+ (Fin 2 → F) where
  toFun := twist σ H
  map_zero' := by simp [twist]
  map_add' u v := by
    simp only [twist, Pi.add_apply, map_add]
    rw [← mulVec_add]
    rfl

theorem twistHom_apply (σ : F ≃+* F) (H : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    twistHom σ H v = H *ᵥ (fun j => σ (v j)) := rfl

theorem twistHom_smul (σ : F ≃+* F) (H : Matrix (Fin 2) (Fin 2) F) (a : F) (v : Fin 2 → F) :
    twistHom σ H (a • v) = σ a • twistHom σ H v := by
  rw [twistHom_apply, twistHom_apply, ← Matrix.mulVec_smul]
  congr 1
  ext j
  simp

theorem iterate_twist (σ : F ≃+* F) (H : Matrix (Fin 2) (Fin 2) F) (k : ℕ) (v : Fin 2 → F) :
    (⇑(twistHom σ H))^[k] v = Mseq σ H k *ᵥ (fun j => (σ ^ k) (v j)) := by
  induction k generalizing v with
  | zero => simp [Mseq]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, twistHom_apply]
    have : (fun j => σ ((Mseq σ H k *ᵥ fun j => (σ ^ k) (v j)) j)) =
        (Mseq σ H k).map σ *ᵥ (fun j => (σ ^ (k + 1)) (v j)) := by
      ext j
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pow_succ']
    rw [this, Matrix.mulVec_mulVec]
    rfl

theorem map_mulVec_aut (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    (fun j => σ ((A *ᵥ v) j)) = A.map σ *ᵥ (fun j => σ (v j)) := by
  ext j
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem twistHom_mulVec (σ : F ≃+* F) (H A : Matrix (Fin 2) (Fin 2) F)
    (hA : A * H = H * A.map σ) (v : Fin 2 → F) :
    twistHom σ H (A *ᵥ v) = A *ᵥ twistHom σ H v := by
  rw [twistHom_apply, twistHom_apply, map_mulVec_aut, Matrix.mulVec_mulVec, ← hA,
    ← Matrix.mulVec_mulVec]

theorem twistHom_fixed_iff (σ : F ≃+* F) (H : Matrix (Fin 2) (Fin 2) F) (x : Fin 2 → F)
    (hx : twistHom σ H x = x) (i : Fin 2) : H i 0 * σ (x 0) + H i 1 * σ (x 1) = x i := by
  have := congrFun hx i
  simpa [twistHom_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this

theorem Mseq_conj (σ : F ≃+* F) (G : Matrix (Fin 2) (Fin 2) F)
    (φ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F))
    (hφ : ∀ b : Matrix.SpecialLinearGroup (Fin 2) F,
      ((φ b : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * G =
        G * (b : Matrix (Fin 2) (Fin 2) F).map σ)
    (k : ℕ) (b : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((φ ^ k) b : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Mseq σ G k =
      Mseq σ G k * (b : Matrix (Fin 2) (Fin 2) F).map (σ ^ k) := by
  induction k generalizing b with
  | zero => simp [Mseq]
  | succ k ih =>
    have e1 : (φ ^ (k + 1)) b = φ ((φ ^ k) b) := by rw [pow_succ']; rfl
    have h1 := hφ ((φ ^ k) b)
    have h2 := ih b
    calc (((φ ^ (k + 1)) b : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Mseq σ G (k + 1)
        = (((φ ((φ ^ k) b) : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * G) *
            (Mseq σ G k).map σ := by rw [e1, Mseq, mul_assoc]
      _ = G * ((((φ ^ k) b : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            Mseq σ G k).map σ := by rw [h1, mul_assoc, map_mul_aut]
      _ = G * (Mseq σ G k * (b : Matrix (Fin 2) (Fin 2) F).map (σ ^ k)).map σ := by rw [h2]
      _ = Mseq σ G (k + 1) * (b : Matrix (Fin 2) (Fin 2) F).map (σ ^ (k + 1)) := by
        rw [map_mul_aut, map_map_pow, ← mul_assoc]
        rfl

theorem exists_basis_matrix (σ : F ≃+* F) (H A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F)
    (hAA : A * A = -1) (hv0 : v ≠ 0) (hv : twistHom σ H v = v)
    (hu : twistHom σ H (A *ᵥ v) = A *ᵥ v) (hneg : ¬ IsSquare (-1 : F)) :
    ∃ Pm : Matrix (Fin 2) (Fin 2) F, Pm.det ≠ 0 ∧ H * Pm.map σ = Pm ∧
      A * Pm = Pm * !![0, 1; -1, 0] := by
  set u : Fin 2 → F := A *ᵥ v with hu_def
  have hAu : A *ᵥ u = -v := by
    rw [hu_def, Matrix.mulVec_mulVec, hAA]
    ext i
    fin_cases i <;> simp
  have hv' := twistHom_fixed_iff σ H v hv
  have hu' := twistHom_fixed_iff σ H u hu
  have hA00 := congrFun (congrFun hAA 0) 0
  have hA01 := congrFun (congrFun hAA 0) 1
  have hA10 := congrFun (congrFun hAA 1) 0
  have hA11 := congrFun (congrFun hAA 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hA00 hA01 hA10 hA11
  refine ⟨!![v 0, -(u 0); v 1, -(u 1)], ?_, ?_, ?_⟩
  ·
    intro hdet
    rw [Matrix.det_fin_two_of] at hdet
    obtain ⟨t, ht⟩ : ∃ t : F, u = t • v := by
      by_cases h0 : v 0 = 0
      · have h1 : v 1 ≠ 0 := by
          intro h1
          apply hv0
          ext i
          fin_cases i <;> simp [h0, h1]
        have hu0 : u 0 = 0 := by
          have : v 0 * -u 1 - -u 0 * v 1 = 0 := hdet
          rw [h0] at this
          have : u 0 * v 1 = 0 := by linear_combination this
          exact (mul_eq_zero.1 this).resolve_right h1
        refine ⟨u 1 / v 1, ?_⟩
        ext i
        fin_cases i
        · simp [hu0, h0]
        · simp; field_simp
      · refine ⟨u 0 / v 0, ?_⟩
        ext i
        fin_cases i
        · simp; field_simp
        · simp
          field_simp
          linear_combination -hdet
    have hAv : A *ᵥ v = t • v := ht
    have h1 : A *ᵥ u = (t * t) • v := by
      rw [ht, Matrix.mulVec_smul, hAv, smul_smul]
    rw [hAu] at h1
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
    have h2 := congrFun h1 j
    simp at h2
    have h3 : (t * t + 1) * v j = 0 := by linear_combination -h2
    have h4 : t * t = -1 := by
      have := (mul_eq_zero.1 h3).resolve_right hj
      linear_combination this
    exact hneg ⟨t, h4.symm⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hv' 0, hv' 1]
    · linear_combination -(hu' 0)
    · linear_combination -(hu' 1)
  · have e0 := congrFun hAu 0
    have e1 := congrFun hAu 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu_def]
    · linear_combination (-(v 0)) * hA00 - (v 1) * hA01
    · linear_combination (-(v 0)) * hA10 - (v 1) * hA11

end CFSG.GH74.GLS.SP.Local.SL2Three
