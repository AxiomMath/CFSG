module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
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

namespace CFSG

namespace FrobeniusKernel.Helpers

open scoped BigOperators

noncomputable section

private def multiplicativeAdditiveMulEquiv (G : Type*) [Group G] :
    Multiplicative (Additive G) ≃* G where
  toFun x := Additive.toMul (Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (Additive.ofMul x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem groupAlgebra_isSemisimpleRing (G : Type*) [Group G] [Fintype G] :
    IsSemisimpleRing (MonoidAlgebra ℂ G) := by
  let e : AddMonoidAlgebra ℂ (Additive G) ≃ₐ[ℂ] MonoidAlgebra ℂ G :=
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (Additive G)).trans
      (MonoidAlgebra.domCongr ℂ ℂ (multiplicativeAdditiveMulEquiv G))
  let : IsSemisimpleRing (AddMonoidAlgebra ℂ (Additive G)) := inferInstance
  exact e.toRingEquiv.isSemisimpleRing

private theorem groupAlgebra_exists_wedderburn (G : Type*) [Group G] [Fintype G] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i : Fin n, NeZero (d i)) ∧
      Nonempty (MonoidAlgebra ℂ G ≃ₐ[ℂ]
        ((i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) := by
  let : IsSemisimpleRing (MonoidAlgebra ℂ G) := groupAlgebra_isSemisimpleRing G
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ
    (MonoidAlgebra ℂ G)

structure CentralIdempotentBasis (R : Type*) [Ring R] [Algebra ℂ R] where
  n : ℕ
  elem : Fin n → R
  central : ∀ i, elem i ∈ Set.center R
  mul_elem : ∀ i j, elem i * elem j = if i = j then elem i else 0
  sum_elem : ∑ i, elem i = 1
  span_center : ∀ z ∈ Set.center R, ∃ c : Fin n → ℂ, z = ∑ i, c i • elem i
  elem_ne_zero : ∀ i, elem i ≠ 0

theorem groupAlgebra_centralIdempotentBasis
    (G : Type*) [Group G] [Fintype G] :
    Nonempty (CentralIdempotentBasis (MonoidAlgebra ℂ G)) := by
  classical
  obtain ⟨n, d, hd, ⟨E⟩⟩ := groupAlgebra_exists_wedderburn G
  let B := (i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) ℂ
  let p : Fin n → B := fun i => Pi.single i 1
  let e : Fin n → MonoidAlgebra ℂ G := fun i => E.symm (p i)
  have hp_center (i : Fin n) : p i ∈ Set.center B := by
    rw [Set.center_pi]
    intro j _
    by_cases hji : j = i
    · subst j
      change p i i ∈ Set.center (Matrix (Fin (d i)) (Fin (d i)) ℂ)
      rw [Matrix.center_eq_range ℂ]
      exact ⟨1, by simp [p, Matrix.scalar_apply]⟩
    · change p i j ∈ Set.center (Matrix (Fin (d j)) (Fin (d j)) ℂ)
      rw [Matrix.center_eq_range ℂ]
      exact ⟨0, by simp [p, hji]⟩
  have he_center (i : Fin n) : e i ∈ Set.center (MonoidAlgebra ℂ G) := by
    exact MulEquivClass.apply_mem_center E.symm.toMulEquiv (hp_center i)
  have he_mul (i j : Fin n) : e i * e j = if i = j then e i else 0 := by
    apply E.injective
    by_cases hij : i = j
    · subst j
      ext k a b
      by_cases hki : k = i
      · subst k
        simp [e, p]
      · simp [e, p, hki]
    · ext k a b
      by_cases hki : k = i
      · subst k
        simp [e, p, hij]
      · by_cases hkj : k = j
        · subst k
          simp [e, p, hij, hki]
        · simp [e, p, hij, hki, hkj]
  have he_sum : ∑ i, e i = 1 := by
    apply E.injective
    ext k a b
    simp [e, p]
  have he_ne (i : Fin n) : e i ≠ 0 := by
    intro hi
    have hpi : p i = 0 := by
      simpa [e] using congrArg E hi
    have hcoord : p i i = 0 := by
      rw [hpi]
      rfl
    have := hd i
    exact (one_ne_zero : (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ) ≠ 0)
      (by simpa [p] using hcoord)
  have he_span (z : MonoidAlgebra ℂ G)
      (hz : z ∈ Set.center (MonoidAlgebra ℂ G)) :
      ∃ c : Fin n → ℂ, z = ∑ i, c i • e i := by
    have hzB : E z ∈ Set.center B :=
      MulEquivClass.apply_mem_center E.toMulEquiv hz
    have hzcoord (i : Fin n) : E z i ∈ Set.center (Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
      rw [Set.center_pi] at hzB
      exact hzB i (Set.mem_univ i)
    have hc (i : Fin n) : ∃ c : ℂ, Matrix.scalar (Fin (d i)) c = E z i := by
      have hi := hzcoord i
      rw [Matrix.center_eq_range ℂ] at hi
      simpa only [Set.mem_range] using hi
    let c : Fin n → ℂ := fun i => (hc i).choose
    refine ⟨c, ?_⟩
    apply E.injective
    simp only [map_sum, map_smul, e, E.apply_symm_apply]
    symm
    funext k
    rw [← (hc k).choose_spec]
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · have hpone : p k k = 1 := by simp [p]
      rw [Pi.smul_apply, hpone, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
    · intro i _ hik
      have hki : k ≠ i := fun h => hik h.symm
      have hpzero : p i k = 0 := by simp [p, hki]
      rw [Pi.smul_apply, hpzero, smul_zero]
    · simp
  exact ⟨{
    n := n
    elem := e
    central := he_center
    mul_elem := he_mul
    sum_elem := he_sum
    span_center := he_span
    elem_ne_zero := he_ne
  }⟩

def groupAlgebraAdjoint {G : Type*} [Group G] [Fintype G]
    (x : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  { coeff := Finsupp.equivFunOnFinite.symm fun g => star (x.coeff g⁻¹) }

@[simp] theorem groupAlgebraAdjoint_coeff {G : Type*} [Group G] [Fintype G]
    (x : MonoidAlgebra ℂ G) (g : G) :
    (groupAlgebraAdjoint x).coeff g = star (x.coeff g⁻¹) := by
  simp [groupAlgebraAdjoint]

theorem groupAlgebra_coeff_mul_eq_sum {G : Type*} [Group G] [Fintype G]
    (x y : MonoidAlgebra ℂ G) (g : G) :
    (x * y).coeff g = ∑ h : G, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro
  simp

@[simp] theorem groupAlgebraAdjoint_adjoint {G : Type*} [Group G] [Fintype G]
    (x : MonoidAlgebra ℂ G) :
    groupAlgebraAdjoint (groupAlgebraAdjoint x) = x := by
  ext g
  simp

private theorem groupAlgebraAdjoint_mul {G : Type*} [Group G] [Fintype G]
    (x y : MonoidAlgebra ℂ G) :
    groupAlgebraAdjoint (x * y) =
      groupAlgebraAdjoint y * groupAlgebraAdjoint x := by
  ext g
  rw [groupAlgebraAdjoint_coeff, groupAlgebra_coeff_mul_eq_sum,
    star_sum Finset.univ, groupAlgebra_coeff_mul_eq_sum]
  simp only [groupAlgebraAdjoint_coeff, mul_inv_rev, inv_inv]
  let F : G → ℂ := fun k =>
    star (y.coeff k⁻¹) * star (x.coeff (g⁻¹ * k))
  simpa [F, mul_assoc, mul_comm] using Equiv.sum_comp (Equiv.mulLeft g) F

private theorem groupAlgebraAdjoint_mem_center {G : Type*} [Group G] [Fintype G]
    {x : MonoidAlgebra ℂ G} (hx : x ∈ Set.center (MonoidAlgebra ℂ G)) :
    groupAlgebraAdjoint x ∈ Set.center (MonoidAlgebra ℂ G) := by
  rw [Set.mem_center_iff] at hx ⊢
  rw [isMulCentral_iff]
  refine ⟨?_, by simp [mul_assoc], by simp [mul_assoc]⟩
  intro y
  have h := congrArg groupAlgebraAdjoint
    ((hx.comm (groupAlgebraAdjoint y)).eq)
  simp only [groupAlgebraAdjoint_mul, groupAlgebraAdjoint_adjoint] at h
  exact h.symm

theorem central_coeff_conj {G : Type*} [Group G] [Fintype G]
    {e : MonoidAlgebra ℂ G} (he : e ∈ Set.center (MonoidAlgebra ℂ G))
    (a g : G) : e.coeff (a * g * a⁻¹) = e.coeff g := by
  have h := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff (a * g))
    (((Set.mem_center_iff.mp he).comm (MonoidAlgebra.single a 1)).eq)
  simpa [MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply, mul_assoc] using h

theorem mem_center_of_coeff_conj {G : Type*} [Group G] [Fintype G]
    {e : MonoidAlgebra ℂ G}
    (he : ∀ a g : G, e.coeff (a * g * a⁻¹) = e.coeff g) :
    e ∈ Set.center (MonoidAlgebra ℂ G) := by
  classical
  rw [Set.mem_center_iff, isMulCentral_iff]
  refine ⟨?_, by simp [mul_assoc], by simp [mul_assoc]⟩
  intro z
  change e * z = z * e
  have hsingle (a : G) :
      e * MonoidAlgebra.single a 1 = MonoidAlgebra.single a 1 * e := by
    ext g
    rw [MonoidAlgebra.coeff_mul_single_apply,
      MonoidAlgebra.coeff_single_mul_apply]
    simpa [mul_assoc] using he a (a⁻¹ * g)
  have hz : z = ∑ a : G, z.coeff a • MonoidAlgebra.single a 1 := by
    ext g
    simp
  rw [hz, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_smul_comm, smul_mul_assoc, hsingle]

@[expose] def groupAlgebraAugmentation (G : Type*) [Group G] :
    MonoidAlgebra ℂ G →ₐ[ℂ] ℂ :=
  (MonoidAlgebra.lift ℂ ℂ G) 1

@[simp] theorem groupAlgebraAugmentation_apply
    {G : Type*} [Group G] [Fintype G] (e : MonoidAlgebra ℂ G) :
    groupAlgebraAugmentation G e = ∑ g : G, e.coeff g := by
  simp [groupAlgebraAugmentation, MonoidAlgebra.lift_apply,
    Finsupp.sum_fintype]

def uniformCentralElement (G : Type*) [Group G] [Fintype G] :
    MonoidAlgebra ℂ G :=
  (Fintype.card G : ℂ)⁻¹ •
    ∑ g : G, MonoidAlgebra.single g 1

@[simp] theorem uniformCentralElement_coeff
    {G : Type*} [Group G] [Fintype G] (g : G) :
    (uniformCentralElement G).coeff g = (Fintype.card G : ℂ)⁻¹ := by
  classical
  simp [uniformCentralElement]

theorem sum_coeff_uniformCentralElement
    {G : Type*} [Group G] [Fintype G] :
    ∑ g : G, (uniformCentralElement G).coeff g = 1 := by
  classical
  simp [uniformCentralElement_coeff, nsmul_eq_mul]

private theorem mul_uniformCentralElement
    {G : Type*} [Group G] [Fintype G]
    (e : MonoidAlgebra ℂ G) :
    e * uniformCentralElement G =
      (∑ g : G, e.coeff g) • uniformCentralElement G := by
  classical
  ext k
  rw [groupAlgebra_coeff_mul_eq_sum]
  simp only [uniformCentralElement_coeff]
  rw [← Finset.sum_mul]
  simp [uniformCentralElement_coeff]

private theorem uniformCentralElement_mul
    {G : Type*} [Group G] [Fintype G]
    (e : MonoidAlgebra ℂ G) :
    uniformCentralElement G * e =
      (∑ g : G, e.coeff g) • uniformCentralElement G := by
  classical
  ext k
  rw [groupAlgebra_coeff_mul_eq_sum]
  simp only [uniformCentralElement_coeff]
  let q : G ≃ G := Equiv.mulRight k
  let F : G → ℂ := fun g => e.coeff g
  have hs := Equiv.sum_comp q F
  have hsum : ∑ g : G, e.coeff (g⁻¹ * k) = ∑ g : G, e.coeff g := by
    let r : G ≃ G := (Equiv.inv G).trans q
    have hr := Equiv.sum_comp r F
    simpa [r, q, F] using hr
  rw [← Finset.mul_sum, hsum]
  simp [uniformCentralElement_coeff]
  ring

private theorem uniformCentralElement_mem_center
    {G : Type*} [Group G] [Fintype G] :
    uniformCentralElement G ∈ Set.center (MonoidAlgebra ℂ G) := by
  rw [Set.mem_center_iff, isMulCentral_iff]
  refine ⟨?_, by simp [mul_assoc], by simp [mul_assoc]⟩
  intro e
  change uniformCentralElement G * e = e * uniformCentralElement G
  rw [uniformCentralElement_mul, mul_uniformCentralElement]

theorem CentralIdempotentBasis.elem_eq_uniform_of_sum_coeff_ne_zero
    {G : Type*} [Group G] [Fintype G]
    (b : CentralIdempotentBasis (MonoidAlgebra ℂ G)) (i : Fin b.n)
    (hmean : (∑ g : G, (b.elem i).coeff g) ≠ 0) :
    b.elem i = uniformCentralElement G := by
  classical
  let e := b.elem i
  let m : ℂ := ∑ g : G, e.coeff g
  have hei : e * e = e := by simpa [e] using b.mul_elem i i
  have hm_idem : m * m = m := by
    have h := congrArg (groupAlgebraAugmentation G) hei
    rw [map_mul] at h
    simpa only [groupAlgebraAugmentation_apply, m, e] using h
  have hm_ne : m ≠ 0 := by simpa [m, e] using hmean
  have hm_one : m = 1 := by
    have hz : m * (m - 1) = 0 := by rw [mul_sub, hm_idem, mul_one, sub_self]
    rcases mul_eq_zero.mp hz with hz | hz
    · exact (hm_ne hz).elim
    · exact sub_eq_zero.mp hz
  let u := uniformCentralElement G
  have heu : e * u = u := by
    rw [mul_uniformCentralElement]
    simp [m, e, u, hm_one]
  obtain ⟨c, hc⟩ := b.span_center u uniformCentralElement_mem_center
  have heusform : e * u = c i • e := by
    rw [hc, Finset.mul_sum]
    simp [e, b.mul_elem]
  have huform : u = c i • e := heu.symm.trans heusform
  have hc_one : c i = 1 := by
    have h := congrArg (groupAlgebraAugmentation G) huform
    rw [map_smul] at h
    have huaug : groupAlgebraAugmentation G u = 1 := by
      simpa [u] using (sum_coeff_uniformCentralElement (G := G))
    have heaug : groupAlgebraAugmentation G e = 1 := by
      rw [groupAlgebraAugmentation_apply]
      simp [m, hm_one]
    rw [huaug, heaug, smul_eq_mul, mul_one] at h
    exact h.symm
  have : u = e := by simpa [hc_one] using huform
  exact this.symm

theorem CentralIdempotentBasis.adjoint_elem
    {G : Type*} [Group G] [Fintype G]
    (b : CentralIdempotentBasis (MonoidAlgebra ℂ G)) (i : Fin b.n) :
    groupAlgebraAdjoint (b.elem i) = b.elem i := by
  classical
  let e := b.elem i
  let f := groupAlgebraAdjoint e
  have he_center : e ∈ Set.center (MonoidAlgebra ℂ G) := b.central i
  have hf_center : f ∈ Set.center (MonoidAlgebra ℂ G) :=
    groupAlgebraAdjoint_mem_center he_center
  have he_idem : e * e = e := by simpa [e] using b.mul_elem i i
  have hf_idem : f * f = f := by
    have h := congrArg groupAlgebraAdjoint he_idem
    simpa [e, f, groupAlgebraAdjoint_mul] using h
  obtain ⟨c, hc⟩ := b.span_center f hf_center
  have hqform : e * f = c i • e := by
    rw [hc, Finset.mul_sum]
    simp [e, b.mul_elem]
  have hef_comm : e * f = f * e :=
    ((Set.mem_center_iff.mp he_center).comm f).eq
  have hq_idem : (e * f) * (e * f) = e * f := by
    calc
      (e * f) * (e * f) = e * (f * e) * f := by simp [mul_assoc]
      _ = e * (e * f) * f := by rw [hef_comm]
      _ = (e * e) * (f * f) := by simp [mul_assoc]
      _ = e * f := by rw [he_idem, hf_idem]
  have he_coeff : ∃ g : G, e.coeff g ≠ 0 := by
    by_contra h
    push Not at h
    apply b.elem_ne_zero i
    ext g
    exact h g
  have hnorm_pos : 0 < ∑ g : G, Complex.normSq (e.coeff g) := by
    apply Finset.sum_pos'
    · intro g _
      exact Complex.normSq_nonneg _
    · obtain ⟨g, hg⟩ := he_coeff
      exact ⟨g, Finset.mem_univ g, Complex.normSq_pos.mpr hg⟩
  have hq_coeff : (e * f).coeff 1 =
      ((∑ g : G, Complex.normSq (e.coeff g) : ℝ) : ℂ) := by
    rw [groupAlgebra_coeff_mul_eq_sum]
    simp only [f, groupAlgebraAdjoint_coeff, mul_inv_rev, inv_one, one_mul,
      inv_inv]
    calc
      ∑ g : G, e.coeff g * star (e.coeff g) =
          ∑ g : G, (Complex.normSq (e.coeff g) : ℂ) := by
            apply Finset.sum_congr rfl
            intro g _
            exact Complex.mul_conj _
      _ = ((∑ g : G, Complex.normSq (e.coeff g) : ℝ) : ℂ) :=
        (map_sum Complex.ofRealHom (fun g : G => Complex.normSq (e.coeff g))
          Finset.univ).symm
  have hq_ne : e * f ≠ 0 := by
    intro hq
    have hz : (e * f).coeff 1 = 0 := by rw [hq]; simp
    rw [hq_coeff] at hz
    exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hnorm_pos)) hz
  have hci_ne : c i ≠ 0 := by
    intro hci
    apply hq_ne
    rw [hqform, hci, zero_smul]
  obtain ⟨g, hg⟩ := he_coeff
  have hci_mul : c i * c i = c i := by
    have hq_idem' := hq_idem
    rw [hqform] at hq_idem'
    have h := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff g) hq_idem'
    simp only [smul_mul_smul_comm, he_idem, 
      ] at h
    exact mul_right_cancel₀ hg h
  have hci_one : c i = 1 := by
    have hz : c i * (c i - 1) = 0 := by rw [mul_sub, hci_mul, mul_one, sub_self]
    rcases mul_eq_zero.mp hz with hz | hz
    · exact (hci_ne hz).elim
    · exact sub_eq_zero.mp hz
  have hq_eq : e * f = e := by simp [hqform, hci_one]
  have h := congrArg groupAlgebraAdjoint hq_eq
  have hef : e * f = f := by
    simpa [f, groupAlgebraAdjoint_mul] using h
  rw [hq_eq] at hef
  change f = e
  exact hef.symm

theorem CentralIdempotentBasis.coeff_one_eq_pos_real
    {G : Type*} [Group G] [Fintype G]
    (b : CentralIdempotentBasis (MonoidAlgebra ℂ G)) (i : Fin b.n) :
    ∃ r : ℝ, 0 < r ∧ (b.elem i).coeff 1 = (r : ℂ) := by
  classical
  let e := b.elem i
  have he_coeff : ∃ g : G, e.coeff g ≠ 0 := by
    by_contra h
    push Not at h
    apply b.elem_ne_zero i
    ext g
    exact h g
  let r : ℝ := ∑ g : G, Complex.normSq (e.coeff g)
  have hr : 0 < r := by
    apply Finset.sum_pos'
    · intro g _
      exact Complex.normSq_nonneg _
    · obtain ⟨g, hg⟩ := he_coeff
      exact ⟨g, Finset.mem_univ g, Complex.normSq_pos.mpr hg⟩
  refine ⟨r, hr, ?_⟩
  have hei : e * e = e := by simpa [e] using b.mul_elem i i
  have hcoeff := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff 1) hei
  rw [groupAlgebra_coeff_mul_eq_sum] at hcoeff
  have hstar (g : G) : e.coeff g⁻¹ = star (e.coeff g) := by
    have h := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff g⁻¹)
      (b.adjoint_elem i)
    simpa [e] using h.symm
  simp only [mul_one, hstar] at hcoeff
  calc
    e.coeff 1 = ∑ g : G, e.coeff g * star (e.coeff g) := hcoeff.symm
    _ = ∑ g : G, (Complex.normSq (e.coeff g) : ℂ) := by
      apply Finset.sum_congr rfl
      intro g _
      exact Complex.mul_conj _
    _ = (r : ℂ) := by
      simp [r]

private def groupAlgebraBimoduleMap {G : Type*} [Group G]
    (s : G × G) : MonoidAlgebra ℂ G →ₗ[ℂ] MonoidAlgebra ℂ G where
  toFun z := MonoidAlgebra.single s.1 1 * z * MonoidAlgebra.single s.2⁻¹ 1
  map_add' x y := by simp [mul_add, add_mul]
  map_smul' r x := by simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

private def groupAlgebraBimoduleRepresentation (G : Type*) [Group G] :
    Representation ℂ (G × G) (MonoidAlgebra ℂ G) where
  toFun := groupAlgebraBimoduleMap
  map_one' := by
    ext z g
    simp [groupAlgebraBimoduleMap]
  map_mul' s t := by
    ext z g
    simp [groupAlgebraBimoduleMap, mul_assoc]

private theorem groupAlgebra_basis_repr {G : Type*} [Group G]
    (z : MonoidAlgebra ℂ G) (g : G) :
    (MonoidAlgebra.basis G ℂ).repr z g = z.coeff g := by
  rfl

private theorem trace_lmul_bimodule {G : Type*} [Group G] [Fintype G]
    (e : MonoidAlgebra ℂ G) (s : G × G) :
    (LinearMap.trace ℂ (MonoidAlgebra ℂ G))
        ((LinearMap.mulLeft ℂ e) * groupAlgebraBimoduleMap s) =
      ∑ x : G, e.coeff (x * s.2 * x⁻¹ * s.1⁻¹) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ)]
  apply Finset.sum_congr rfl
  intro x _
  change ((LinearMap.toMatrix (MonoidAlgebra.basis G ℂ) (MonoidAlgebra.basis G ℂ))
      ((LinearMap.mulLeft ℂ e) * groupAlgebraBimoduleMap s)) x x = _
  rw [LinearMap.toMatrix_apply, groupAlgebra_basis_repr]
  simp [groupAlgebraBimoduleMap, Module.End.mul_apply,
    LinearMap.mulLeft, MonoidAlgebra.basis_apply, mul_assoc]

private theorem trace_average_centralIdempotent_eq_nat
    {G L : Type*} [Group G] [Fintype G] [Group L] [Fintype L]
    (f : L →* G × G) (e : MonoidAlgebra ℂ G)
    (hec : e ∈ Set.center (MonoidAlgebra ℂ G))
    (hei : e * e = e) :
    ∃ n : ℕ, ⅟(Fintype.card L : ℂ) *
      ∑ s : L, ∑ x : G,
        e.coeff (x * (f s).2 * x⁻¹ * (f s).1⁻¹) = n := by
  classical
  let ρ : Representation ℂ L (MonoidAlgebra ℂ G) :=
    (groupAlgebraBimoduleRepresentation G).comp f
  let P : Module.End ℂ (MonoidAlgebra ℂ G) := LinearMap.mulLeft ℂ e
  let Q : Module.End ℂ (MonoidAlgebra ℂ G) := ρ.averageMap
  have hP : IsIdempotentElem P := by
    apply LinearMap.ext
    intro z
    change e * (e * z) = e * z
    rw [← mul_assoc, hei]
  have hQ : IsIdempotentElem Q :=
    (Representation.isProj_averageMap ρ).isIdempotentElem
  have hcomm_s (s : L) : P * ρ s = ρ s * P := by
    apply LinearMap.ext
    intro z
    change e * (MonoidAlgebra.single (f s).1 1 * z *
          MonoidAlgebra.single (f s).2⁻¹ 1) =
      MonoidAlgebra.single (f s).1 1 * (e * z) *
          MonoidAlgebra.single (f s).2⁻¹ 1
    calc
      e * (MonoidAlgebra.single (f s).1 1 * z *
          MonoidAlgebra.single (f s).2⁻¹ 1) =
          (e * MonoidAlgebra.single (f s).1 1) * z *
            MonoidAlgebra.single (f s).2⁻¹ 1 := by simp [mul_assoc]
      _ = (MonoidAlgebra.single (f s).1 1 * e) * z *
            MonoidAlgebra.single (f s).2⁻¹ 1 := by
          rw [((Set.mem_center_iff.mp hec).comm _).eq]
      _ = MonoidAlgebra.single (f s).1 1 * (e * z) *
            MonoidAlgebra.single (f s).2⁻¹ 1 := by simp [mul_assoc]
  have hcomm : P * Q = Q * P := by
    simp only [Q, Representation.averageMap, GroupAlgebra.average, map_smul,
      map_sum]
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one, hcomm_s]
  have hPQ : IsIdempotentElem (P * Q) := by
    calc
      (P * Q) * (P * Q) = P * (Q * P) * Q := by simp [mul_assoc]
      _ = P * (P * Q) * Q := by rw [← hcomm]
      _ = (P * P) * (Q * Q) := by simp [mul_assoc]
      _ = P * Q := by rw [hP, hQ]
  let proj := LinearMap.IsIdempotentElem.isProj_range (P * Q) hPQ
  have hn : ∃ n : ℕ,
      (LinearMap.trace ℂ (MonoidAlgebra ℂ G)) (P * Q) = n :=
    ⟨Module.finrank ℂ ↥(P * Q).range, proj.trace⟩
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  rw [← hn]
  change _ = (LinearMap.trace ℂ (MonoidAlgebra ℂ G))
    ((LinearMap.mulLeft ℂ e) * ρ.averageMap)
  simp only [ρ, Representation.averageMap, GroupAlgebra.average, map_smul,
    map_sum]
  rw [mul_smul_comm, map_smul]
  change ⅟(Fintype.card L : ℂ) * _ = ⅟(Fintype.card L : ℂ) * _
  apply congrArg (⅟(Fintype.card L : ℂ) * ·)
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one]
  exact (trace_lmul_bimodule e (f s)).symm

theorem trace_average_centralIdempotent_eq_nat_of_adjoint
    {G L : Type*} [Group G] [Fintype G] [Group L] [Fintype L]
    (f : L →* G × G) (e : MonoidAlgebra ℂ G)
    (hec : e ∈ Set.center (MonoidAlgebra ℂ G))
    (hei : e * e = e) (hestar : groupAlgebraAdjoint e = e) :
    ∃ n : ℕ, ⅟(Fintype.card L : ℂ) *
      ∑ s : L, ∑ x : G,
        e.coeff ((f s).1 * x * (f s).2⁻¹ * x⁻¹) = n := by
  classical
  obtain ⟨n, hn⟩ := trace_average_centralIdempotent_eq_nat f e hec hei
  refine ⟨n, ?_⟩
  have hstar (u : G) : star (e.coeff u) = e.coeff u⁻¹ := by
    have h := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff u⁻¹) hestar
    simpa using h
  have h := congrArg (starRingEnd ℂ) hn
  simp only [map_mul, map_sum, starRingEnd_apply, hstar, map_natCast] at h
  simpa only [invOf_eq_inv, map_inv₀, star_inv₀, map_natCast, star_natCast,
    mul_inv_rev, inv_inv, mul_assoc] using h

end

end FrobeniusKernel.Helpers

end CFSG
