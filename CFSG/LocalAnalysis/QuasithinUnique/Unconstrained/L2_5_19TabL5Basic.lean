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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.L5

open Matrix
open scoped commutatorElement

abbrev M5 := Matrix (Fin 5) (Fin 5) (ZMod 2)

abbrev S := Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

@[expose] def circ (c : Fin 5 → ZMod 2) : M5 := Matrix.of fun i j => c (j - i)

@[expose] def Pm : M5 := circ (Pi.single 1 1)

theorem mul_Pm_apply (M : M5) (i j : Fin 5) : (M * Pm) i (j + 1) = M i j := by
  simp only [Matrix.mul_apply, Pm, circ, Matrix.of_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    have key : ∀ j k : Fin 5, j + 1 - k = 1 → k = j := by decide
    have : (j + 1 - k) ≠ 1 := fun h => hk (key j k h)
    simp [this]
  · simp

theorem Pm_mul_apply (M : M5) (i j : Fin 5) : (Pm * M) i j = M (i + 1) j := by
  simp only [Matrix.mul_apply, Pm, circ, Matrix.of_apply]
  rw [Finset.sum_eq_single (i + 1)]
  · simp
  · intro k _ hk
    have key : ∀ i k : Fin 5, k - i = 1 → k = i + 1 := by decide
    have : (k - i) ≠ 1 := fun h => hk (key i k h)
    simp [this]
  · simp

theorem circ_of_comm (M : M5) (h : M * Pm = Pm * M) : M = circ (fun d => M 0 d) := by
  have h1 : ∀ i j, M i j = M (i + 1) (j + 1) := by
    intro i j
    have := congrFun (congrFun h i) (j + 1)
    rw [mul_Pm_apply, Pm_mul_apply] at this
    exact this
  have e1 : ∀ j : Fin 5, j - 1 + 1 = j := by decide
  have step : ∀ i j, M (i + 1) j = M i (j - 1) := by
    intro i j
    have := h1 i (j - 1)
    rw [e1] at this
    exact this.symm
  have e2 : ∀ j : Fin 5, j - 1 - 1 = j - 2 := by decide
  have e3 : ∀ j : Fin 5, j - 1 - 1 - 1 = j - 3 := by decide
  have e4 : ∀ j : Fin 5, j - 1 - 1 - 1 - 1 = j - 4 := by decide
  ext i j
  simp only [circ, Matrix.of_apply]
  fin_cases i
  · simp
  · exact step 0 j
  · exact (step 1 j).trans ((step 0 (j - 1)).trans (congrArg (M 0) (e2 j)))
  · exact (step 2 j).trans ((step 1 (j - 1)).trans ((step 0 (j - 1 - 1)).trans
      (congrArg (M 0) (e3 j))))
  · exact (step 3 j).trans ((step 2 (j - 1)).trans ((step 1 (j - 1 - 1)).trans
      ((step 0 (j - 1 - 1 - 1)).trans (congrArg (M 0) (e4 j)))))

theorem circ_invol : ∀ c : Fin 5 → ZMod 2, circ c * circ c = 1 → circ c = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem symm_circ : ∀ c : Fin 5 → ZMod 2, (circ c)ᵀ = circ c → (circ c).det = 1 →
    c = ![1, 0, 0, 0, 0] ∨ c = ![1, 1, 0, 0, 1] ∨ c = ![1, 0, 1, 1, 0] := by
  decide

@[expose] def bm : M5 :=
  !![0, 1, 1, 1, 0; 1, 1, 1, 0, 0; 1, 1, 0, 1, 0; 1, 0, 1, 1, 0; 0, 0, 0, 0, 1]

theorem Pm_orth : Pm * Pmᵀ = 1 := by decide

theorem bm_orth : bm * bmᵀ = 1 := by decide

theorem bm_sq : bm * bm = 1 := by decide

set_option maxRecDepth 100000 in
@[expose] def Ps : S := ⟨Pm, by decide⟩

set_option maxRecDepth 100000 in
@[expose] def bs : S := ⟨bm, by decide⟩

@[expose] def Om : Subgroup S := Subgroup.closure {Ps, bs}

theorem Ps_mem : Ps ∈ Om := Subgroup.subset_closure (by simp)

theorem bs_mem : bs ∈ Om := Subgroup.subset_closure (by simp)

theorem comm_of_mul_eq {G : Type*} [Group G] {x y p : G} (h : x * y = p * y * x) :
    ⁅x, y⁆ = p := by
  rw [commutatorElement_def]
  calc x * y * x⁻¹ * y⁻¹ = (p * y * x) * x⁻¹ * y⁻¹ := by rw [h]
    _ = p := by group

set_option maxRecDepth 100000 in
theorem Ps_comm : ⁅bs * Ps * Ps * Ps, Ps * Ps * Ps * bs * Ps * bs⁆ = Ps :=
  comm_of_mul_eq (by decide)

set_option maxRecDepth 100000 in
theorem bs_comm : ⁅Ps * bs * Ps * Ps * Ps, bs * Ps * Ps * Ps * bs * Ps⁆ = bs :=
  comm_of_mul_eq (by decide)

theorem x1_mem : (bs * Ps * Ps * Ps) ∈ Om := by
  refine mul_mem (mul_mem (mul_mem bs_mem Ps_mem) Ps_mem) Ps_mem

theorem y1_mem : (Ps * Ps * Ps * bs * Ps * bs) ∈ Om := by
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem Ps_mem Ps_mem) Ps_mem) bs_mem) Ps_mem) bs_mem

theorem Ps_mem_comm : Ps ∈ ⁅Om, Om⁆ := by
  have := Subgroup.commutator_mem_commutator x1_mem y1_mem
  rwa [Ps_comm] at this

theorem x2_mem : (Ps * bs * Ps * Ps * Ps) ∈ Om := by
  refine mul_mem (mul_mem (mul_mem (mul_mem Ps_mem bs_mem) Ps_mem) Ps_mem) Ps_mem

theorem y2_mem : (bs * Ps * Ps * Ps * bs * Ps) ∈ Om := by
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem bs_mem Ps_mem) Ps_mem) Ps_mem) bs_mem) Ps_mem

theorem bs_mem_comm : bs ∈ ⁅Om, Om⁆ := by
  have := Subgroup.commutator_mem_commutator x2_mem y2_mem
  rwa [bs_comm] at this

theorem Om_perfect : ⁅Om, Om⁆ = Om := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact Om.mul_mem (Om.mul_mem (Om.mul_mem hx hy) (Om.inv_mem hx)) (Om.inv_mem hy)
  · refine (Subgroup.closure_le _).2 ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Ps_mem_comm
    · exact bs_mem_comm

set_option maxRecDepth 100000 in
theorem cent_circ : ∀ c : Fin 5 → ZMod 2, circ c * bm = bm * circ c → (circ c).det = 1 →
    circ c = 1 := by
  decide

theorem cent_Om (M : S) (hP : M * Ps = Ps * M) (hb : M * bs = bs * M) : M = 1 := by
  have h1 : (M : M5) * Pm = Pm * (M : M5) := congrArg Subtype.val hP
  have h2 : (M : M5) * bm = bm * (M : M5) := congrArg Subtype.val hb
  have h3 := circ_of_comm M h1
  rw [h3] at h2
  have h4 : (circ (fun d => (M : M5) 0 d)).det = 1 := by rw [← h3]; exact M.2
  have h5 := cent_circ _ h2 h4
  apply Subtype.ext
  rw [h3, h5]
  rfl

theorem center_S : Subgroup.center S = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun A hA => ?_
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hA⟩ := hA
  have hr0 : ∀ r : ZMod 2, r ^ Fintype.card (Fin 5) = 1 → r = 1 := by decide
  have hr1 : r = 1 := hr0 r hr
  subst hr1
  apply Subtype.ext
  rw [← hA]
  simp

theorem card_S : Nat.card S = 9999360 := by
  have := Matrix.card_SL_field (𝔽 := ZMod 2) 5
  rw [this]
  simp [Fin.prod_univ_five, ZMod.card]

theorem Ps_pow : Ps ^ 5 = 1 := by
  set_option maxRecDepth 100000 in decide

theorem orderOf_Ps : orderOf Ps = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine orderOf_eq_prime Ps_pow ?_
  set_option maxRecDepth 100000 in decide

theorem sylow_conj (z : S) (hz : orderOf z = 5) : ∃ (g : S) (m : ℤ), (g * z * g⁻¹) ^ m = Ps := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hfact : (Nat.card S).factorization 5 = 1 := by
    rw [card_S]
    have h : (9999360 : ℕ) = 5 * 1999872 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self Nat.prime_five,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 5 ∣ 1999872 by norm_num)]
  have key : ∀ w : S, orderOf w = 5 →
      ∃ Q : Sylow 5 S, (Q : Subgroup S) = Subgroup.zpowers w := by
    intro w hw
    have hH : Nat.card (Subgroup.zpowers w) = 5 := by rw [Nat.card_zpowers, hw]
    have hP : IsPGroup 5 (Subgroup.zpowers w) :=
      IsPGroup.of_card (n := 1) (by rw [hH]; norm_num)
    obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
    refine ⟨Q, ?_⟩
    have hQc : Nat.card (Q : Subgroup S) = 5 := by
      rw [Sylow.card_eq_multiplicity, hfact]; norm_num
    exact (Subgroup.eq_of_le_of_card_ge hQ (by rw [hH, hQc])).symm
  obtain ⟨Qz, hQz⟩ := key z hz
  obtain ⟨QP, hQP⟩ := key Ps orderOf_Ps
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S Qz QP
  have hP : Ps ∈ ((g • Qz : Sylow 5 S) : Subgroup S) := by
    rw [hg, hQP]
    exact Subgroup.mem_zpowers Ps
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hP
  obtain ⟨s, hs, hsP⟩ := hP
  rw [hQz] at hs
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  refine ⟨g, m, ?_⟩
  rw [← hsP]
  simp [MulAut.conj_apply, conj_zpow]

abbrev A6 := alternatingGroup (Fin 6)

@[expose] def v0 : A6 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem invol_conj : ∀ u : A6, u * u = 1 → u ≠ 1 → ∃ k : A6, k * u * k⁻¹ = v0 := by
  decide +kernel

theorem invol_conj_of_equiv {K : Type*} [Group K] (e : K ≃* A6) {u v : K} (hu : u * u = 1)
    (hu1 : u ≠ 1) (hv : v * v = 1) (hv1 : v ≠ 1) : ∃ k : K, k * u * k⁻¹ = v := by
  have hu' : e u * e u = 1 := by rw [← map_mul, hu, map_one]
  have hv' : e v * e v = 1 := by rw [← map_mul, hv, map_one]
  have hu1' : e u ≠ 1 := fun h => hu1 (e.injective (by rw [h, map_one]))
  have hv1' : e v ≠ 1 := fun h => hv1 (e.injective (by rw [h, map_one]))
  obtain ⟨k₁, hk₁⟩ := invol_conj (e u) hu' hu1'
  obtain ⟨k₂, hk₂⟩ := invol_conj (e v) hv' hv1'
  refine ⟨e.symm (k₂⁻¹ * k₁), e.injective ?_⟩
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply]
  calc k₂⁻¹ * k₁ * e u * (k₂⁻¹ * k₁)⁻¹ = k₂⁻¹ * (k₁ * e u * k₁⁻¹) * k₂ := by group
    _ = k₂⁻¹ * v0 * k₂ := by rw [hk₁]
    _ = e v := by rw [← hk₂]; group

@[expose] def Q2 : M5 :=
  !![1, 0, 0, 0, 0; 1, 1, 1, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 1, 0; 1, 0, 1, 0, 1]

@[expose] def Q3 : M5 :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 1, 0, 1, 1, 0; 1, 1, 1, 0, 0; 0, 1, 1, 0, 1]

theorem circ_one : circ ![1, 0, 0, 0, 0] = 1 * (1 : M5)ᵀ := by decide

theorem circ_Q2 : circ ![1, 1, 0, 0, 1] = Q2 * Q2ᵀ := by decide

theorem circ_Q3 : circ ![1, 0, 1, 1, 0] = Q3 * Q3ᵀ := by decide

set_option maxRecDepth 100000 in
theorem Q2_det : Q2.det = 1 := by decide

set_option maxRecDepth 100000 in
theorem Q3_det : Q3.det = 1 := by decide

theorem exists_Q (a : S) (hsym : (a : M5)ᵀ = a) (hP : a * Ps = Ps * a) :
    ∃ Q : S, (a : M5) = (Q : M5) * (Q : M5)ᵀ := by
  have h1 : (a : M5) * Pm = Pm * (a : M5) := congrArg Subtype.val hP
  have h3 := circ_of_comm a h1
  have h4 : (circ (fun d => (a : M5) 0 d)).det = 1 := by rw [← h3]; exact a.2
  have h5 : (circ (fun d => (a : M5) 0 d))ᵀ = circ (fun d => (a : M5) 0 d) := by
    rw [← h3]; exact hsym
  have hc := symm_circ _ h5 h4
  rcases hc with hc | hc | hc
  · refine ⟨1, ?_⟩
    rw [h3, hc, circ_one]
    simp
  · refine ⟨⟨Q2, Q2_det⟩, ?_⟩
    rw [h3, hc, circ_Q2]
  · refine ⟨⟨Q3, Q3_det⟩, ?_⟩
    rw [h3, hc, circ_Q3]

@[expose] def y0m : M5 :=
  !![1, 1, 1, 0, 0; 1, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem y0m_spec : y0mᵀ * y0m = bm := by decide

set_option maxRecDepth 100000 in
theorem y0m_det : y0m.det = 1 := by decide

@[expose] def y0s : S := ⟨y0m, y0m_det⟩

end CFSG.QuasithinUnique.Id2519.Tab.L5
