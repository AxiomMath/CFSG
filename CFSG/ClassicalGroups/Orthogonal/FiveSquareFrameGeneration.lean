module

public import TauCeti.LinearAlgebra.QuadraticForm.Standard
public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.ClassicalGroups.Symplectic.OrthogonalFiveModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveSimilarity

open QuadraticMap
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open scoped commutatorElement

namespace CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration

namespace Generic

@[expose] public noncomputable def Q (K : Type) [Field K] : QuadraticForm K (Fin 5 → K) :=
  QuadraticMap.weightedSumSquares K (1 : Fin 5 → K)

@[expose] public noncomputable def e (K : Type) [Field K] : Module.Basis (Fin 5) K (Fin 5 → K) :=
  Pi.basisFun K (Fin 5)

@[simp] public theorem e_apply (K : Type) [Field K] (i : Fin 5) :
    e K i = Pi.single i 1 := Pi.basisFun_apply K (Fin 5) i

public theorem two_ne_zero (K : Type) [Field K] [CharP K 5] : (2 : K) ≠ 0 := by
  intro h
  have hdvd : 5 ∣ 2 := (CharP.cast_eq_zero_iff K 5 2).1 h
  norm_num at hdvd

theorem three_ne_zero (K : Type) [Field K] [CharP K 5] : (3 : K) ≠ 0 := by
  intro h
  have hdvd : 5 ∣ 3 := (CharP.cast_eq_zero_iff K 5 3).1 h
  norm_num at hdvd

public theorem polar_apply (K : Type) [Field K] [CharP K 5] (x y : Fin 5 → K) :
    polar (Q K) x y = 2 * ∑ i, x i * y i := by
  rw [Q, ← QuadraticMap.polarBilin_apply_apply]
  rw [TauCeti.QuadraticForm.polarBilin_weightedSumSquares_one]
  simp [LinearMap.smul_apply, Matrix.toLinearMap₂'_apply', Matrix.one_mulVec, dotProduct,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

public theorem Q_single (K : Type) [Field K] [CharP K 5] (i : Fin 5) : Q K (e K i) = 1 := by
  rw [Q, e_apply, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_five]
  fin_cases i <;> simp [Pi.single_apply]

public theorem polar_single (K : Type) [Field K] [CharP K 5] (i j : Fin 5) :
    polar (Q K) (e K i) (e K j) = if i = j then 2 else 0 := by
  rw [polar_apply, Fin.sum_univ_five]
  fin_cases i <;> fin_cases j <;> simp [e_apply, Pi.single_apply]

theorem polar_single_of_ne (K : Type) [Field K] [CharP K 5] {i j : Fin 5} (h : i ≠ j) :
    polar (Q K) (e K i) (e K j) = 0 := by
  rw [polar_single, if_neg h]

public theorem Q_nondegenerate (K : Type) [Field K] [CharP K 5] : (Q K).Nondegenerate := by
  letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero K)
  exact QuadraticMap.nondegenerate_weightedSumSquares (w := (1 : Fin 5 → K))
    (fun _ => isRegular_one)

public theorem polar_nondegenerate (K : Type) [Field K] [CharP K 5] :
    (polarBilin (Q K)).Nondegenerate := by
  letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero K)
  exact QuadraticMap.nondegenerate_polar_iff.mpr (Q_nondegenerate K)

noncomputable def u (K : Type) [Field K] : Fin 5 → K := e K 0 + 2 • e K 1

noncomputable def v (K : Type) [Field K] : Fin 5 → K := 4 • (e K 0 - 2 • e K 1)

theorem v_eq (K : Type) [Field K] [CharP K 5] : v K = 4 • e K 0 + 2 • e K 1 := by
  funext j
  fin_cases j <;> simp [v, e_apply, Pi.single_apply]
  linear_combination (-2 : K) * (CharP.cast_eq_zero K 5)

theorem Q_u (K : Type) [Field K] [CharP K 5] : Q K (u K) = 0 := by
  simp [u, e_apply, Q, QuadraticMap.weightedSumSquares_apply, Pi.one_apply, Fin.sum_univ_five]
  ring_nf
  exact (CharP.cast_eq_zero_iff K 5 5).2 (by norm_num)

theorem Q_v (K : Type) [Field K] [CharP K 5] : Q K (v K) = 0 := by
  rw [v_eq]
  simp [e_apply, Q, QuadraticMap.weightedSumSquares_apply, Pi.one_apply, Fin.sum_univ_five]
  ring_nf
  exact (CharP.cast_eq_zero_iff K 5 20).2 (by norm_num)

theorem polar_u_v (K : Type) [Field K] [CharP K 5] : polar (Q K) (u K) (v K) = 1 := by
  rw [v_eq, polar_apply]
  simp [u, e_apply, Fin.sum_univ_five]
  ring_nf
  linear_combination (CharP.cast_eq_zero_iff K 5 15).2 (by norm_num)

theorem sum_u (K : Type) [Field K] (w : Fin 5 → K) :
    ∑ i, u K i * w i = w 0 + 2 * w 1 := by
  simp [u, e_apply, Fin.sum_univ_five, Pi.single_apply]

theorem sum_v (K : Type) [Field K] [CharP K 5] (w : Fin 5 → K) :
    ∑ i, v K i * w i = 4 * w 0 + 2 * w 1 := by
  rw [v_eq]
  simp [e_apply, Fin.sum_univ_five, Pi.single_apply]

noncomputable def P (K : Type) [Field K] [CharP K 5] : HypPair (Q K) where
  e := u K
  f := v K
  Q_e := Q_u K
  Q_f := Q_v K
  polar_ef := polar_u_v K

theorem P_e (K : Type) [Field K] [CharP K 5] : (P K).e = u K := rfl

theorem P_f (K : Type) [Field K] [CharP K 5] : (P K).f = v K := rfl

theorem perp_subset_span (K : Type) [Field K] [CharP K 5] :
    (P K).perp ≤ Submodule.span K ({e K 2, e K 3, e K 4} : Set (Fin 5 → K)) := by
  intro w hw
  rw [HypPair.mem_perp] at hw
  have h1 : 2 * (w 0 + 2 * w 1) = 0 := by
    have := hw.1
    rw [P_e, polar_apply, sum_u] at this
    exact this
  have h2 : 2 * (4 * w 0 + 2 * w 1) = 0 := by
    have := hw.2
    rw [P_f, polar_apply, sum_v] at this
    exact this
  have hs1 : w 0 + 2 * w 1 = 0 := (mul_eq_zero.mp h1).resolve_left (two_ne_zero K)
  have hs2 : 4 * w 0 + 2 * w 1 = 0 := (mul_eq_zero.mp h2).resolve_left (two_ne_zero K)
  have h3 : (3 : K) * w 0 = 0 := by
    calc (3 : K) * w 0 = (4 * w 0 + 2 * w 1) - (w 0 + 2 * w 1) := by ring
      _ = 0 := by rw [hs2, hs1, sub_zero]
  have h0 : w 0 = 0 := (mul_eq_zero.mp h3).resolve_left (three_ne_zero K)
  have h1' : w 1 = 0 := by
    have := hs1
    rw [h0, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_left (two_ne_zero K)
  have hwdecomp : w = w 2 • e K 2 + w 3 • e K 3 + w 4 • e K 4 := by
    funext j
    fin_cases j <;> simp [e_apply, Pi.single_apply, h0, h1']
  rw [hwdecomp]
  have h2span : e K 2 ∈ Submodule.span K ({e K 2, e K 3, e K 4} : Set (Fin 5 → K)) :=
    Submodule.subset_span (by
      change e K 2 = e K 2 ∨ e K 2 = e K 3 ∨ e K 2 = e K 4
      exact Or.inl rfl)
  have h3span : e K 3 ∈ Submodule.span K ({e K 2, e K 3, e K 4} : Set (Fin 5 → K)) :=
    Submodule.subset_span (by
      change e K 3 = e K 2 ∨ e K 3 = e K 3 ∨ e K 3 = e K 4
      exact Or.inr (Or.inl rfl))
  have h4span : e K 4 ∈ Submodule.span K ({e K 2, e K 3, e K 4} : Set (Fin 5 → K)) :=
    Submodule.subset_span (by
      change e K 4 = e K 2 ∨ e K 4 = e K 3 ∨ e K 4 = e K 4
      exact Or.inr (Or.inr rfl))
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ h2span) (Submodule.smul_mem _ _ h3span)
  · exact Submodule.smul_mem _ _ h4span

theorem e_mem_perp (K : Type) [Field K] [CharP K 5] {i : Fin 5}
    (hi : i = 2 ∨ i = 3 ∨ i = 4) : e K i ∈ (P K).perp := by
  rw [HypPair.mem_perp, P_e, P_f]
  constructor
  · rw [polar_apply, sum_u]
    rcases hi with rfl | rfl | rfl <;> simp [e_apply, Pi.single_apply]
  · rw [polar_apply, sum_v]
    rcases hi with rfl | rfl | rfl <;> simp [e_apply, Pi.single_apply]

theorem hspan (K : Type) [Field K] [CharP K 5] :
    (P K).perp ≤ Submodule.span K {x | x ∈ (P K).perp ∧ Q K x ≠ 0} := by
  refine (perp_subset_span K).trans (Submodule.span_mono ?_)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨e_mem_perp K (Or.inl rfl), by rw [Q_single]; exact one_ne_zero⟩
  · exact ⟨e_mem_perp K (Or.inr (Or.inl rfl)), by rw [Q_single]; exact one_ne_zero⟩
  · exact ⟨e_mem_perp K (Or.inr (Or.inr rfl)), by rw [Q_single]; exact one_ne_zero⟩

noncomputable abbrev O (K : Type) [Field K] [CharP K 5] : Subgroup ((Fin 5 → K) ≃ₗ[K] (Fin 5 → K)) :=
  TauCeti.QuadraticMap.orthogonalGroup (Q K)

noncomputable abbrev D (K : Type) [Field K] [CharP K 5] : Subgroup ((Fin 5 → K) ≃ₗ[K] (Fin 5 → K)) :=
  ⁅O K, O K⁆

theorem derived_isSimpleGroup (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) : IsSimpleGroup ↥(D K) := by
  have hdim : Module.finrank K (Fin 5 → K) = 5 := by
    simpa using Module.finrank_fin_fun (R := K) (n := 5)
  obtain ⟨d, psi, eO, hpsi, happ, hsymm⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalFive.finite_odd_five_selfAdjoint_form_similarity
      hodd (Q K) (polar_nondegenerate K) hdim
  let eComm : ↥(commutator (O K)) ≃*
      ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.ComponentClassification.CatalogueBOrthogonalFive.selfAdjointForm K))) :=
    MulEquiv.commutatorCongr eO
  let eMap : ↥(commutator (O K)) ≃* ↥(D K) :=
    (Subgroup.equivMapOfInjective (commutator (O K)) (O K).subtype
      (O K).subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (O K)))
  let eP := CFSG.ClassicalGroups.Symplectic.pspFourEquivDerivedOrthogonal (K := K) hodd
  let eD : ↥(D K) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 K) :=
    eMap.symm.trans (eComm.trans eP.symm)
  have h : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ 2) ∨
      (Nat.card K = 2 ∧ 3 ≤ 2) := by
    rcases Nat.lt_or_ge (Nat.card K) 4 with h4 | h4
    · have h3 : Nat.card K = 3 := by omega
      exact Or.inr (Or.inl ⟨h3, by norm_num⟩)
    · exact Or.inl (Or.inr h4)
  haveI : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num) h
  exact eD.isSimpleGroup

theorem elementary_le_derived (K : Type) [Field K] [CharP K 5] :
    elementaryGroup (Q K) ≤ D K :=
  elementaryGroup_le_commutator_of_perp_le_span (polar_nondegenerate K) (P K) (hspan K)

theorem elementary_ne_bot (K : Type) [Field K] [CharP K 5] : elementaryGroup (Q K) ≠ ⊥ := by
  intro hbot
  have hmem : eichler (Q K) (P K).e (e K 2) ∈ elementaryGroup (Q K) :=
    eichler_mem_elementaryGroup (Q K) (P K).e (e K 2)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (eichler_ne_one_of_anisotropic (P K) (e_mem_perp K (Or.inl rfl))
    (by rw [Q_single]; exact one_ne_zero)) hmem

theorem derived_eq_elementary (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) :
    D K = elementaryGroup (Q K) :=
  commutator_orthogonalGroup_eq_elementaryGroup_of_isSimpleGroup
    (elementary_le_derived K) (elementary_ne_bot K) (derived_isSimpleGroup K hodd hcard)

public theorem Q_sub_ne (K : Type) [Field K] [CharP K 5] {i j : Fin 5} (hij : i ≠ j) :
    Q K (e K i - e K j) = 2 := by
  have h : Q K (e K i - e K j) =
      Q K (e K i) + Q K (e K j) - polar (Q K) (e K i) (e K j) := by
    rw [sub_eq_add_neg, QuadraticMap.map_add (Q K), QuadraticMap.map_neg (Q K), polar_neg_right]
    ring
  rw [h, Q_single, Q_single, polar_single_of_ne K hij]
  ring

public theorem polar_sub_left_self (K : Type) [Field K] [CharP K 5] {i j : Fin 5}
    (hij : i ≠ j) : polar (Q K) (e K i - e K j) (e K i) = 2 := by
  rw [QuadraticMap.polar_sub_left, polar_single, if_pos rfl,
    polar_single_of_ne K (Ne.symm hij)]
  ring

public theorem polar_sub_left_of_ne (K : Type) [Field K] [CharP K 5] {i j k : Fin 5}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    polar (Q K) (e K i - e K j) (e K k) = 0 := by
  rw [QuadraticMap.polar_sub_left, polar_single_of_ne K (Ne.symm hki),
    polar_single_of_ne K (Ne.symm hkj)]
  ring

noncomputable def r (K : Type) [Field K] [CharP K 5] : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) :=
  reflect (Q K) (e K 2 - e K 4)

noncomputable def s (K : Type) [Field K] [CharP K 5] : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) :=
  reflect (Q K) (e K 2 - e K 3)

noncomputable def k (K : Type) [Field K] [CharP K 5] : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) :=
  ⁅r K, s K⁆

theorem r_mem (K : Type) [Field K] [CharP K 5] : r K ∈ O K :=
  reflect_mem_orthogonalGroup (Q K) _

theorem s_mem (K : Type) [Field K] [CharP K 5] : s K ∈ O K :=
  reflect_mem_orthogonalGroup (Q K) _

theorem k_mem_D (K : Type) [Field K] [CharP K 5] : k K ∈ D K :=
  Subgroup.commutator_mem_commutator (r_mem K) (s_mem K)

public theorem reflect_sub_apply_left (K : Type) [Field K] [CharP K 5] {i j : Fin 5}
    (hij : i ≠ j) : reflect (Q K) (e K i - e K j) (e K i) = e K j := by
  have hv : Q K (e K i - e K j) ≠ 0 := by
    rw [Q_sub_ne K hij]
    exact two_ne_zero K
  rw [reflect_apply hv, polar_sub_left_self K hij, Q_sub_ne K hij,
    div_self (two_ne_zero K), one_smul]
  abel

public theorem reflect_sub_apply_right (K : Type) [Field K] [CharP K 5] {i j : Fin 5}
    (hij : i ≠ j) : reflect (Q K) (e K i - e K j) (e K j) = e K i := by
  have h := congrArg (fun g : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) => g (e K i))
    (reflect_mul_self (Q K) (e K i - e K j))
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] at h
  rw [reflect_sub_apply_left K hij] at h
  exact h

theorem r_e2 (K : Type) [Field K] [CharP K 5] : r K (e K 2) = e K 4 := by
  rw [r]
  exact reflect_sub_apply_left K (i := 2) (j := 4) (by decide)

theorem r_e4 (K : Type) [Field K] [CharP K 5] : r K (e K 4) = e K 2 := by
  rw [r]
  exact reflect_sub_apply_right K (i := 2) (j := 4) (by decide)

public theorem reflect_sub_apply_of_ne (K : Type) [Field K] [CharP K 5] {i j k : Fin 5}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    reflect (Q K) (e K i - e K j) (e K k) = e K k := by
  exact reflect_apply_of_polar_eq_zero (polar_sub_left_of_ne K hij hki hkj)

theorem r_e0 (K : Type) [Field K] [CharP K 5] : r K (e K 0) = e K 0 :=
  reflect_sub_apply_of_ne K (i := 2) (j := 4) (k := 0) (by decide) (by decide) (by decide)

theorem r_e1 (K : Type) [Field K] [CharP K 5] : r K (e K 1) = e K 1 :=
  reflect_sub_apply_of_ne K (i := 2) (j := 4) (k := 1) (by decide) (by decide) (by decide)

theorem r_e3 (K : Type) [Field K] [CharP K 5] : r K (e K 3) = e K 3 :=
  reflect_sub_apply_of_ne K (i := 2) (j := 4) (k := 3) (by decide) (by decide) (by decide)

theorem s_e2 (K : Type) [Field K] [CharP K 5] : s K (e K 2) = e K 3 := by
  rw [s]
  exact reflect_sub_apply_left K (i := 2) (j := 3) (by decide)

theorem s_e3 (K : Type) [Field K] [CharP K 5] : s K (e K 3) = e K 2 := by
  rw [s]
  exact reflect_sub_apply_right K (i := 2) (j := 3) (by decide)

theorem s_e0 (K : Type) [Field K] [CharP K 5] : s K (e K 0) = e K 0 :=
  reflect_sub_apply_of_ne K (i := 2) (j := 3) (k := 0) (by decide) (by decide) (by decide)

theorem s_e1 (K : Type) [Field K] [CharP K 5] : s K (e K 1) = e K 1 :=
  reflect_sub_apply_of_ne K (i := 2) (j := 3) (k := 1) (by decide) (by decide) (by decide)

theorem s_e4 (K : Type) [Field K] [CharP K 5] : s K (e K 4) = e K 4 :=
  reflect_sub_apply_of_ne K (i := 2) (j := 3) (k := 4) (by decide) (by decide) (by decide)

theorem r_inv (K : Type) [Field K] [CharP K 5] : (r K)⁻¹ = r K :=
  reflect_inv (Q K) _

theorem s_inv (K : Type) [Field K] [CharP K 5] : (s K)⁻¹ = s K :=
  reflect_inv (Q K) _

theorem k_e0 (K : Type) [Field K] [CharP K 5] : k K (e K 0) = e K 0 := by
  rw [k, commutatorElement_def, r_inv, s_inv]
  change r K (s K (r K (s K (e K 0)))) = e K 0
  rw [s_e0, r_e0, s_e0, r_e0]

theorem k_e1 (K : Type) [Field K] [CharP K 5] : k K (e K 1) = e K 1 := by
  rw [k, commutatorElement_def, r_inv, s_inv]
  change r K (s K (r K (s K (e K 1)))) = e K 1
  rw [s_e1, r_e1, s_e1, r_e1]

theorem k_e2 (K : Type) [Field K] [CharP K 5] : k K (e K 2) = e K 4 := by
  rw [k, commutatorElement_def, r_inv, s_inv]
  change r K (s K (r K (s K (e K 2)))) = e K 4
  rw [s_e2, r_e3, s_e3, r_e2]

theorem k_e3 (K : Type) [Field K] [CharP K 5] : k K (e K 3) = e K 2 := by
  rw [k, commutatorElement_def, r_inv, s_inv]
  change r K (s K (r K (s K (e K 3)))) = e K 2
  rw [s_e3, r_e2, s_e4, r_e4]

theorem k_e4 (K : Type) [Field K] [CharP K 5] : k K (e K 4) = e K 3 := by
  rw [k, commutatorElement_def, r_inv, s_inv]
  change r K (s K (r K (s K (e K 4)))) = e K 3
  rw [s_e4, r_e4, s_e2, r_e3]

theorem k_u (K : Type) [Field K] [CharP K 5] : k K (u K) = u K := by
  rw [u, map_add, map_nsmul, k_e0, k_e1]

@[expose] public noncomputable def stdFrame (K : Type) [Field K] [CharP K 5] : FrameData (Q K) where
  e := e K
  orth := fun i j hij => by rw [polar_single K, if_neg hij]
  norm := fun i hi => Q_single K i
  last := by
    rw [Q_single]
    exact one_ne_zero
  nondeg := polar_nondegenerate K

noncomputable abbrev z (K : Type) [Field K] [CharP K 5] : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) :=
  (stdFrame K).z

theorem z_mem_D (K : Type) [Field K] [CharP K 5] : z K ∈ D K :=
  (stdFrame K).z_mem_commutator

theorem z_mul_self (K : Type) [Field K] [CharP K 5] : z K * z K = 1 :=
  (stdFrame K).z_mul_self

noncomputable def frameVectors (K : Type) [Field K] [CharP K 5] : Set (Fin 5 → K) :=
  {x | ∃ i : Fin 5, x = e K i ∨ x = -e K i}

noncomputable def zD (K : Type) [Field K] [CharP K 5] : ↥(D K) :=
  ⟨z K, z_mem_D K⟩

noncomputable def zCentralizer (K : Type) [Field K] [CharP K 5] : Subgroup ↥(D K) :=
  Subgroup.centralizer ({zD K} : Set ↥(D K))

noncomputable def frameNormalizer (K : Type) [Field K] [CharP K 5] : Subgroup ↥(D K) :=
  @MulAction.stabilizer (↥(D K)) (Set (Fin 5 → K)) _ (Set.mulActionSet) (frameVectors K)

noncomputable def J (K : Type) [Field K] [CharP K 5] :
    Subgroup ((Fin 5 → K) ≃ₗ[K] (Fin 5 → K)) :=
  (zCentralizer K ⊔ frameNormalizer K).map (D K).subtype

public theorem stdFrame_e (K : Type) [Field K] [CharP K 5] (i : Fin 5) :
    (stdFrame K).e i = e K i := rfl

theorem z_e2 (K : Type) [Field K] [CharP K 5] : z K (e K 2) = -e K 2 := by
  have h := (stdFrame K).z_e 2
  rw [stdFrame_e] at h
  simpa using h

theorem z_e3 (K : Type) [Field K] [CharP K 5] : z K (e K 3) = -e K 3 := by
  have h := (stdFrame K).z_e 3
  rw [stdFrame_e] at h
  simpa using h

theorem z_e4 (K : Type) [Field K] [CharP K 5] : z K (e K 4) = e K 4 := by
  have h := (stdFrame K).z_e 4
  rw [stdFrame_e] at h
  simpa using h

theorem z_e0 (K : Type) [Field K] [CharP K 5] : z K (e K 0) = -e K 0 := by
  have h := (stdFrame K).z_e 0
  rw [stdFrame_e] at h
  simpa using h

theorem z_e1 (K : Type) [Field K] [CharP K 5] : z K (e K 1) = -e K 1 := by
  have h := (stdFrame K).z_e 1
  rw [stdFrame_e] at h
  simpa using h

theorem z_u (K : Type) [Field K] [CharP K 5] : z K (u K) = -u K := by
  rw [u, map_add, map_nsmul, z_e0, z_e1]
  module

theorem z_v (K : Type) [Field K] [CharP K 5] : z K (v K) = -v K := by
  rw [v_eq, map_add, map_nsmul, map_nsmul, z_e0, z_e1]
  module

theorem z_mem_O (K : Type) [Field K] [CharP K 5] : z K ∈ O K :=
  Subgroup.commutator_le_self (O K) (z_mem_D K)

theorem eichler_mem_D (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) (u w : Fin 5 → K) :
    eichler (Q K) u w ∈ D K := by
  rw [derived_eq_elementary K hodd hcard]
  exact eichler_mem_elementaryGroup (Q K) u w

theorem eichler_u_smul_e2_mem_zCentralizer (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) (c : K) :
    (⟨eichler (Q K) (u K) (c • e K 2), eichler_mem_D K hodd hcard _ _⟩ : ↥(D K)) ∈
      zCentralizer K := by
  rw [zCentralizer, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  have hconj : z K * eichler (Q K) (u K) (c • e K 2) * (z K)⁻¹ =
      eichler (Q K) (u K) (c • e K 2) := by
    rw [eichler_conj (z_mem_O K)]
    rw [z_u, map_smul, z_e2]
    rw [show c • (-e K 2) = -(c • e K 2) by simp]
    rw [show -u K = (-1 : K) • u K by simp]
    rw [eichler_smul_left]
    simp
  have hzEz : z K * eichler (Q K) (u K) (c • e K 2) * z K =
      eichler (Q K) (u K) (c • e K 2) := by
    simpa [inv_eq_of_mul_eq_one_right (z_mul_self K)] using hconj
  calc eichler (Q K) (u K) (c • e K 2) * z K =
      (z K * eichler (Q K) (u K) (c • e K 2) * z K) * z K := by rw [hzEz]
    _ = z K * eichler (Q K) (u K) (c • e K 2) := by
      rw [mul_assoc, mul_assoc, z_mul_self, mul_one]

theorem eichler_u_smul_e3_mem_zCentralizer (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) (c : K) :
    (⟨eichler (Q K) (u K) (c • e K 3), eichler_mem_D K hodd hcard _ _⟩ : ↥(D K)) ∈
      zCentralizer K := by
  rw [zCentralizer, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  have hconj : z K * eichler (Q K) (u K) (c • e K 3) * (z K)⁻¹ =
      eichler (Q K) (u K) (c • e K 3) := by
    rw [eichler_conj (z_mem_O K)]
    rw [z_u, map_smul, z_e3]
    rw [show c • (-e K 3) = -(c • e K 3) by simp]
    rw [show -u K = (-1 : K) • u K by simp]
    rw [eichler_smul_left]
    simp
  have hzEz : z K * eichler (Q K) (u K) (c • e K 3) * z K =
      eichler (Q K) (u K) (c • e K 3) := by
    simpa [inv_eq_of_mul_eq_one_right (z_mul_self K)] using hconj
  calc eichler (Q K) (u K) (c • e K 3) * z K =
      (z K * eichler (Q K) (u K) (c • e K 3) * z K) * z K := by rw [hzEz]
    _ = z K * eichler (Q K) (u K) (c • e K 3) := by
      rw [mul_assoc, mul_assoc, z_mul_self, mul_one]

theorem eichler_v_smul_e2_mem_zCentralizer (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) (c : K) :
    (⟨eichler (Q K) (v K) (c • e K 2), eichler_mem_D K hodd hcard _ _⟩ : ↥(D K)) ∈
      zCentralizer K := by
  rw [zCentralizer, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  have hconj : z K * eichler (Q K) (v K) (c • e K 2) * (z K)⁻¹ =
      eichler (Q K) (v K) (c • e K 2) := by
    rw [eichler_conj (z_mem_O K)]
    rw [z_v, map_smul, z_e2]
    rw [show c • (-e K 2) = -(c • e K 2) by simp]
    rw [show -v K = (-1 : K) • v K by simp]
    rw [eichler_smul_left]
    simp
  have hzEz : z K * eichler (Q K) (v K) (c • e K 2) * z K =
      eichler (Q K) (v K) (c • e K 2) := by
    simpa [inv_eq_of_mul_eq_one_right (z_mul_self K)] using hconj
  calc eichler (Q K) (v K) (c • e K 2) * z K =
      (z K * eichler (Q K) (v K) (c • e K 2) * z K) * z K := by rw [hzEz]
    _ = z K * eichler (Q K) (v K) (c • e K 2) := by
      rw [mul_assoc, mul_assoc, z_mul_self, mul_one]

theorem mem_frameNormalizer_iff (K : Type) [Field K] [CharP K 5] [Finite K]
    (g : ↥(D K)) :
    g ∈ frameNormalizer K ↔
      ∀ ⦃b : Fin 5 → K⦄, b ∈ frameVectors K → g • b ∈ frameVectors K := by
  rw [frameNormalizer]
  exact MulAction.mem_stabilizer_set' (Set.toFinite _)

theorem neg_mem_frameVectors (K : Type) [Field K] [CharP K 5] {x : Fin 5 → K}
    (hx : x ∈ frameVectors K) : -x ∈ frameVectors K := by
  rcases hx with ⟨i, rfl | rfl⟩
  · exact ⟨i, Or.inr rfl⟩
  · exact ⟨i, Or.inl (by simp)⟩

theorem k_e0_mem_frame (K : Type) [Field K] [CharP K 5] :
    k K (e K 0) ∈ frameVectors K := ⟨0, Or.inl (by rw [k_e0])⟩

theorem k_e1_mem_frame (K : Type) [Field K] [CharP K 5] :
    k K (e K 1) ∈ frameVectors K := ⟨1, Or.inl (by rw [k_e1])⟩

theorem k_e2_mem_frame (K : Type) [Field K] [CharP K 5] :
    k K (e K 2) ∈ frameVectors K := ⟨4, Or.inl (by rw [k_e2])⟩

theorem k_e3_mem_frame (K : Type) [Field K] [CharP K 5] :
    k K (e K 3) ∈ frameVectors K := ⟨2, Or.inl (by rw [k_e3])⟩

theorem k_e4_mem_frame (K : Type) [Field K] [CharP K 5] :
    k K (e K 4) ∈ frameVectors K := ⟨3, Or.inl (by rw [k_e4])⟩

theorem k_mem_frameNormalizer (K : Type) [Field K] [CharP K 5] [Finite K] :
    (⟨k K, k_mem_D K⟩ : ↥(D K)) ∈ frameNormalizer K := by
  rw [mem_frameNormalizer_iff]
  intro b hb
  rcases hb with ⟨i, rfl | rfl⟩
  · rw [Subgroup.smul_def, LinearEquiv.smul_def]
    change k K (e K i) ∈ frameVectors K
    fin_cases i <;>
      first
      | exact k_e0_mem_frame K
      | exact k_e1_mem_frame K
      | exact k_e2_mem_frame K
      | exact k_e3_mem_frame K
      | exact k_e4_mem_frame K
  · rw [Subgroup.smul_def, LinearEquiv.smul_def]
    change k K (-e K i) ∈ frameVectors K
    rw [map_neg]
    fin_cases i <;>
      first
      | exact neg_mem_frameVectors K (k_e0_mem_frame K)
      | exact neg_mem_frameVectors K (k_e1_mem_frame K)
      | exact neg_mem_frameVectors K (k_e2_mem_frame K)
      | exact neg_mem_frameVectors K (k_e3_mem_frame K)
      | exact neg_mem_frameVectors K (k_e4_mem_frame K)

theorem k_mem_J (K : Type) [Field K] [CharP K 5] [Finite K] : k K ∈ J K :=
  Subgroup.mem_map.mpr ⟨⟨k K, k_mem_D K⟩, le_sup_right (a := zCentralizer K) (b := frameNormalizer K) (k_mem_frameNormalizer K), rfl⟩

theorem J_le_O (K : Type) [Field K] [CharP K 5] : J K ≤ O K :=
  (Subgroup.map_subtype_le (zCentralizer K ⊔ frameNormalizer K)).trans
    (Subgroup.commutator_le_self (O K))

theorem eichler_u_smul_e2_mem_J (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) (c : K) :
    eichler (Q K) (u K) (c • e K 2) ∈ J K :=
  Subgroup.mem_map.mpr
    ⟨⟨eichler (Q K) (u K) (c • e K 2), eichler_mem_D K hodd hcard _ _⟩,
      le_sup_left (a := zCentralizer K) (b := frameNormalizer K)
        (eichler_u_smul_e2_mem_zCentralizer K hodd hcard c), rfl⟩

theorem eichler_u_smul_e3_mem_J (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) (c : K) :
    eichler (Q K) (u K) (c • e K 3) ∈ J K :=
  Subgroup.mem_map.mpr
    ⟨⟨eichler (Q K) (u K) (c • e K 3), eichler_mem_D K hodd hcard _ _⟩,
      le_sup_left (a := zCentralizer K) (b := frameNormalizer K)
        (eichler_u_smul_e3_mem_zCentralizer K hodd hcard c), rfl⟩

theorem eichler_u_smul_e4_mem_J (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) (c : K) :
    eichler (Q K) (u K) (c • e K 4) ∈ J K := by
  have hE2 : eichler (Q K) (u K) (c • e K 2) ∈ J K :=
    eichler_u_smul_e2_mem_J K hodd hcard c
  have hconj := eichler_mem_of_conj (H := J K) (J_le_O K) (k_mem_J K) hE2
  rw [k_u, map_smul, k_e2] at hconj
  exact hconj

theorem polar_u_e2 (K : Type) [Field K] [CharP K 5] : polar (Q K) (u K) (e K 2) = 0 := by
  rw [polar_apply, sum_u]
  simp [e_apply, Pi.single_apply]

theorem polar_u_e3 (K : Type) [Field K] [CharP K 5] : polar (Q K) (u K) (e K 3) = 0 := by
  rw [polar_apply, sum_u]
  simp [e_apply, Pi.single_apply]

theorem polar_u_e4 (K : Type) [Field K] [CharP K 5] : polar (Q K) (u K) (e K 4) = 0 := by
  rw [polar_apply, sum_u]
  simp [e_apply, Pi.single_apply]

theorem polar_v_e2 (K : Type) [Field K] [CharP K 5] : polar (Q K) (v K) (e K 2) = 0 := by
  rw [polar_apply, sum_v]
  simp [e_apply, Pi.single_apply]

theorem span_eichler_mem_J (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) :
    ∀ x ∈ Submodule.span K ({e K 2, e K 3, e K 4} : Set (Fin 5 → K)),
      polar (Q K) (u K) x = 0 ∧ ∀ a : K, eichler (Q K) (u K) (a • x) ∈ J K := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨polar_u_e2 K, fun a => eichler_u_smul_e2_mem_J K hodd hcard a⟩
    · exact ⟨polar_u_e3 K, fun a => eichler_u_smul_e3_mem_J K hodd hcard a⟩
    · exact ⟨polar_u_e4 K, fun a => eichler_u_smul_e4_mem_J K hodd hcard a⟩
  | zero =>
    constructor
    · rw [polar_zero_right]
    · intro a
      rw [smul_zero, eichler_zero_right]
      exact (J K).one_mem
  | add x y hx hy ihx ihy =>
    constructor
    · rw [polar_add_right, ihx.1, ihy.1, add_zero]
    · intro a
      rw [smul_add]
      have hx0 : polar (Q K) (u K) (a • x) = 0 := by
        rw [polar_smul_right_eq, ihx.1, mul_zero]
      have hy0 : polar (Q K) (u K) (a • y) = 0 := by
        rw [polar_smul_right_eq, ihy.1, mul_zero]
      rw [← eichler_mul hx0 hy0]
      exact (J K).mul_mem (ihx.2 a) (ihy.2 a)
  | smul c x hx ih =>
    constructor
    · rw [polar_smul_right_eq, ih.1, mul_zero]
    · intro a
      rw [smul_smul]
      exact ih.2 (a * c)

theorem rootGroup_le_J (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) :
    rootGroup (Q K) (u K) ≤ J K := by
  intro g hg
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
  have hproj : (P K).proj w ∈ Submodule.span K ({e K 2, e K 3, e K 4} : Set (Fin 5 → K)) :=
    perp_subset_span K ((P K).proj_mem_perp w)
  have hJproj : eichler (Q K) (u K) ((P K).proj w) ∈ J K := by
    have h := (span_eichler_mem_J K hodd hcard ((P K).proj w) hproj).2 (1 : K)
    simpa using h
  have hdec : w = (P K).proj w + polar (Q K) w ((P K).f) • u K := by
    have hwu : polar (Q K) w ((P K).e) = 0 := by
      rw [P_e, polar_comm]
      exact hw
    have h := (P K).eq_add_proj w
    rw [hwu, zero_smul, add_zero] at h
    conv_lhs => rw [h]
    rw [P_e]
    abel
  have hdec' : eichler (Q K) (u K) w =
      eichler (Q K) (u K) ((P K).proj w + polar (Q K) w ((P K).f) • u K) := by
    conv_lhs => rw [hdec]
  rw [hdec']
  rw [eichler_add_smul_self (Q_u K)]
  exact hJproj

theorem eichler_v_e2_mem_J (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) :
    eichler (Q K) (v K) (e K 2) ∈ J K := by
  have h := eichler_v_smul_e2_mem_zCentralizer K hodd hcard (1 : K)
  let g : ↥(D K) :=
    ⟨eichler (Q K) (v K) (1 • e K 2), eichler_mem_D K hodd hcard _ _⟩
  have hg : g ∈ zCentralizer K := by simpa [g] using h
  have hJ : eichler (Q K) (v K) (1 • e K 2) ∈ J K :=
    Subgroup.mem_map.mpr ⟨g, le_sup_left (a := zCentralizer K) (b := frameNormalizer K) hg, rfl⟩
  simpa using hJ

theorem elementary_le_J (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) :
    elementaryGroup (Q K) ≤ J K := by
  have hEgen : rootGroup (Q K) (u K) ⊔ Subgroup.zpowers (eichler (Q K) (v K) (e K 2)) =
      elementaryGroup (Q K) :=
    rootGroup_sup_zpowers_eichler (Q := Q K) (polar_nondegenerate K) (Q_u K) (Q_v K)
      (by rw [polar_u_v]; exact one_ne_zero) (polar_v_e2 K) (by rw [Q_single]; exact one_ne_zero)
  rw [← hEgen]
  exact sup_le (rootGroup_le_J K hodd hcard)
    (Subgroup.zpowers_le.mpr (eichler_v_e2_mem_J K hodd hcard))

theorem D_le_J (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) : D K ≤ J K := by
  rw [derived_eq_elementary K hodd hcard]
  exact elementary_le_J K hodd hcard

theorem J_eq_D (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) : J K = D K :=
  le_antisymm (Subgroup.map_subtype_le (zCentralizer K ⊔ frameNormalizer K))
    (D_le_J K hodd hcard)

theorem centralizer_sup_frameNormalizer (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) :
    zCentralizer K ⊔ frameNormalizer K = ⊤ := by
  rw [eq_top_iff]
  intro x hx
  have hxJ : (x : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K)) ∈ J K := by
    rw [J_eq_D K hodd hcard]
    exact x.2
  rcases Subgroup.mem_map.mp hxJ with ⟨y, hy, hyx⟩
  have hyx' : y = x := Subtype.ext hyx
  rwa [hyx'] at hy

theorem not_mem_frameVectors_of_zero_two (K : Type) [Field K] [CharP K 5]
    {x : Fin 5 → K} (h0 : x 0 ≠ 0) (h2 : x 2 ≠ 0) : x ∉ frameVectors K := by
  rintro ⟨i, h | h⟩
  · rw [h] at h0 h2
    fin_cases i <;> simp [e_apply, Pi.single_apply] at h0 h2
  · rw [h] at h0 h2
    fin_cases i <;> simp [e_apply, Pi.single_apply] at h0 h2

theorem k_not_mem_zCentralizer (K : Type) [Field K] [CharP K 5] :
    (⟨k K, k_mem_D K⟩ : ↥(D K)) ∉ zCentralizer K := by
  intro hk
  have hcomm : k K * z K = z K * k K :=
    Subtype.ext_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp hk)
  have h := congrArg (fun g : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) => g (e K 4)) hcomm
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, z_e4, k_e4, z_e3] at h
  have h2 : (2 : K) • e K 3 = 0 := by
    have hh : e K 3 + e K 3 = 0 := by
      have h' := congrArg (fun x : Fin 5 → K => x + e K 3) h
      simpa using h'
    rw [two_smul, hh]
  rcases smul_eq_zero.mp h2 with hzero | hzero
  · exact (two_ne_zero K) hzero
  · exact (e K).ne_zero 3 hzero

theorem zCentralizer_lt_top (K : Type) [Field K] [CharP K 5] :
    zCentralizer K < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  exact k_not_mem_zCentralizer K (by rw [htop]; exact Subgroup.mem_top _)

theorem polar_e0_u (K : Type) [Field K] [CharP K 5] : polar (Q K) (e K 0) (u K) = 2 := by
  rw [polar_apply]
  simp [u, e_apply, Fin.sum_univ_five, Pi.single_apply]

theorem eichler_u_e2_e0 (K : Type) [Field K] [CharP K 5] :
    eichler (Q K) (u K) (e K 2) (e K 0) = 4 • e K 0 + e K 1 + 2 • e K 2 := by
  rw [eichler_apply (Q_u K) (polar_u_e2 K)]
  rw [polar_e0_u, Q_single, polar_single_of_ne K (i := 0) (j := 2) (by decide)]
  rw [u]
  funext j
  fin_cases j <;> simp [e_apply, Pi.single_apply]
  all_goals
    first
    | rfl
    | (have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
       linear_combination (-1 : K) * h5)

theorem a_not_mem_frameNormalizer (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) :
    (⟨eichler (Q K) (u K) (e K 2), eichler_mem_D K hodd hcard _ _⟩ : ↥(D K)) ∉
      frameNormalizer K := by
  intro ha
  have h0mem : e K 0 ∈ frameVectors K := ⟨0, Or.inl rfl⟩
  have ha0 : (⟨eichler (Q K) (u K) (e K 2),
      eichler_mem_D K hodd hcard _ _⟩ : ↥(D K)) • e K 0 ∈ frameVectors K :=
    (MulAction.mem_stabilizer_set.mp ha (e K 0)).mpr h0mem
  rw [Subgroup.smul_def, LinearEquiv.smul_def] at ha0
  change eichler (Q K) (u K) (e K 2) (e K 0) ∈ frameVectors K at ha0
  refine not_mem_frameVectors_of_zero_two K ?_ ?_ ha0
  · rw [eichler_u_e2_e0]
    simp [e_apply, Pi.single_apply]
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero (two_ne_zero K) (two_ne_zero K)
  · rw [eichler_u_e2_e0]
    simp [e_apply, Pi.single_apply]
    exact two_ne_zero K

theorem frameNormalizer_lt_top (K : Type) [Field K] [CharP K 5] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 ≤ Nat.card K) :
    frameNormalizer K < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  exact a_not_mem_frameNormalizer K hodd hcard (by rw [htop]; exact Subgroup.mem_top _)

end Generic

public section

instance fact_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev F : Type := ZMod 5

abbrev V : Type := Fin 5 → F

noncomputable abbrev Q := Generic.Q F

noncomputable abbrev e := Generic.e F

noncomputable abbrev stdFrame := Generic.stdFrame F

noncomputable abbrev O := TauCeti.QuadraticMap.orthogonalGroup Q

noncomputable abbrev derived := ⁅O, O⁆

noncomputable abbrev frameVectors : Set (Fin 5 → F) := {x | ∃ i : Fin 5, x = e i ∨ x = -e i}

noncomputable abbrev z := stdFrame.z

theorem stdFrame_e (i : Fin 5) : stdFrame.e i = e i := rfl

theorem z_e (i : Fin 5) : z (e i) = if (i : ℕ) < 4 then -e i else e i := by
  have h := stdFrame.z_e i
  rwa [stdFrame_e] at h

theorem z_mem_derived : z ∈ derived := stdFrame.z_mem_commutator

noncomputable abbrev zD : ↥derived := ⟨z, z_mem_derived⟩

noncomputable abbrev zCentralizer : Subgroup ↥derived :=
  Subgroup.centralizer ({zD} : Set ↥derived)

noncomputable abbrev frameNormalizer : Subgroup ↥derived :=
  @MulAction.stabilizer ↥derived (Set V) _ (Set.mulActionSet) frameVectors

theorem mem_zCentralizer_iff {g : ↥derived} : g ∈ zCentralizer ↔ g * zD = zD * g :=
  Subgroup.mem_centralizer_singleton_iff

theorem mem_frameNormalizer_iff {g : ↥derived} :
    g ∈ frameNormalizer ↔ ∀ ⦃b : V⦄, b ∈ frameVectors → g • b ∈ frameVectors := by
  rw [frameNormalizer]
  exact MulAction.mem_stabilizer_set' (Set.toFinite _)

theorem derived_isSimpleGroup : IsSimpleGroup ↥derived := by
  have hodd : Odd (Nat.card F) := by rw [Nat.card_zmod]; norm_num
  have hcard : 3 ≤ Nat.card F := by rw [Nat.card_zmod]; norm_num
  change IsSimpleGroup ↥(Generic.D F)
  exact Generic.derived_isSimpleGroup F hodd hcard

theorem centralizer_sup_frameNormalizer : zCentralizer ⊔ frameNormalizer = ⊤ := by
  have hodd : Odd (Nat.card F) := by rw [Nat.card_zmod]; norm_num
  have hcard : 3 ≤ Nat.card F := by rw [Nat.card_zmod]; norm_num
  change Generic.zCentralizer F ⊔ Generic.frameNormalizer F = ⊤
  exact Generic.centralizer_sup_frameNormalizer F hodd hcard

theorem zCentralizer_lt_top : zCentralizer < ⊤ := by
  change Generic.zCentralizer F < ⊤
  exact Generic.zCentralizer_lt_top F

theorem frameNormalizer_lt_top : frameNormalizer < ⊤ := by
  have hodd : Odd (Nat.card F) := by rw [Nat.card_zmod]; norm_num
  have hcard : 3 ≤ Nat.card F := by rw [Nat.card_zmod]; norm_num
  change Generic.frameNormalizer F < ⊤
  exact Generic.frameNormalizer_lt_top F hodd hcard

end

end CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration
