module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedModels
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.Open Matrix
open scoped commutatorElement

section Derived

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem exists_perp_polar_one (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {x : V} (hx : x ∈ P.perp) (hx0 : x ≠ 0) : ∃ y ∈ P.perp, polar Q x y = 1 := by
  obtain ⟨y₀, hy₀, hne⟩ := (HypPair.polarNondegOn_perp hQ P).exists_polar_ne_zero hx hx0
  exact ⟨(polar Q x y₀)⁻¹ • y₀, P.perp.smul_mem _ hy₀, by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hne]⟩

theorem eichler_mem_commutator_of_anisotropic (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {u x : V} (hpu : ∀ y ∈ P.perp, polar Q u y = 0) (hx : x ∈ P.perp) (hQx : Q x ≠ 0) :
    eichler Q u x ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hx0 : x ≠ 0 := fun h => hQx (by rw [h, QuadraticMap.map_zero])
  obtain ⟨y₁, hy₁, hxy₁⟩ := exists_perp_polar_one hQ P hx hx0
  obtain ⟨y, hyP, hxy⟩ : ∃ y ∈ P.perp, polar Q x y = -Q x :=
    ⟨(-Q x) • y₁, P.perp.smul_mem _ hy₁, by rw [polar_smul_right_eq, hxy₁, mul_one]⟩
  have hxu : polar Q x u = 0 := by rw [polar_comm]; exact hpu x hx
  have hgu : reflect Q x u = u := reflect_apply_of_polar_eq_zero hxu
  have hr : reflect Q x y - y = x := by
    rw [reflect_apply hQx, hxy, neg_div, div_self hQx, neg_one_smul]
    abel
  have hc := commutatorElement_eichler (reflect_mem_orthogonalGroup Q x) hgu (hpu y hyP)
  rw [hr] at hc
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q x)
    (eichler_mem_orthogonalGroup Q u y)

theorem eichler_mem_commutator_of_perp_le_span (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    (hspan : P.perp ≤ Submodule.span K {x | x ∈ P.perp ∧ Q x ≠ 0}) {u : V}
    (hpu : ∀ y ∈ P.perp, polar Q u y = 0) {x : V} (hx : x ∈ P.perp) :
    eichler Q u x ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hsub : Submodule.span K {x | x ∈ P.perp ∧ Q x ≠ 0} ≤ P.perp :=
    Submodule.span_le.mpr fun y hy => hy.1
  have key : ∀ y ∈ Submodule.span K {x | x ∈ P.perp ∧ Q x ≠ 0}, ∀ a : K,
      eichler Q u (a • y) ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      intro a
      by_cases ha : a = 0
      · rw [ha, zero_smul, eichler_zero_right]
        exact Subgroup.one_mem _
      · exact eichler_mem_commutator_of_anisotropic hQ P hpu (P.perp.smul_mem a hy.1)
          (by rw [map_smul_eq_sq]; exact mul_ne_zero (pow_ne_zero 2 ha) hy.2)
    | zero =>
      intro a
      rw [smul_zero, eichler_zero_right]
      exact Subgroup.one_mem _
    | add y z hy hz ihy ihz =>
      intro a
      rw [smul_add, ← eichler_mul (hpu _ (P.perp.smul_mem a (hsub hy)))
        (hpu _ (P.perp.smul_mem a (hsub hz)))]
      exact Subgroup.mul_mem _ (ihy a) (ihz a)
    | smul b y hy ihy =>
      intro a
      rw [smul_smul]
      exact ihy (a * b)
  have := key x (hspan hx) 1
  rwa [one_smul] at this

theorem elementaryGroup_le_commutator_of_perp_le_span (hQ : (polarBilin Q).Nondegenerate)
    (P : HypPair Q) (hspan : P.perp ≤ Submodule.span K {x | x ∈ P.perp ∧ Q x ≠ 0}) :
    elementaryGroup Q ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [← rootGroup_sup_eq_elementaryGroup hQ P.Q_e P.Q_f (by rw [P.polar_ef]; exact one_ne_zero)]
  refine sup_le ?_ ?_
  · intro g hg
    obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
    have hwe : polar Q w P.e = 0 := by rw [polar_comm]; exact hw
    have hdec : w = P.proj w + polar Q w P.f • P.e := by
      conv_lhs => rw [P.eq_add_proj w, hwe, zero_smul, add_zero, add_comm]
    rw [hdec, eichler_add_smul_self P.Q_e]
    exact eichler_mem_commutator_of_perp_le_span hQ P hspan
      (fun y hy => (HypPair.mem_perp.mp hy).1) (P.proj_mem_perp w)
  · intro g hg
    obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
    have hwf : polar Q w P.f = 0 := by rw [polar_comm]; exact hw
    have hdec : w = P.proj w + polar Q w P.e • P.f := by
      conv_lhs => rw [P.eq_add_proj w, hwf, zero_smul, zero_add]
      abel
    rw [hdec, eichler_add_smul_self P.Q_f]
    exact eichler_mem_commutator_of_perp_le_span hQ P hspan
      (fun y hy => (HypPair.mem_perp.mp hy).2) (P.proj_mem_perp w)

theorem eichler_ne_one_of_anisotropic (P : HypPair Q) {x : V} (hx : x ∈ P.perp) (hQx : Q x ≠ 0) :
    eichler Q P.e x ≠ 1 := by
  intro h
  have hEf : eichler Q P.e x P.f = P.f + x - Q x • P.e := by
    rw [eichler_apply P.Q_e (HypPair.mem_perp.mp hx).1 P.f, P.polar_fe,
      (HypPair.mem_perp.mp hx).2]
    module
  rw [h] at hEf
  have hx' : x = Q x • P.e := by
    have h1 : P.f = P.f + x - Q x • P.e := hEf
    linear_combination (norm := module) (-1 : K) • h1
  have h2 := congrArg (fun z => polar Q P.f z) hx'
  simp only [polar_smul_right_eq, P.polar_fe, mul_one] at h2
  exact hQx (by rw [← h2]; exact (HypPair.mem_perp.mp hx).2)

theorem commutator_orthogonalGroup_eq_elementaryGroup_of_isSimpleGroup
    (hle : elementaryGroup Q ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hne : elementaryGroup Q ≠ ⊥)
    (hsimple : IsSimpleGroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q := by
  have hnormal : ((elementaryGroup Q).subgroupOf
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h k hh hk
    exact conj_mem_elementaryGroup (Subgroup.commutator_le_self _ hk) hh
  refine le_antisymm ?_ hle
  rcases hsimple.eq_bot_or_eq_top_of_normal ((elementaryGroup Q).subgroupOf
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) with h | h
  · exact absurd (Disjoint.eq_bot_of_le (Subgroup.subgroupOf_eq_bot.mp h) hle) hne
  · exact Subgroup.subgroupOf_eq_top.mp h

end Derived

section Minus

variable {K : Type} [Field K] {b c : K}

theorem quadMinus_single_u {m : ℕ} :
    quadMinus m K b c (Pi.single (Sum.inr (Sum.inr 0)) 1) = 1 := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

theorem quadMinus_single_v {m : ℕ} :
    quadMinus m K b c (Pi.single (Sum.inr (Sum.inr 1)) 1) = c := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

private theorem mem_perp_coordinate_iff {m : ℕ} {i0 : Fin (m - 1)}
    (P : HypPair (quadMinus m K b c)) (hPe : P.e = Pi.single (Sum.inl i0) 1)
    (hPf : P.f = Pi.single (Sum.inr (Sum.inl i0)) 1)
    (w : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    w ∈ P.perp ↔ w (Sum.inr (Sum.inl i0)) = 0 ∧ w (Sum.inl i0) = 0 := by
  rw [HypPair.mem_perp, hPe, hPf, polar_single_inl_quadMinus, polar_single_inr_quadMinus]

theorem single_inr_inr_mem_perp {m : ℕ} {i0 : Fin (m - 1)} (P : HypPair (quadMinus m K b c))
    (hPe : P.e = Pi.single (Sum.inl i0) 1) (hPf : P.f = Pi.single (Sum.inr (Sum.inl i0)) 1)
    (j : Fin 2) :
    (Pi.single (Sum.inr (Sum.inr j)) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈ P.perp := by
  rw [mem_perp_coordinate_iff P hPe hPf]
  simp [Pi.single_apply]

theorem perp_le_span_quadMinus {m : ℕ} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i0 : Fin (m - 1)} (P : HypPair (quadMinus m K b c)) (hPe : P.e = Pi.single (Sum.inl i0) 1)
    (hPf : P.f = Pi.single (Sum.inr (Sum.inl i0)) 1) :
    P.perp ≤ Submodule.span K {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} := by
  have hmem := mem_perp_coordinate_iff P hPe hPf
  have hc0 : c ≠ 0 := by simpa using hirr 0
  set x₁ : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inr 0)) 1 with hx₁
  set x₂ : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inr 1)) 1 with hx₂
  have hQx₁ : quadMinus m K b c x₁ = 1 := quadMinus_single_u
  have hQx₂ : quadMinus m K b c x₂ = c := quadMinus_single_v
  have hx₁P : x₁ ∈ P.perp := single_inr_inr_mem_perp P hPe hPf 0
  have hx₂P : x₂ ∈ P.perp := single_inr_inr_mem_perp P hPe hPf 1
  have hS₁ : x₁ ∈ {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} :=
    ⟨hx₁P, by rw [hQx₁]; exact one_ne_zero⟩
  have hS₂ : x₂ ∈ {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} :=
    ⟨hx₂P, by rw [hQx₂]; exact hc0⟩
  have hspan_of : ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K, v ∈ P.perp →
      quadMinus m K b c v = 0 → polar (quadMinus m K b c) v x₁ = 0 →
        v ∈ Submodule.span K {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} := by
    intro v hv hQv hvx
    have hsum : v + x₁ ∈ {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} := by
      refine ⟨P.perp.add_mem hv hx₁P, ?_⟩
      rw [QuadraticMap.map_add (quadMinus m K b c) v x₁, hQv, hQx₁, hvx]
      norm_num
    have h : v + x₁ - x₁ ∈ Submodule.span K {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} :=
      Submodule.sub_mem _ (Submodule.subset_span hsum) (Submodule.subset_span hS₁)
    simpa using h
  have hinr : ∀ j : Fin 2, (Pi.single (Sum.inr (Sum.inr j)) (1 : K) :
      Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈
        Submodule.span K {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} :=
    Fin.forall_fin_two.mpr ⟨Submodule.subset_span hS₁, Submodule.subset_span hS₂⟩
  have hbasis : ∀ k : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2, k ≠ Sum.inl i0 →
      k ≠ Sum.inr (Sum.inl i0) →
      (Pi.single k (1 : K) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈
        Submodule.span K {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} := by
    intro k hk1 hk2
    rcases k with i | i | j
    · have hi : i ≠ i0 := fun h => hk1 (congrArg Sum.inl h)
      have hmemi : (Pi.single (Sum.inl i) (1 : K) :
          Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈ P.perp :=
        (hmem _).mpr ⟨by simp [Pi.single_apply], by simp [Pi.single_apply, Ne.symm hi]⟩
      have hpol : polar (quadMinus m K b c) (Pi.single (Sum.inl i) (1 : K)) x₁ = 0 := by
        rw [polar_single_inl_quadMinus, hx₁]
        simp [Pi.single_apply]
      exact hspan_of _ hmemi (quadMinus_single_inl i) hpol
    · have hi : i ≠ i0 := fun h => hk2 (congrArg Sum.inr (congrArg Sum.inl h))
      have hmemi : (Pi.single (Sum.inr (Sum.inl i)) (1 : K) :
          Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈ P.perp :=
        (hmem _).mpr ⟨by simp [Pi.single_apply, Ne.symm hi], by simp [Pi.single_apply]⟩
      have hpol : polar (quadMinus m K b c) (Pi.single (Sum.inr (Sum.inl i)) (1 : K)) x₁ = 0 := by
        rw [polar_single_inr_quadMinus, hx₁]
        simp [Pi.single_apply]
      exact hspan_of _ hmemi (quadMinus_single_inr i) hpol
    · exact hinr j
  intro w hw
  have hw' := (hmem w).mp hw
  have hdec : w = ∑ k, Pi.single k (w k) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hdec]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk0 : k = Sum.inl i0 ∨ k = Sum.inr (Sum.inl i0)
  · have hwk : w k = 0 := by
      rcases hk0 with rfl | rfl
      · exact hw'.2
      · exact hw'.1
    rw [hwk]
    simp
  · have hsc : (Pi.single k (w k) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) =
        w k • (Pi.single k (1 : K) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      funext j
      simp [Pi.single_apply]
    rw [hsc]
    exact Submodule.smul_mem _ _
      (hbasis k (fun h => hk0 (Or.inl h)) (fun h => hk0 (Or.inr h)))

theorem elementaryGroup_quadMinus_le_commutator [Finite K] {m : ℕ} (hm : 2 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    elementaryGroup (quadMinus m K b c) ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c)⁆ :=
  elementaryGroup_le_commutator_of_perp_le_span
    (nondegenerate_polarBilin_quadMinus_of_finite m K hirr)
    (minusPair K b c (⟨0, by omega⟩ : Fin (m - 1))) (perp_le_span_quadMinus hirr _ rfl rfl)

theorem elementaryGroup_quadMinus_ne_bot {m : ℕ} (hm : 2 ≤ m) :
    elementaryGroup (quadMinus m K b c) ≠ ⊥ := by
  intro h
  obtain ⟨i0⟩ : Nonempty (Fin (m - 1)) := ⟨⟨0, by omega⟩⟩
  refine eichler_ne_one_of_anisotropic (minusPair K b c i0)
    (single_inr_inr_mem_perp _ rfl rfl 0) (x := Pi.single (Sum.inr (Sum.inr 0)) 1)
    (by rw [quadMinus_single_u]; exact one_ne_zero) ?_
  have := eichler_mem_elementaryGroup (quadMinus m K b c) (minusPair K b c i0).e
    (Pi.single (Sum.inr (Sum.inr 0)) 1)
  rwa [h, Subgroup.mem_bot] at this

end Minus

section MinusSmall

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {b c : K}

theorem commutator_orthogonalGroup_quadMinus_small (hn : n = 2 ∨ n = 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆ =
        elementaryGroup (quadMinus n K b c) := by
  have hn2 : 2 ≤ n := by omega
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have hdim : Module.finrank K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have hmin := isMinus_quadMinus (by omega : 1 ≤ n) hirr
  obtain ⟨hsimple, -⟩ := CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
    (quadMinus n K b c) hQ (by omega) fun U hU => hmin.noTS U (by rw [hdim] at hU; omega)
  exact commutator_orthogonalGroup_eq_elementaryGroup_of_isSimpleGroup
    (elementaryGroup_quadMinus_le_commutator hn2 hirr) (elementaryGroup_quadMinus_ne_bot hn2)
    hsimple

theorem commutator_orthogonalGroup_quadMinus_of_two_le (hn : 2 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆ =
        elementaryGroup (quadMinus n K b c) := by
  rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with h | h | h
  · exact commutator_orthogonalGroup_quadMinus_small (Or.inl h) hirr
  · exact commutator_orthogonalGroup_quadMinus_small (Or.inr h) hirr
  · exact commutator_orthogonalGroup_quadMinus h hirr

theorem statedOmega_quadMinus_eq_map_of_two_le (hn : 2 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    StatedOmega (StatedQuadMinus n K b c) =
      (elementaryGroup (quadMinus n K b c)).map
        (toLinEquiv (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).symm.toMonoidHom :=
  statedOmega_eq_map_elementaryGroup (coe_quadMinus n K b c)
    (commutator_orthogonalGroup_quadMinus_of_two_le hn hirr)

end MinusSmall

section Equiv

variable {K : Type} [Field K]

@[expose] noncomputable def statedOmegaPlusEquiv {m : ℕ} (hm : 3 ≤ m) :
    StatedOmega (StatedQuadPlus m K) ≃* Gom (quadPlus m K) :=
  statedOmegaEquiv (coe_quadPlus m K) (commutator_orthogonalGroup_quadPlus hm)

theorem statedOmegaPlusEquiv_app {m : ℕ} (hm : 3 ≤ m) (A : StatedOmega (StatedQuadPlus m K))
    (v : Fin m ⊕ Fin m → K) :
    (statedOmegaPlusEquiv hm A).app v = (A : GL (Fin m ⊕ Fin m) K).val *ᵥ v := by
  unfold Gom.app statedOmegaPlusEquiv
  rw [coe_statedOmegaEquiv, toLinEquiv_apply]

theorem statedOmegaPlusEquiv_symm_app {m : ℕ} (hm : 3 ≤ m) (g : Gom (quadPlus m K))
    (v : Fin m ⊕ Fin m → K) :
    ((statedOmegaPlusEquiv hm).symm g : GL (Fin m ⊕ Fin m) K).val *ᵥ v = g.app v := by
  rw [← statedOmegaPlusEquiv_app hm, MulEquiv.apply_symm_apply]

variable [Finite K] [CharP K 2] {m : ℕ} {b c : K}

@[expose] noncomputable def statedOmegaMinusEquiv (hm : 2 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    StatedOmega (StatedQuadMinus m K b c) ≃* Gom (quadMinus m K b c) :=
  statedOmegaEquiv (coe_quadMinus m K b c) (commutator_orthogonalGroup_quadMinus_of_two_le hm hirr)

theorem statedOmegaMinusEquiv_app (hm : 2 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (A : StatedOmega (StatedQuadMinus m K b c)) (v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    (statedOmegaMinusEquiv hm hirr A).app v =
      (A : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).val *ᵥ v := by
  unfold Gom.app statedOmegaMinusEquiv
  rw [coe_statedOmegaEquiv, toLinEquiv_apply]

theorem statedOmegaMinusEquiv_symm_app (hm : 2 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (g : Gom (quadMinus m K b c)) (v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    ((statedOmegaMinusEquiv hm hirr).symm g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).val *ᵥ
      v = g.app v := by
  rw [← statedOmegaMinusEquiv_app hm hirr, MulEquiv.apply_symm_apply]

end Equiv

section Flag

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_apply_sub_eq_zero {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {u : V} (hgu : g u = u) (x : V) : polar Q u (g x - x) = 0 := by
  have h := polar_map_of_mem hg u x
  rw [hgu] at h
  rw [polar_sub_right, h, sub_self]

theorem mem_rootGroup_iff_flag (hQ : (polarBilin Q).Nondegenerate) {u : V} (hu : Q u = 0)
    (hu0 : u ≠ 0) {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    g ∈ rootGroup Q u ↔ g u = u ∧ (∀ x, polar Q u x = 0 → ∃ c : K, g x - x = c • u) ∧
      ∀ x, polar Q u (g x - x) = 0 := by
  rw [mem_rootGroup_iff hQ hu hu0]
  constructor
  · rintro ⟨-, hgu, hperp⟩
    exact ⟨hgu, fun x hx => hperp x (by rw [polar_comm]; exact hx), polar_apply_sub_eq_zero hg hgu⟩
  · rintro ⟨hgu, hperp, -⟩
    exact ⟨hg, hgu, fun x hx => hperp x (by rw [polar_comm]; exact hx)⟩

theorem mem_Lom_iff_flag (hQ : (polarBilin Q).Nondegenerate) {u : V} (hu : Q u = 0) (hu0 : u ≠ 0)
    (g : Gom Q) :
    g ∈ Lom Q u ↔ g.app u = u ∧ (∀ x, polar Q u x = 0 → ∃ c : K, g.app x - x = c • u) ∧
      ∀ x, polar Q u (g.app x - x) = 0 :=
  mem_rootGroup_iff_flag hQ hu hu0 (elementaryGroup_le_orthogonalGroup Q g.2)

end Flag

section MatrixRoot

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def rootGroupGL (Q : QuadraticForm K (ι → K)) (u : ι → K) :
    Subgroup (GL ι K) :=
  (rootGroup Q u).comap (toLinEquiv ι K).toMonoidHom

theorem mem_rootGroupGL_iff {Q : QuadraticForm K (ι → K)} (hQ : (polarBilin Q).Nondegenerate)
    {u : ι → K} (hu : Q u = 0) (hu0 : u ≠ 0) {A : GL ι K} :
    A ∈ rootGroupGL Q u ↔ (∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v) ∧ (A : Matrix ι ι K) *ᵥ u = u ∧
      (∀ x, polar Q u x = 0 → ∃ c : K, (A : Matrix ι ι K) *ᵥ x - x = c • u) ∧
      ∀ x, polar Q u ((A : Matrix ι ι K) *ᵥ x - x) = 0 := by
  rw [rootGroupGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h
    have hO := ((mem_rootGroup_iff hQ hu hu0).mp h).1
    exact ⟨fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hO v,
      (mem_rootGroup_iff_flag hQ hu hu0 hO).mp h⟩
  · rintro ⟨hiso, hrest⟩
    exact (mem_rootGroup_iff_flag hQ hu hu0
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso)).mpr hrest

section LomGL

variable {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

@[expose] noncomputable def LomGL (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (u : ι → K) : Subgroup (GL ι K) :=
  ((Lom Q u).map (statedOmegaEquiv hQ hE).symm.toMonoidHom).map (StatedOmega Q₀).subtype

theorem mem_statedOmega_iff_mem_elementaryGroup (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {A : GL ι K} :
    A ∈ StatedOmega Q₀ ↔ toLinEquiv ι K A ∈ elementaryGroup Q := by
  rw [statedOmega_eq_comap hQ, hE, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]

theorem LomGL_eq_rootGroupGL (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (u : ι → K) : LomGL hQ hE u = rootGroupGL Q u := by
  ext A
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    have h1 := coe_statedOmegaEquiv hQ hE ((statedOmegaEquiv hQ hE).symm g)
    rw [MulEquiv.apply_symm_apply] at h1
    show toLinEquiv ι K (((statedOmegaEquiv hQ hE).symm g : StatedOmega Q₀) : GL ι K) ∈
      rootGroup Q u
    rw [← h1]
    exact hg
  · intro hA
    have hA' : toLinEquiv ι K A ∈ rootGroup Q u := hA
    have hAE : A ∈ StatedOmega Q₀ :=
      (mem_statedOmega_iff_mem_elementaryGroup hQ hE).mpr (rootGroup_le_elementaryGroup Q u hA')
    refine ⟨⟨A, hAE⟩, ⟨statedOmegaEquiv hQ hE ⟨A, hAE⟩, ?_, ?_⟩, rfl⟩
    · exact mem_Lom.mpr (by rw [coe_statedOmegaEquiv]; exact hA')
    · simp

theorem mem_LomGL_iff (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hnd : (polarBilin Q).Nondegenerate) {u : ι → K} (hu : Q u = 0)
    (hu0 : u ≠ 0) {A : GL ι K} :
    A ∈ LomGL hQ hE u ↔ A ∈ StatedOmega Q₀ ∧ (A : Matrix ι ι K) *ᵥ u = u ∧
      (∀ x, polar Q u x = 0 → ∃ c : K, (A : Matrix ι ι K) *ᵥ x - x = c • u) ∧
      ∀ x, polar Q u ((A : Matrix ι ι K) *ᵥ x - x) = 0 := by
  rw [LomGL_eq_rootGroupGL]
  constructor
  · intro h
    have hA : A ∈ StatedOmega Q₀ :=
      (mem_statedOmega_iff_mem_elementaryGroup hQ hE).mpr (rootGroup_le_elementaryGroup Q u h)
    exact ⟨hA, ((mem_rootGroupGL_iff hnd hu hu0).mp h).2⟩
  · rintro ⟨hA, hrest⟩
    refine (mem_rootGroupGL_iff hnd hu hu0).mpr ⟨fun v => ?_, hrest⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (elementaryGroup_le_orthogonalGroup Q
        ((mem_statedOmega_iff_mem_elementaryGroup hQ hE).mp hA)) v

end LomGL

end MatrixRoot

section Models

variable {K : Type} [Field K]

@[expose] noncomputable def LomGLPlus {m : ℕ} (hm : 3 ≤ m) (u : Fin m ⊕ Fin m → K) :
    Subgroup (GL (Fin m ⊕ Fin m) K) :=
  ((Lom (quadPlus m K) u).map (statedOmegaPlusEquiv hm).symm.toMonoidHom).map
    (StatedOmega (StatedQuadPlus m K)).subtype

theorem mem_LomGLPlus_iff {m : ℕ} (hm : 3 ≤ m) {u : Fin m ⊕ Fin m → K}
    (hu : quadPlus m K u = 0) (hu0 : u ≠ 0) {A : GL (Fin m ⊕ Fin m) K} :
    A ∈ LomGLPlus hm u ↔ A ∈ StatedOmega (StatedQuadPlus m K) ∧
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u ∧
      (∀ x, polar (quadPlus m K) u x = 0 →
        ∃ c : K, (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x - x = c • u) ∧
      ∀ x, polar (quadPlus m K) u ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x - x) = 0 :=
  mem_LomGL_iff (coe_quadPlus m K) (commutator_orthogonalGroup_quadPlus hm)
    (nondegenerate_polarBilin_quadPlus m K) hu hu0

variable [Finite K] [CharP K 2] {m : ℕ} {b c : K}

@[expose] noncomputable def LomGLMinus (hm : 2 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (u : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :=
  ((Lom (quadMinus m K b c) u).map (statedOmegaMinusEquiv hm hirr).symm.toMonoidHom).map
    (StatedOmega (StatedQuadMinus m K b c)).subtype

end Models

end CFSG.ClassicalGroups.Orthogonal
