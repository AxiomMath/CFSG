module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthMain

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Module QuadraticMap CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCOrthogonal

theorem PerfectNoncycThreeIn.subgroupOf_commutator {G : Type*} [Group G] {C O : Subgroup G}
    (h : PerfectNoncycThreeIn C) (hCO : C ≤ O) : PerfectNoncycThreeIn (C.subgroupOf ⁅O, O⁆) := by
  obtain ⟨V, hVC, hV, Q, hQV, hQ, hnc⟩ := h
  have hVD : V ≤ ⁅O, O⁆ := hV ▸ Subgroup.commutator_mono (hVC.trans hCO) (hVC.trans hCO)
  have hQD := hQV.trans hVD
  refine ⟨V.subgroupOf ⁅O, O⁆, Subgroup.subgroupOf_mono _ hVC, commutator_subgroupOf_of_le hVD hV,
    Q.subgroupOf ⁅O, O⁆, Subgroup.subgroupOf_mono _ hQV,
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQD).symm, fun hc => hnc ?_⟩
  have e := Subgroup.subgroupOfEquivOfLe hQD
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

section Derived

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem centNoncycThreeGroup_orthDerived (hQ : (polarBilin Q).Nondegenerate) {r : ℕ}
    (hdim : finrank K V = 2 * r) (hr : (4 ≤ Nat.card K ∧ 4 ≤ r) ∨ (Nat.card K = 2 ∧ 6 ≤ r)) :
    CentNoncycThreeGroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  intro a ha3 ha1
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    norm_num
  have hx : OddOrderIsometry Q 3 (a : V ≃ₗ[K] V) :=
    ⟨Subgroup.commutator_le_self _ a.2, by rw [← Subgroup.coe_pow, ha3, Subgroup.coe_one], h3K,
      fun v hv => hQ.1 v hv⟩
  refine ((perfectNoncycThreeIn_isometryCentralizer hx hdim hr).subgroupOf_commutator
    inf_le_left).mono fun y hy => ?_
  rw [Subgroup.mem_subgroupOf, mem_isometryCentralizer] at hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (LinearEquiv.ext fun v => hy.2 v)

end Derived

section Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem exists_quadratic_ne_zero {W : Type*} [AddCommGroup W] [Module K W] [Nontrivial W]
    {Q : QuadraticForm K W} (hQ : (polarBilin Q).Nondegenerate) : ∃ v, Q v ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  exact hv (hQ.1 v fun w => by
    rw [polarBilin_apply_apply, QuadraticMap.polar, h, h, h, sub_zero, sub_zero])

theorem statedScalars_subgroupOf_statedOmega [Nonempty ι] {Q : QuadraticForm K (ι → K)}
    {Q₀ : (ι → K) → K} (hQ0 : ⇑Q = Q₀) (hQ : (polarBilin Q).Nondegenerate) :
    (StatedScalars ι K).subgroupOf (StatedOmega Q₀) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  have hgO : CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K (g : GL ι K) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _
      (Subgroup.mem_comap.mp ((CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ0).le g.2))
  obtain ⟨v, hv⟩ := exists_quadratic_ne_zero hQ
  have hcv := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO v
  rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, ← hc,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at hcv
  have hsmul : Matrix.mulVec (Matrix.diagonal fun _ => (c : K)) v = (c : K) • v := by
    funext i
    simp [Matrix.mulVec_diagonal]
  rw [hsmul, QuadraticMap.map_smul, smul_eq_mul] at hcv
  have hc2 : (c : K) * c = 1 := by
    have h1 : ((c : K) * c - 1) * Q v = 0 := by rw [sub_mul, hcv, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hv)
  have hc1 : (c : K) = 1 := by
    have h2 := sub_pow_char (p := 2) (c : K) 1
    rw [_root_.sq (c : K), hc2, one_pow, sub_self] at h2
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h2)
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by rw [OneMemClass.coe_one, ← hc, show c = 1 from Units.ext hc1, map_one])

@[expose] noncomputable def statedProjOmegaEquivDerivedCharTwo [Nonempty ι]
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ0 : ⇑Q = Q₀)
    (hQ : (polarBilin Q).Nondegenerate) :
    StatedProj (StatedOmega Q₀) ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  ((QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedOmega hQ0 hQ)).trans
    QuotientGroup.quotientBot).trans
    (((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans
      (MulEquiv.subgroupCongr (by
        rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ0]
        exact Subgroup.map_comap_eq_self_of_surjective
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective _)))

end Matrix

open CFSG.LieType.Universal.Spin in
theorem centNoncycThreeGroup_of_model_pomegaPlus {X : Type} [Group X] {r f : ℕ}
    (h : StatedClassicalModel X .POmegaPlus r 2 f) (hr : (2 ≤ f ∧ 4 ≤ r) ∨ (f = 1 ∧ 6 ≤ r)) :
    CentNoncycThreeGroup X := by
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have : Nonempty (Fin r ⊕ Fin r) := ⟨.inl ⟨0, by omega⟩⟩
  have hdim : finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]
  refine (centNoncycThreeGroup_orthDerived (nondegenerate_polarBilin_quadPlus r K) hdim
    ?_).of_mulEquiv (e.trans (statedProjOmegaEquivDerivedCharTwo (coe_quadPlus r K)
      (nondegenerate_polarBilin_quadPlus r K)))
  rcases hr with ⟨hf, hr⟩ | ⟨rfl, hr⟩
  · refine Or.inl ⟨?_, hr⟩
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  · exact Or.inr ⟨by rw [hK, pow_one], hr⟩

open CFSG.LieType.Universal.Spin in
theorem centNoncycThreeGroup_of_model_pomegaMinus {X : Type} [Group X] {r f : ℕ}
    (h : StatedClassicalModel X .POmegaMinus r 2 f) (hr : (2 ≤ f ∧ 4 ≤ r) ∨ (f = 1 ∧ 6 ≤ r)) :
    CentNoncycThreeGroup X := by
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := h
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have : Nonempty (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) := ⟨.inr (.inr 0)⟩
  have hdim : finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  refine (centNoncycThreeGroup_orthDerived (nondegenerate_polarBilin_quadMinus_of_finite r K hbc)
    hdim ?_).of_mulEquiv (e.trans (statedProjOmegaEquivDerivedCharTwo (coe_quadMinus r K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite r K hbc)))
  rcases hr with ⟨hf, hr⟩ | ⟨rfl, hr⟩
  · refine Or.inl ⟨?_, hr⟩
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  · exact Or.inr ⟨by rw [hK, pow_one], hr⟩

end CFSG.AGLEmbedding.ToralCensus
