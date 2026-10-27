module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusPlane
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourExtract
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixExtract
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockThreeFivesGroup

public section

namespace CFSG.AGLEmbedding.LeviBlock

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank

section Transport

variable {K : Type*} [Field K] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}

theorem orthMinus_map_autCongr_orthogonalGroup (e : Q₁.IsometryEquiv Q₂) :
    (TauCeti.QuadraticMap.orthogonalGroup Q₁).map
      (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom =
        TauCeti.QuadraticMap.orthogonalGroup Q₂ := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun m => ?_
    rw [MulEquiv.coe_toMonoidHom, LinearEquiv.autCongr_apply_apply]
    erw [e.map_app, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hf, ← e.map_app,
      e.apply_symm_apply]
  · intro hg
    refine ⟨(LinearEquiv.autCongr e.toLinearEquiv).symm g,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun m => ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [LinearEquiv.autCongr_symm_apply_apply]
    erw [← e.map_app, e.apply_symm_apply, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg,
      e.map_app]

theorem orthMinus_map_autCongr_commutator (e : Q₁.IsometryEquiv Q₂) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q₁, TauCeti.QuadraticMap.orthogonalGroup Q₁⁆.map
      (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom =
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q₂, TauCeti.QuadraticMap.orthogonalGroup Q₂⁆ := by
  rw [Subgroup.map_commutator, orthMinus_map_autCongr_orthogonalGroup]

@[expose] noncomputable def orthMinusCommutatorCongr (e : Q₁.IsometryEquiv Q₂) :
    ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₁, TauCeti.QuadraticMap.orthogonalGroup Q₁⁆ ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₂, TauCeti.QuadraticMap.orthogonalGroup Q₂⁆ :=
  ((LinearEquiv.autCongr e.toLinearEquiv).subgroupMap _).trans
    (MulEquiv.subgroupCongr (orthMinus_map_autCongr_commutator e))

end Transport

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

omit [CharP K 2] in
theorem commutator_orthogonalGroup_quadTail_minus {r : ℕ} (hr : 3 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c)),
      TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c))⁆ =
        orthElementaryGroup (quadTail r (minusTailForm K b c)) := by
  let ψ : (quadTail r (minusTailForm K b c)).IsometryEquiv (quadMinus (r + 1) K b c) :=
    minusTailIsometry (r + 1) K b c
  apply Subgroup.map_injective (f := (LinearEquiv.autCongr ψ.toLinearEquiv).toMonoidHom)
    (LinearEquiv.autCongr ψ.toLinearEquiv).injective
  rw [orthMinus_map_autCongr_commutator ψ,
    commutator_orthogonalGroup_quadMinus (by omega) hirr]
  exact (CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.elementaryGroup_map ψ).symm

variable (K b c) in
noncomputable abbrev orthResDer (m : ℕ) :
    Subgroup (((Fin m ⊕ Fin m → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin m ⊕ Fin m → K) × (Fin 2 → K))) :=
  ⁅TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)),
    TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))⁆

omit [Finite K] [CharP K 2] in
theorem minusTail_zero_apply (v : (Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K)) :
    quadTail 0 (minusTailForm K b c) v = minusTailForm K b c v.2 := by
  rw [quadTail_apply, quadPlus_apply]
  simp

@[expose] noncomputable def minusTailZeroIsometry :
    (quadTail 0 (minusTailForm K b c)).IsometryEquiv (minusTailForm K b c) :=
  { (LinearEquiv.uniqueProd : ((Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K)) ≃ₗ[K] (Fin 2 → K)) with
    map_app' := fun v => (minusTail_zero_apply v).symm }

theorem isSolvable_orthResDer_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Group.IsSolvable ↥(orthResDer K b c 0) := by
  set e := orthMinusCommutatorCongr (minusTailZeroIsometry (b := b) (c := c))
  refine Group.isSolvable_of_comm fun x y => e.injective ?_
  rw [map_mul, map_mul]
  exact Subtype.ext (commute_of_mem_commutator_minusTailForm hirr (e x).2 (e y).2)

@[expose] noncomputable def orthResDerEquivStatedOmega (m : ℕ) :
    ↥(orthResDer K b c m) ≃* ↥(StatedOmega (StatedQuadMinus (m + 1) K b c)) :=
  (orthMinusCommutatorCongr (minusTailIsometry (m + 1) K b c :
      (quadTail m (minusTailForm K b c)).IsometryEquiv (quadMinus (m + 1) K b c))).trans
    (((toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) K).subgroupMap
      (StatedOmega (StatedQuadMinus (m + 1) K b c))).trans
        (MulEquiv.subgroupCongr (by
          rw [statedOmega_eq_comap (coe_quadMinus (m + 1) K b c)]
          exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv _ K).surjective _))).symm

@[expose] noncomputable def orthMinusStatedProjEquiv {n : ℕ} (hn : 2 ≤ n) :
    StatedProj (StatedOmega (StatedQuadMinus n K b c)) ≃* StatedOmega (StatedQuadMinus n K b c) :=
  (QuotientGroup.quotientMulEquivOfEq
    (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (coe_quadMinus n K b c) ⟨(minusPair K b c ⟨0, by omega⟩).e +
        (minusPair K b c ⟨0, by omega⟩).f, by
        rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair]
        exact one_ne_zero⟩)).trans QuotientGroup.quotientBot

theorem orthResDer_facts_of_three_le {f m : ℕ} (hK : Nat.card K = 2 ^ f) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsSimpleGroup ↥(orthResDer K b c m) ∧
      Nat.card ↥(orthResDer K b c m) = CFSG.Open.ordTwistedD (m + 1) (2 ^ f) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact h
  set e := (orthResDerEquivStatedOmega (b := b) (c := c) m).trans
    (orthMinusStatedProjEquiv (b := b) (c := c) (n := m + 1) (by omega)).symm
  have hs := isSimpleGroup_statedProj_statedOmega_quadMinus (n := m + 1) (by omega) hirr
  refine ⟨(MulEquiv.isSimpleGroup_congr e).2 hs, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact (CFSG.Timmesfeld.card_statedClassicalModel_two (G := StatedProj (StatedOmega
    (StatedQuadMinus (m + 1) K b c))) (t := .POmegaMinus) (n := m + 1)
      ⟨⟨Nat.prime_two, hf, by omega⟩, K, inferInstance,
      inferInstance, hK, b, c, hirr, ⟨MulEquiv.refl _⟩⟩).2.2.2.2 rfl

omit [Finite K] [CharP K 2] in
theorem exists_minusTail_ne_zero {m : ℕ} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (U : Submodule K ((Fin m ⊕ Fin m → K) × (Fin 2 → K))) (hU : Module.finrank K U = m + 1) :
    ∃ u ∈ U, quadTail m (minusTailForm K b c) u ≠ 0 := by
  by_contra h
  push Not at h
  have := finrank_le_of_totSing_tail (anisotropic_minusTailForm hirr) h
  omega

theorem orthResDer_one_facts (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsSimpleGroup ↥(orthResDer K b c 1) ∧ (∃ x y : ↥(orthResDer K b c 1), x * y ≠ y * x) ∧
      Nat.card ↥(orthResDer K b c 1) = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hs, -, hna, hcard, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction
      (quadTail 1 (minusTailForm K b c))
      (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr))
      (by rw [finrank_tailSpace, finrank_fin_two_fun]) (exists_minusTail_ne_zero hirr)
  rw [orthResDer, hcomm]
  push Not at hna
  exact ⟨hs, hna, hcard⟩

theorem orthResDer_two_facts (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsSimpleGroup ↥(orthResDer K b c 2) ∧ (∃ x y : ↥(orthResDer K b c 2), x * y ≠ y * x) ∧
      Nat.card ↥(orthResDer K b c 2) =
        Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) * (Nat.card K ^ 4 - 1) := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hs, -, hna, hcard, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction
      (quadTail 2 (minusTailForm K b c))
      (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr))
      (by rw [finrank_tailSpace, finrank_fin_two_fun]) (exists_minusTail_ne_zero hirr)
  rw [orthResDer, hcomm]
  push Not at hna
  exact ⟨hs, hna, hcard⟩

theorem orthMinus_ordTwistedD_two {f : ℕ} (hf : 1 ≤ f) :
    CFSG.Open.ordTwistedD 2 (2 ^ f) = (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) := by
  have hg := CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one
    (CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one hf (n := 2) (by norm_num))
  rw [CFSG.Open.ordTwistedD, hg, Nat.div_one, show Finset.Icc 1 (2 - 1) = {1} from rfl,
    Finset.prod_singleton]
  have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : 1 ≤ (2 ^ f) ^ 4 := Nat.one_le_pow _ _ (by positivity)
  zify [h1, h2]
  ring

theorem orthMinus_ordTwistedD_three {f : ℕ} (hf : 1 ≤ f) :
    CFSG.Open.ordTwistedD 3 (2 ^ f) =
      (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1) := by
  have hg := CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one
    (CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one hf (n := 3) (by norm_num))
  rw [CFSG.Open.ordTwistedD, hg, Nat.div_one, show Finset.Icc 1 (3 - 1) = {1, 2} from rfl,
    Finset.prod_pair (by norm_num)]
  ring

theorem orthResDer_facts {f m : ℕ} (hK : Nat.card K = 2 ^ f) (hm : 1 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsSimpleGroup ↥(orthResDer K b c m) ∧ (∃ x y : ↥(orthResDer K b c m), x * y ≠ y * x) ∧
      Nat.card ↥(orthResDer K b c m) = CFSG.Open.ordTwistedD (m + 1) (2 ^ f) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact h
  rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | h3
  · obtain ⟨hs, hna, hc⟩ := orthResDer_one_facts hirr
    exact ⟨hs, hna, by rw [hc, hK, orthMinus_ordTwistedD_two hf]⟩
  · obtain ⟨hs, hna, hc⟩ := orthResDer_two_facts hirr
    exact ⟨hs, hna, by rw [hc, hK, orthMinus_ordTwistedD_three hf]⟩
  · obtain ⟨hs, hc⟩ := orthResDer_facts_of_three_le hK h3 hirr
    refine ⟨hs, CFSG.AGLEmbedding.ThreeFives.exists_noncomm_of_simple hs ?_, hc⟩
    rw [hc, CFSG.Open.ordTwistedD, CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one
      (CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one hf (by omega)), Nat.div_one]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    rw [← pow_mul, Nat.add_sub_cancel]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ∣ 2 ^ (f * ((m + 1) * m)) := pow_dvd_pow 2
        ((show 2 ≤ (m + 1) * m by nlinarith).trans (Nat.le_mul_of_pos_left _ hf))

end CFSG.AGLEmbedding.LeviBlock
