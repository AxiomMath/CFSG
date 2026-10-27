module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkD4Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkTriD4
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutBase
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Field
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTriality

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

private theorem g2_of_layer_triD4 {X : Type} [Group X] {n f : ℕ}
    (h : OuterLayerThree .trialityD4 n f X) : CFSG.Blueprint.LieModel X .G2 0 3 f := by
  rcases h with ⟨t', n', f', hs, hm⟩ | ⟨h, -⟩
  · rcases hs with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, rfl, rfl, rfl⟩
    · exact absurd rfl h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact hm
  · exact absurd h (by decide)

private theorem pSimple_equiv_of_conj {P : Type} [Group P] [Finite P] {α ψ : MulAut P} {X : Type}
    [Group X] (e : ↥(fixSubgroup (ψ * α * ψ⁻¹)) ≃* X) (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) {A : Subgroup P}
    (hA : GLAPComponent 3 (fixSubgroup α) A) : Nonempty (PSimple 3 A ≃* X) := by
  have hc : MulAut.congr (ψ : P ≃* P) α = ψ * α * ψ⁻¹ := by
    ext x
    rfl
  let E : ↥(fixSubgroup α) ≃* X :=
    ((CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv (ψ : P ≃* P) α).trans
      (MulEquiv.subgroupCongr (by rw [hc]))).trans e
  haveI : IsSimpleGroup ↥(fixSubgroup α) := E.isSimpleGroup
  have hcomm : ⁅fixSubgroup α, fixSubgroup α⁆ ≤ fixSubgroup α := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  obtain ⟨a, b, hab⟩ := hnab
  obtain ⟨-, ⟨e'⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.I1431C2.psimple_equiv_of_simple_normal_comm
    le_rfl hcomm inferInstance
    ⟨E.symm a, E.symm b, fun h => hab (E.symm.injective (by simpa using h))⟩ hA
  exact ⟨e'.trans E⟩


section FieldTypes


private theorem fieldType_conj {K : Type} [Field K] [Finite K] [CharP K 3] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1)
    (hσ1 : σ ≠ 1) (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K 0)) :
    ∃ (d : ℕ) (T : K ≃+* K) (ψ : MulAut (adjointGroup Tag.D4 K)), d * 3 = f ∧
      (∀ c, T c = c ^ 3 ^ d) ∧ (ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.D4 T ∨
        ψ * α ^ 2 * ψ⁻¹ = entrywiseAdjointAut Tag.D4 T) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, T, hd0, hdf, hT, hT3, hσT⟩ :=
    exists_frobenius_of_cube Nat.prime_three hf K hK σ hσ3 hσ1
  rw [d4Graph_zero, mul_one] at hαeq
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases hσT with hσ | hσ
  · rw [hσ] at hαeq
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_entrywiseAdjointAut_D4 hK hK4 hd0 hdf T hT g a α hαeq hα3
    exact ⟨d, T, ψ, hdf, hT, Or.inl hψ⟩
  · obtain ⟨g', a', hα2⟩ := sq_conj_mul_exactNormalAut g a σ
    have hσ2 : σ ^ 2 = T := by
      rw [hσ, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hT3, one_mul]
    rw [hσ2, ← hαeq] at hα2
    have hα23 : (α ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hα3, one_pow]
    obtain ⟨ψ, hψ⟩ :=
      exists_conj_eq_entrywiseAdjointAut_D4 hK hK4 hd0 hdf T hT g' a' (α ^ 2) hα2 hα23
    exact ⟨d, T, ψ, hdf, hT, Or.inr hψ⟩

private theorem twisted_fixed_facts {K : Type} [Field K] [Finite K] [CharP K 3] {e : ℕ}
    (he : 1 ≤ e) (hK : Nat.card K = (3 ^ e) ^ 3) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (3 ^ e))
    (j : ℤ) (hj : j = 1 ∨ j = 2) :
    ∃ (X : Type) (_ : Group X),
      Nonempty (↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) ≃* X) ∧ IsSimpleGroup X ∧
        (∃ a b : X, a * b ≠ b * a) ∧ CFSG.Blueprint.LieModel X .trialityD4 0 3 e := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP (AlgebraicClosure K) 3 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 3
  obtain ⟨σ, r, hr, hσ, hfix⟩ : ∃ (σ : K ≃+* K) (r : ℕ), (r = 1 ∨ r = 2) ∧
      (∀ c, σ c = c ^ ((3 ^ e) ^ r)) ∧ fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T) =
        fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ) := by
    rcases hj with rfl | rfl
    · exact ⟨T, 1, Or.inl rfl, fun c => by rw [hT, pow_one], rfl⟩
    · have hT3 := ringEquiv_cube_apply_eq hK hT
      refine ⟨T⁻¹, 2, Or.inr rfl, fun c => ?_, fixedSubgroup_twistedEntrywiseAut_D4_two T⟩
      have h1 : T⁻¹ (T (T (T c))) = T (T c) := RingEquiv.symm_apply_apply T _
      rw [hT3] at h1
      rw [h1, hT, hT, ← pow_mul, sq]
  obtain ⟨-, -, htw, hs, hnab⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group
    3 e Nat.prime_three he K hK (AlgebraicClosure K) r hr σ.toRingHom hσ
    (iterateFrobenius (AlgebraicClosure K) 3 e) (fun c => iterateFrobenius_def _ _ _)
  refine ⟨↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), inferInstance,
    ⟨(MulEquiv.subgroupCongr hfix).trans ((fixedSubgroupTwistedEntrywiseAutOneEquiv TwistTag.D4
      σ).trans (MulEquiv.subgroupCongr htw))⟩, hs, hnab, ?_⟩
  refine CFSG.ComponentClassification.CatLeafProof.lieModel_graphFixedRootGroup_trialityD4_odd
    Nat.prime_three (by norm_num) he hK σ ?_
  rcases hr with rfl | rfl
  · exact Or.inl fun c => by rw [hσ, pow_one]
  · exact Or.inr hσ

private theorem graphFieldType_comp {K : Type} [Field K] [Finite K] [CharP K 3] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) (α : MulAut (adjointGroup Tag.D4 K))
    (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (ε : ℕ) (hε : ε < 3) (hε0 : ε ≠ 0) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))
    {A : Subgroup (adjointGroup Tag.D4 K)} (hA : GLAPComponent 3 (fixSubgroup α) A) :
    ∃ f', 3 * f' = f ∧ CFSG.Blueprint.LieModel (PSimple 3 A) .trialityD4 0 3 f' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  obtain ⟨e, T, he, hef, hT, hσT⟩ := exists_frobenius_eq_or_inv_of_orderOf_three Nat.prime_three
    hf K hK σ (orderOf_eq_prime hσ3 hσ1)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKe : Nat.card K = (3 ^ e) ^ 3 := by rw [hK, ← hef, pow_mul]
  have hε' : ε = 1 ∨ ε = 2 := by omega
  obtain ⟨β, j, hj, ψ, hψ, hAβ⟩ : ∃ (β : MulAut (adjointGroup Tag.D4 K)) (j : ℤ), (j = 1 ∨ j = 2) ∧
      ∃ ψ : MulAut (adjointGroup Tag.D4 K), ψ * β * ψ⁻¹ = twistedEntrywiseAut TwistTag.D4 j T ∧
        GLAPComponent 3 (fixSubgroup β) A := by
    rcases hσT with hσ | hσ
    · rw [hσ] at hαeq
      obtain ⟨ψ, hψ⟩ :=
        exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T hT α hα3 g a ε hαeq
      exact ⟨α, ε, by rcases hε' with rfl | rfl <;> simp, ψ, hψ, hA⟩
    · rw [hσ] at hαeq
      obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T
        T⁻¹ hT (mul_inv_cancel T) α hα3 g a ε hαeq
      have hshift : twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T =
          twistedEntrywiseAut TwistTag.D4 (3 - (ε : ℤ)) T := by
        have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-(ε : ℤ)) 1 T
        rw [show -(ε : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 3 - (ε : ℤ) by
          change -(ε : ℤ) + 1 * 3 = _
          ring] at h
        exact h.symm
      refine ⟨α⁻¹, 3 - ε, by rcases hε' with rfl | rfl <;> simp, ψ, hψ.trans hshift, ?_⟩
      rwa [CFSG.LocalAnalysis.GLTheoremA.I1431C2.fixSubgroup_inv_eq']
  obtain ⟨X, _, ⟨eX⟩, hs, hnab, hm⟩ := twisted_fixed_facts he hKe T hT j hj
  obtain ⟨e'⟩ := pSimple_equiv_of_conj
    ((MulEquiv.subgroupCongr (congrArg fixSubgroup hψ)).trans eX) hs hnab hAβ
  exact ⟨e, by omega, CFSG.Blueprint.LieModel.of_mulEquiv e'.symm hm⟩

end FieldTypes

private theorem graphType_comp {K : Type} [Field K] [Finite K] [CharP K 3] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ) (hε : ε < 3) (hε0 : ε ≠ 0)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε))
    {A : Subgroup (adjointGroup Tag.D4 K)} (hA : GLAPComponent 3 (fixSubgroup α) A) :
    CFSG.Blueprint.LieModel (PSimple 3 A) .G2 0 3 f := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv hf K hK α
      hα3 g a (by omega) hαeq
  haveI : CharP K₃ 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three (k := 3 * f) (by omega) (by rw [hK₃, ← pow_mul, mul_comm])
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.finite_graphFixedRootGroup_D4 Fr
  exact g2_of_layer_triD4
    (outerSubThree_of_mulEquiv e (outerSubThree_triD4_graphFixed hf hK₃ Fr hFr φ hφ3 hφout) A hA)

theorem d4ThreeOuterCases_holds : D4ThreeOuterCases := by
  intro K _ f hK hf α hα3 hout
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (by norm_num))
  haveI : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      hf hK
  obtain ⟨g, a, σ, ε, hε, hαeq, hσ3, hcase⟩ := outer_cube_normal_form_cases α hα3 hout
  rcases hcase with ⟨rfl, hσ1⟩ | ⟨hε0, hσ1⟩ | ⟨hε0, rfl⟩
  · exact Or.inl (fieldType_conj hf hK α hα3 g a σ hσ3 hσ1 hαeq)
  · exact Or.inr fun A hA =>
      Or.inr (graphFieldType_comp hf hK α hα3 g a σ ε hε hε0 hσ3 hσ1 hαeq hA)
  · exact Or.inr fun A hA => Or.inl (graphType_comp hf hK α hα3 g a ε hε hε0 hαeq hA)

theorem d4_fieldType_of_component_card {K : Type} [Field K] (hK : Nat.card K = 27)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hout : α ∉ inner (adjointGroup Tag.D4 K)) {A : Subgroup (adjointGroup Tag.D4 K)}
    (hA : GLAPComponent 3 (fixSubgroup α) A) (hcard : Nat.card (PSimple 3 A) = 4952179814400) :
    ∃ (T : K ≃+* K) (ψ : MulAut (adjointGroup Tag.D4 K)), (∀ c, T c = c ^ 3) ∧
      (ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.D4 T ∨
        ψ * α ^ 2 * ψ⁻¹ = entrywiseAdjointAut Tag.D4 T) := by
  rcases d4ThreeOuterCases_holds (show Nat.card K = 3 ^ 3 by rw [hK]; norm_num) (by norm_num) α
      hα3 hout with ⟨d, T, ψ, hd, hT, hψ⟩ | h
  · obtain rfl : d = 1 := by omega
    exact ⟨T, ψ, fun c => by simpa using hT c, hψ⟩
  · exfalso
    rcases h A hA with hm | ⟨f', hf', hm⟩
    · have h1 := CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two (by norm_num)
        (hm.chevalleyExceptionalModel (by decide))
      rw [hcard] at h1
      norm_num [ordG2] at h1
    · obtain rfl : f' = 1 := by omega
      have h1 := CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two (by norm_num)
        (hm.chevalleyExceptionalModel (by decide))
      rw [hcard] at h1
      norm_num [ordTrialityD4] at h1

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
