module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOmegaUniqueModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeGraphMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal Module
open scoped Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.RankThree.OrthogonalInvolutions (commSpace)
open CFSG.RankThree.PartOne.AUTSL (reflMat reflMat_mem_isometries reflMat_mul_self
  finrank_commSpace_reflMat)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

@[expose] def SpThreeOmegaTorusInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k (threeOmegaRootKind κ)) → SpOmegaRowGlobal e t f κ →
        centralizerPerfectCore (modelToG e (spATorus K 3 1)) ≤ centralizer ({t} : Set G)

@[expose] def OmegaMinusEightSpSixNonembeddingInput : Prop :=
  ∀ (Y : Type) [Group Y] (g : ℕ), 1 ≤ g → LieModel Y .POmegaMinus 4 2 g →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * g) →
      ∀ φ : Y →* StatedSp 3 K, ¬ Function.Injective φ

section ClassDet

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem mem_normalizer_of_linear_three (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hglob : SpOmegaRowGlobal e t f κ)
    (htor : centralizerPerfectCore (modelToG e (spATorus K 3 1)) ≤ centralizer ({t} : Set G))
    (htN : t ∈ normalizer (spGlobal e : Set G))
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2] (hK' : Nat.card K' = 2 ^ f)
    {Q : QuadraticForm K' (Fin (2 * (3 + 1)) → K')} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (3 + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (ε₀ : spGlobal e ≃* matrixProjectiveDerived Q) {s₀ : matrixIsometries Q}
    (hs₀ : s₀ * s₀ = 1) (hr₀ : finrank K' (commSpace (matrixLinearIso s₀.val)) = 1)
    (hθ₀ : MulAut.congr ε₀ ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩) =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₀))
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G))
    {β : MulAut (matrixProjectiveDerived Q)} {s : matrixIsometries Q} (hs : s * s = 1)
    (hβ : β⁻¹ * MulAut.congr ε₀ ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) * β =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) :
    g ∈ normalizer (spGlobal e : Set G) := by
  obtain ⟨σ⟩ : Nonempty (K ≃+* K') := by
    have := Fintype.ofFinite K
    have := Fintype.ofFinite K'
    exact ⟨FiniteField.ringEquivOfCardEq (K := K) (K' := K') (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc, hK'])⟩
  have hθ₀' : (1 : MulAut (matrixProjectiveDerived Q))⁻¹ *
      MulAut.congr ε₀ ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩) * 1 =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₀) := by
    rw [inv_one, one_mul, mul_one]
    exact hθ₀
  rcases Nat.even_or_odd (finrank K' (commSpace (matrixLinearIso s.val))) with hev | ⟨m, hm⟩
  · exact (false_of_linear_of_even hset (by norm_num) (by norm_num) hKc hf e ht hKt hκ hglob hg
      hQ hT ε₀ β s hev hβ).elim
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  ·
    obtain ⟨γ, hγ⟩ := exists_conj_of_rank_eq_one hQ hT hs hs₀
      (by rw [lagRank_sub_one_eq_finrank_commSpace]; omega)
      (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr₀)
    obtain ⟨β', hβ'⟩ := exists_conj_of_linearClass_conj ε₀ hβ hθ₀' hγ
    exact mem_normalizer_of_conj_mulAut hset (by norm_num) hKc hf e ht hKt htN hg β' hβ'
  ·
    exfalso
    have hsh := spOmegaBShapeAut_of_conj e σ hQ hT hE ε₀ hs₀ hr₀ hθ₀' hs hmpos hm hβ
    have hm1 : m = 1 := by
      have := hsh.2.1
      omega
    subst hm1
    obtain ⟨hZ, hodd⟩ := spGlobal_inf_centralizer_eq_bot_and_odd (by norm_num) hKc hf e ht hKt hκ
      hglob
    refine false_of_spOmegaBShapeAut hset (by norm_num) hKc hf e ht hKt htN hZ hodd
      spACentralizerPerfectInput_holds spAToralInput_holds (fun y hy => ?_) htor hg hsh
    rcases coset_dichotomy_of_linear e σ hQ hT hE ε₀ hs₀ hr₀ hθ₀ y hy with h | ⟨j, hj, hj3, hshj⟩
    · exact Or.inl h
    · have hj1 : j = 1 := by omega
      subst hj1
      exact Or.inr hshj

end ClassDet

theorem spThreeOmegaRowUniqueInput_omegaMinus_of_torus
    (htor : SpThreeOmegaTorusInput .omegaMinus) : SpThreeOmegaRowUniqueInput .omegaMinus := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot hglob g hg
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hty : LieModel (spGlobal e) .POmegaMinus (3 + 1) 2 f := hglob.1
  obtain ⟨K', _, _, b, c, hirr, ε, hK', hlinα⟩ :=
    exists_isometry_eq_of_lieModel_minus (by norm_num) hty
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hreg := regular_coordinateQuadMinus (3 + 1) K' b c (by norm_num) hirr
  have hE := commutator_coordinateQuadMinus (3 + 1) K' b c (by norm_num) hirr
  have hg1 : (1 : G)⁻¹ * t * 1 ∈ normalizer (spGlobal e : Set G) := by simpa using htN
  obtain ⟨s₀, hs₀, hs₀α⟩ :=
    hlinα _ (normalizerMonoidHom_mul_self (mul_self_inv_conj_eq_one htt 1) hg1)
  rw [normalizerMonoidHom_one_conj_eq htN hg1] at hs₀α
  have hr₀ := bCoord_finrank_eq_one_of_outer hreg.1 hreg.2 ε (hglob.2 htN).1
    (bCoord_fixed_centreless e ht hKt (le_spGlobal hK4 (by norm_num) e) htN (hglob.2 htN).1)
    hs₀ hs₀α
  obtain ⟨s, hs, hsα⟩ :=
    hlinα _ (normalizerMonoidHom_mul_self (mul_self_inv_conj_eq_one htt g) hg)
  have hβ : (1 : MulAut _)⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom
      ⟨g⁻¹ * t * g, hg⟩) * 1 = matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) := by
    rw [inv_one, one_mul, mul_one]
    exact hsα
  exact mem_normalizer_of_linear_three hset hKc hf e ht hKt (Or.inr rfl) hglob
    (htor G L hset f K hKc hf e t ht hKt hroot hglob) htN hK' hreg.1 hreg.2 hE ε hs₀ hr₀ hs₀α hg
    hs hβ

theorem spThreeOmegaRowUniqueInput_omegaPlus_of_torus
    (htor : SpThreeOmegaTorusInput .omegaPlus) (hU18 : OmegaMinusEightSpSixNonembeddingInput) :
    SpThreeOmegaRowUniqueInput .omegaPlus := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot hglob g hg
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hty : LieModel (spGlobal e) .POmegaPlus (3 + 1) 2 f := hglob.1
  have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
    (by decide) hty
  have hI := (even_orthogonal_involutions_conjugate_into_semilinear_image (spGlobal e)
    .POmegaPlus (Or.inl rfl) (3 + 1) f hC).1
  obtain ⟨⟨-, hf1, -⟩, K', _, _, hK', ⟨eE⟩⟩ := hC
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hconj := (hI K' hK' eE).1
  have hreg := regular_coordinateQuadPlus (K := K') (n := 3 + 1) (by norm_num)
  have hE := commutator_coordinateQuadPlus (K := K') (n := 3 + 1) (by norm_num)
  obtain ⟨v, hv⟩ : ∃ v : Fin (2 * (3 + 1)) → K', coordinateQuadPlus (3 + 1) K' v = 1 := by
    obtain ⟨a, ha⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hreg.1
    obtain ⟨c, hc2⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K' 2)
      (1 / coordinateQuadPlus (3 + 1) K' a)
    refine ⟨c • a, ?_⟩
    rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, _root_.sq, ← hc2, one_div,
      inv_mul_cancel₀ ha]
  have hv0 : coordinateQuadPlus (3 + 1) K' v ≠ 0 := by rw [hv]; exact one_ne_zero
  set ε := coordinatePlusWitnessEquiv K' eE with hεdef
  set θ := (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ with hθdef
  have hθθ : θ * θ = 1 := by
    rw [hθdef, ← map_mul, show (⟨t, htN⟩ : normalizer (spGlobal e : Set G)) * ⟨t, htN⟩ = 1 from
      Subtype.ext htt, map_one]
  have hαα : MulAut.congr ε θ * MulAut.congr ε θ = 1 := by rw [← map_mul, hθθ, map_one]
  have hαo : MulAut.congr ε θ ∉
      inner (matrixProjectiveDerived (coordinateQuadPlus (3 + 1) K')) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact (hglob.2 htN).1
  have hαfix : LieModel (fixedSubgroup (MulAut.congr ε θ)) .PSp 3 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θ) (hglob.2 htN).2
  obtain ⟨Ψ, hΨ⟩ := exists_conj_eq_symmetryAut_of_lieModel_PSp hf1 hK' (by norm_num) hreg.1
    hreg.2 hE hconj hv _ hαα hαo hαfix
  set ε₀ := ε.trans Ψ⁻¹ with hε₀
  set s₀ := symmetryIsometry (coordinateQuadPlus (3 + 1) K') v with hs₀def
  have hs₀val : s₀.val = reflMat _ v hv0 := bParam_symmetryGL_eq_reflMat hv hv0
  have hs₀ : s₀ * s₀ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hs₀val, Subgroup.coe_one]
    exact reflMat_mul_self v hv0
  have hr₀ : finrank K' (commSpace (matrixLinearIso s₀.val)) = 1 := by
    rw [hs₀val]
    exact finrank_commSpace_reflMat hreg.1 v hv0
  have hθ₀ : MulAut.congr ε₀ θ =
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s₀) := by
    rw [hε₀, mulAutCongr_trans_inv, hΨ]
    group
    rfl
  set θw := (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ with hθwdef
  have hww : MulAut.congr ε₀ θw * MulAut.congr ε₀ θw = 1 := by
    rw [← map_mul, hθwdef, normalizerMonoidHom_mul_self (mul_self_inv_conj_eq_one htt g) hg,
      map_one]
  rcases exists_conj_linear_or_lieModel hf1 hK' (N := 3 + 1) (by norm_num) hreg.1 hreg.2 hE
      hconj hww with ⟨β, s, hs, hβ⟩ | ⟨⟨m, hm⟩, τ, P, hτ, hPF, hPc, hPlie⟩
  · exact mem_normalizer_of_linear_three hset hKc hf e ht hKt (Or.inl rfl) hglob
      (htor G L hset f K hKc hf e t ht hKt hroot hglob) htN hK' hreg.1 hreg.2 hE ε₀ hs₀ hr₀ hθ₀ hg
      hs hβ
  · exfalso
    obtain ⟨φ, hφ⟩ := exists_injective_of_congr ε₀ θw
      (fun P' hP'c hP'F => exists_injective_of_perfect_le_fixedSubgroup_conj hset (by norm_num) e
        ht hKt hg P' hP'c hP'F) P hPc hPF
    have hg1 : 1 ≤ f / 2 := by omega
    have hKg : Nat.card K = 2 ^ (2 * (f / 2)) := by rw [hKc]; congr 1; omega
    rcases hτ with rfl | rfl
    · have hcard := Subgroup.card_dvd_of_injective φ hφ
      rw [F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hPlie] at hcard
      exact not_ordD_dvd_card_statedSp_of_even (N := 4) (by norm_num) ⟨2, rfl⟩ hg1 hKg hcard
    · exact hU18 P (f / 2) hg1 hPlie K hKg φ hφ

end CFSG.SeitzReduction.SymplecticPilot
