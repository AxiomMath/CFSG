module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightGraphRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaLagMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)

section StepOne

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem not_mem_range_conj_omega_two_of_three_le (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hroot : ∀ k : Fin (n + 1), NsKindSp e t k κ)
    (hglob : NsRowGlobal e t (q2GlobalKind κ)) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)) :
    (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ ∉
      (MulAut.conj : nsGlobal e →* MulAut (nsGlobal e)).range := by
  intro hin
  obtain ⟨τ, hτ, hτm⟩ : ∃ τ : StatedLieTag, (τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧
      LieModel (nsGlobal e) τ (n + 1 + 1) 2 1 := by
    rcases hκ with rfl | rfl
    · exact ⟨_, Or.inr rfl, hglob.1⟩
    · exact ⟨_, Or.inl rfl, hglob.1⟩
  obtain ⟨F, _, _, _, V, _, _, _, Q, hF, hnd, hdim, -, ⟨φ⟩⟩ :=
    exists_mulEquiv_omega_of_lieModel_two hτ hτm
  have hwG := conj_mem_nsGlobal_of_mem_range_two hK hn e ht hKt hκ hglob hg hin
  have hss := congrArg Subtype.val (mul_self_map_conj_eq_one φ ht hwG)
  have h10 : 10 ≤ finrank F V := by rw [hdim]; omega
  by_cases hlag : (∀ w ∈ omegaInvSpace (φ ⟨_, hwG⟩ : V ≃ₗ[F] V), Q w = 0) ∧
      2 * finrank F (omegaInvSpace (φ ⟨_, hwG⟩ : V ≃ₗ[F] V)) = finrank F V ∧
      finrank F (omegaInvSpace (φ ⟨_, hwG⟩ : V ≃ₗ[F] V)) % 4 = 2
  · have hn4 : 4 ≤ n := by
      have h1 := hlag.2.1
      have h2 := hlag.2.2
      omega
    exact spTwoOmegaLagrangianATwoInput_holds κ G L hset n K hK hn4 e t ht hKt hroot hglob F V Q
      φ hF hnd hdim g hwG hlag
  · exact false_of_mem_omegaO2Cent hset (by omega) e ht hKt φ hwG
      (mem_omegaO2Cent_two_of_not_lagrangian hF hnd (φ ⟨_, hwG⟩).2 hss h10 hlag)

end StepOne

@[expose] def SpTwoOmegaBClassAtInput (κ : Sp2mKind) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) → NsRowGlobal e t (q2GlobalKind κ) →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G))
        (K' : Type) [Field K'] [Finite K'] (Q : QuadraticForm K' (Fin (2 * (n + 1 + 1)) → K')),
        Nat.card K' = 2 ^ 1 → Q.polarBilin.Nondegenerate →
        (∃ T : Submodule K' (Fin (2 * (n + 1 + 1)) → K'), Module.finrank K' T = 3 ∧
          ∀ x ∈ T, Q x = 0) →
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
          elementaryGroup Q →
        ∀ (ε : nsGlobal e ≃* matrixProjectiveDerived Q) (β : MulAut (matrixProjectiveDerived Q))
          (s : matrixIsometries Q), s * s = 1 →
          Odd (((s : GL (Fin (2 * (n + 1 + 1))) K') :
            Matrix (Fin (2 * (n + 1 + 1))) (Fin (2 * (n + 1 + 1))) K') - 1).rank →
          3 ≤ (((s : GL (Fin (2 * (n + 1 + 1))) K') :
            Matrix (Fin (2 * (n + 1 + 1))) (Fin (2 * (n + 1 + 1))) K') - 1).rank →
          β⁻¹ * MulAut.congr ε ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) * β ≠
            matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)

theorem spTwoOmegaBClassAtInput_of_bClassInput {κ : Sp2mKind} (h : SpTwoOmegaBClassInput κ)
    {n : ℕ} (hn : 4 ≤ n) : SpTwoOmegaBClassAtInput κ n :=
  fun G _ _ L hset K _ _ _ hK => h G L hset n K hK hn

section Class

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem rank_eq_one_of_bClassAt_two {κ : Sp2mKind} (hκ : κ = .omegaPlus ∨ κ = .omegaMinus)
    {n : ℕ} (hB : SpTwoOmegaBClassAtInput κ n) (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin (n + 1), NsKindSp e t k κ) (hglob : NsRowGlobal e t (q2GlobalKind κ))
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G))
    {K' : Type} [Field K'] [Finite K'] {Q : QuadraticForm K' (Fin (2 * (n + 1 + 1)) → K')}
    (hK' : Nat.card K' = 2 ^ 1) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (n + 1 + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (ε : nsGlobal e ≃* matrixProjectiveDerived Q) (β : MulAut (matrixProjectiveDerived Q))
    (s : matrixIsometries Q) (hs : s * s = 1)
    (hβ : β⁻¹ * MulAut.congr ε ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) * β =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) :
    (((s : GL (Fin (2 * (n + 1 + 1))) K') :
      Matrix (Fin (2 * (n + 1 + 1))) (Fin (2 * (n + 1 + 1))) K') - 1).rank = 1 := by
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  rcases Nat.even_or_odd (((s : GL (Fin (2 * (n + 1 + 1))) K') :
      Matrix (Fin (2 * (n + 1 + 1))) (Fin (2 * (n + 1 + 1))) K') - 1).rank with hev | hodd
  · exfalso
    have hsΩ : (s : GL (Fin (2 * (n + 1 + 1))) K') ∈ matrixDerived Q := by
      rw [CFSG.RankThree.PartOne.AUTSL.mem_matrixDerived_iff_even hQ hT s.2,
        ← lagRank_sub_one_eq_finrank_commSpace]
      exact hev
    rw [matrixProjectiveConjugationHom_eq_conj Q s hsΩ] at hβ
    have hc : MulAut.congr ε ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) =
        MulAut.conj (β (matrixProjectiveProjection Q ⟨s, hsΩ⟩)) := by
      rw [← lagMulAut_mul_conj_mul_inv, ← hβ]
      group
    exact not_mem_range_conj_omega_two_of_three_le hset hK hn e ht hKt hκ hroot hglob hg
      (lagMem_range_conj_of_congr ε _ hc)
  · by_contra h1'
    have h3 : 3 ≤ (((s : GL (Fin (2 * (n + 1 + 1))) K') :
        Matrix (Fin (2 * (n + 1 + 1))) (Fin (2 * (n + 1 + 1))) K') - 1).rank := by
      obtain ⟨j, hj⟩ := hodd
      omega
    exact hB G L hset K hK e t ht hKt hroot hglob g hg K' Q hK' hQ hT hE ε β s hs hodd h3 hβ

theorem exists_conj_of_bClassAt_two_omegaMinus {n : ℕ}
    (hB : SpTwoOmegaBClassAtInput .omegaMinus n) (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin (n + 1), NsKindSp e t k .omegaMinus)
    (hglob : NsRowGlobal e t (q2GlobalKind .omegaMinus))
    (htN : t ∈ normalizer (nsGlobal e : Set G)) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)) :
    ∃ β : MulAut (nsGlobal e), β * (nsGlobal e).normalizerMonoidHom ⟨t, htN⟩ =
      (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ * β := by
  have hty : LieModel (nsGlobal e) .POmegaPlus (n + 1 + 1) 2 1 := hglob.1
  have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
    (by decide) hty
  obtain ⟨K', _, _, Q, hK', hQ, hT, hE, hconj, ⟨ε⟩⟩ :=
    CFSG.ComponentClassification.EvenOrthSelector.exists_coordinate_witness (Or.inl rfl) hC
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hg1 : (1 : G)⁻¹ * t * 1 ∈ normalizer (nsGlobal e : Set G) := by simpa using htN
  obtain ⟨β, s, hs, hβ⟩ := exists_conj_linear_of_conj_nsGlobal hset hn e hK ht hKt hK'
    hQ hT hE hconj ε hg
  obtain ⟨β₀, s₀, hs₀, hβ₀⟩ := exists_conj_linear_of_conj_nsGlobal hset hn e hK ht hKt
    hK' hQ hT hE hconj ε hg1
  have r1 := rank_eq_one_of_bClassAt_two (Or.inr rfl) hB hset hK hn e ht hKt hroot hglob hg hK'
    hQ hT hE ε β s hs hβ
  have r0 := rank_eq_one_of_bClassAt_two (Or.inr rfl) hB hset hK hn e ht hKt hroot hglob hg1 hK'
    hQ hT hE ε β₀ s₀ hs₀ hβ₀
  obtain ⟨γ, hγ⟩ := exists_conj_of_rank_eq_one hQ hT hs hs₀ r1 r0
  rw [normalizerMonoidHom_one_conj_eq htN hg1] at hβ₀
  exact exists_conj_of_linearClass_conj ε hβ hβ₀ hγ

theorem exists_conj_of_bClassAt_two_omegaPlus {n : ℕ}
    (hB : SpTwoOmegaBClassAtInput .omegaPlus n) (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin (n + 1), NsKindSp e t k .omegaPlus)
    (hglob : NsRowGlobal e t (q2GlobalKind .omegaPlus))
    (htN : t ∈ normalizer (nsGlobal e : Set G)) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)) :
    ∃ β : MulAut (nsGlobal e), β * (nsGlobal e).normalizerMonoidHom ⟨t, htN⟩ =
      (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ * β := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hty : LieModel (nsGlobal e) .POmegaMinus (n + 1 + 1) 2 1 := hglob.1
  obtain ⟨K', _, _, b, c, hirr, ε, hK', hlinα⟩ :=
    exists_isometry_eq_of_lieModel_minus (by omega) hty
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hreg := regular_coordinateQuadMinus (n + 1 + 1) K' b c (by omega) hirr
  have hE := commutator_coordinateQuadMinus (n + 1 + 1) K' b c (by omega) hirr
  have hg1 : (1 : G)⁻¹ * t * 1 ∈ normalizer (nsGlobal e : Set G) := by simpa using htN
  obtain ⟨s, hs, hsα⟩ := hlinα _ (normalizerMonoidHom_mul_self (mul_self_inv_conj_eq_one htt g) hg)
  obtain ⟨s₀, hs₀, hs₀α⟩ :=
    hlinα _ (normalizerMonoidHom_mul_self (mul_self_inv_conj_eq_one htt 1) hg1)
  have hsα' : (1 : MulAut _)⁻¹ * MulAut.congr ε ((nsGlobal e).normalizerMonoidHom
      ⟨g⁻¹ * t * g, hg⟩) * 1 = matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) := by
    rw [inv_one, one_mul, mul_one]
    exact hsα
  have hs₀α' : (1 : MulAut _)⁻¹ * MulAut.congr ε ((nsGlobal e).normalizerMonoidHom
      ⟨(1 : G)⁻¹ * t * 1, hg1⟩) * 1 =
        matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s₀) := by
    rw [inv_one, one_mul, mul_one]
    exact hs₀α
  have r1 := rank_eq_one_of_bClassAt_two (Or.inl rfl) hB hset hK hn e ht hKt hroot hglob hg hK'
    hreg.1 hreg.2 hE ε 1 s hs hsα'
  have r0 := rank_eq_one_of_bClassAt_two (Or.inl rfl) hB hset hK hn e ht hKt hroot hglob hg1 hK'
    hreg.1 hreg.2 hE ε 1 s₀ hs₀ hs₀α'
  obtain ⟨γ, hγ⟩ := exists_conj_of_rank_eq_one hreg.1 hreg.2 hs hs₀ r1 r0
  rw [normalizerMonoidHom_one_conj_eq htN hg1] at hs₀α'
  exact exists_conj_of_linearClass_conj ε hsα' hs₀α' hγ

end Class

theorem spTwoOmegaClassEightInput_omegaMinus_of_bClass
    (hB : SpTwoOmegaBClassAtInput .omegaMinus 3) : SpTwoOmegaClassEightInput .omegaMinus := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot hglob htN g hg
  exact exists_conj_of_bClassAt_two_omegaMinus hB hset hK le_rfl e ht hKt hroot hglob htN hg

theorem spTwoOmegaClassEightInput_omegaPlus_of_bClass
    (hB : SpTwoOmegaBClassAtInput .omegaPlus 3) : SpTwoOmegaClassEightInput .omegaPlus := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot hglob htN g hg
  exact exists_conj_of_bClassAt_two_omegaPlus hB hset hK le_rfl e ht hKt hroot hglob htN hg

theorem spTwoOmegaClassInput_of_bClass {κ : Sp2mKind} (hκ : κ = .omegaPlus ∨ κ = .omegaMinus)
    (hB : SpTwoOmegaBClassInput κ) : SpTwoOmegaClassInput κ := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot hglob htN g hg
  rcases hκ with rfl | rfl
  · exact exists_conj_of_bClassAt_two_omegaPlus (spTwoOmegaBClassAtInput_of_bClassInput hB hn)
      hset hK (by omega) e ht hKt hroot hglob htN hg
  · exact exists_conj_of_bClassAt_two_omegaMinus (spTwoOmegaBClassAtInput_of_bClassInput hB hn)
      hset hK (by omega) e ht hKt hroot hglob htN hg

end CFSG.SeitzReduction.SymplecticPilot
