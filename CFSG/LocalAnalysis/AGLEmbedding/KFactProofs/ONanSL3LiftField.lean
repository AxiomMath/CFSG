module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFourInner
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftMain
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField

theorem exists_generating_elemAbelian_field_of_equiv
    {X : Type} [Group X] [Finite X] (R : Sylow 3 X) (K : Subgroup X) [K.Normal] (z : X)
    {k : Type} [Field k] [Finite k] (h3 : 3 ∣ Nat.card k - 1)
    (ψ : Matrix.SpecialLinearGroup (Fin 3) k ≃* K)
    (hzc : z ∈ Subgroup.center X) (hz3 : orderOf z = 3)
    (hΩ : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ Subgroup.zpowers z)
    (hrank : Open.pRank 3 (R : Subgroup X) = 3) :
    ∃ A : Subgroup X, A ≤ (R : Subgroup X) ∧ Open.IsElemAbelian 3 A ∧ 3 ≤ Open.pRank 3 A ∧
      Subgroup.closure {x : K | ∃ f ∈ A, f ∉ Subgroup.centralizer (K : Set X) ∧
        f * (x : X) * f⁻¹ = x} = ⊤ := by
  classical
  obtain ⟨A, hAR, hAe, hAcard⟩ := exists_elemAbelian_card_27 hrank
  have hzR : z ∈ (R : Subgroup X) := mem_sylow_of_central R hzc hz3
  have hzA : z ∈ A := mem_of_pRank_eq_three hrank hzc hz3 hzR hAR hAe hAcard
  refine ⟨A, hAR, hAe, three_le_pRank_of_card hAe hAcard, ?_⟩
  have hCz : ∀ c ∈ Subgroup.centralizer (K : Set X), c ^ 3 = 1 → c ∈ Subgroup.zpowers z :=
    fun c hc hc3 => mem_zpowers_of_pow_three_eq_one R hzc hz3 hΩ hc hc3
  by_cases hall : ∀ a : A, ∃ g : GL (Fin 3) k, IsConjBy (actionAut K ψ (a : X)) g
  · exact SL3LiftFour.closure_fixed_eq_top_of_conj R K z h3 ψ hzc hz3 hΩ hAe hAcard hzA hall
  · obtain ⟨a₀, ha₀⟩ := not_forall.1 hall
    have hβ3 : actionAut K ψ (a₀ : X) ^ 3 = 1 := by
      rw [← map_pow, hAe.2 a₀ a₀.2, map_one]
    rcases exists_isConjBy_or_conj_fieldAut _ hβ3 with hconj | ⟨σ, H, hσ, hβ⟩
    · exact absurd hconj ha₀
    · obtain ⟨F, i, hi, hFσ⟩ := FrobData.exists_of_orderOf_eq_three hσ
      have hτ : orderOf F.τ = 3 := by
        rcases hi with rfl | rfl
        · rw [hFσ, pow_one]
          exact hσ
        · rw [hFσ, orderOf_pow' σ (by norm_num), hσ]
          norm_num
      have hact : actionAut K ψ ((a₀ : X) ^ i) =
          slConjugation 3 k H * slFieldAut (Fin 3) k F.τ * (slConjugation 3 k H)⁻¹ := by
        rw [map_pow, hβ, conj_pow, ← map_pow, hFσ]
      refine closure_fixed_eq_top_of_field K z h3 F hτ ((slConjugation 3 k H).trans ψ) hzc hCz hAe
        hAcard hzA (pow_mem a₀.2 i) ?_
      ext1 s
      rw [actionAut_trans, hact]
      simp

theorem kFactSL3LiftGenField : KFactSL3LiftGenField := by
  intro X _ _ R K _ z d _ hfd hK ⟨e⟩ hzc hzK hz3 hΩ hrank
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  obtain ⟨q, hqd, h3, h4, -⟩ := hfd
  simp only at hqd
  subst hqd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, by norm_num, ?_, ?_⟩, GaloisField q.p q.exponent,
      inferInstance, inferInstance, GaloisField.card q.p q.exponent q.exponent_pos.ne',
      ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
        (projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField q.p q.exponent))⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  obtain ⟨-, k, _, _, hkcard, ⟨e'⟩⟩ := hm
  have hcard : Nat.card k = q.card := by rw [hkcard, TauCeti.PrimePower.card_def]
  have h3k : 3 ∣ Nat.card k - 1 := by rw [hcard]; exact h3
  have h4k : Nat.card k ≠ 4 := by rw [hcard]; exact h4
  have hzcenter : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro κ
    exact Subtype.ext (Subgroup.mem_center_iff.mp hzc κ)
  have hZK : Subgroup.center K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hzcenter
    have hz1 : z = 1 := congrArg Subtype.val hzcenter
    rw [hz1, orderOf_one] at hz3
    omega
  obtain ⟨ψ⟩ := exists_mulEquiv_specialLinear h3k h4k hK.1
    ((e'.trans (projectiveSpecialLinearGroupEquivStatedProj 3 k).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k)) hZK
  exact exists_generating_elemAbelian_field_of_equiv R K z h3k ψ hzc hz3 hΩ hrank

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField
