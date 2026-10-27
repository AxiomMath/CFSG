module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankOneCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBDihedralPair
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalDihedralLinearModel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerRankOneTwoGroups
public import CFSG.Open.FusionDefs

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup CFSG.Assembly.LowTwoRank

namespace RankSmallSources

theorem two_le_pRank_of_four {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 4) : 2 ≤ CFSG.pRank 2 X := by
  apply le_csSup
  · refine ⟨Nat.card X, ?_⟩
    rintro r ⟨B, -, hB⟩
    have h1 : r < 2 ^ r := Nat.lt_two_pow_self
    have h2 : Nat.card B ≤ Nat.card X := Subgroup.card_le_card_group B
    omega
  · exact ⟨E, hE, by rw [hcard]; norm_num⟩

theorem two_le_pRank_of_commuting {X : Type*} [Group X] [Finite X] {z u : X}
    (hz : orderOf z = 2) (hu : orderOf u = 2) (hzu : z * u = u * z) (hne : u ∉ zpowers z) :
    2 ≤ CFSG.pRank 2 X := by
  obtain ⟨hE, hcard⟩ := DihedralPair.klein_closure hz hu hzu hne
  exact two_le_pRank_of_four hE hcard

theorem two_le_pRank_psl_two {K : Type*} [Field K] [Finite K] (hK : ringChar K ≠ 2) :
    2 ≤ CFSG.pRank 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  classical
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.ComponentInitial.finite_odd_field_two_squares hK (-1)
  obtain ⟨x, y, -, -, hx, hy, hxy⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.sl2_exists_anticommuting_pair hab
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) K) ≠ 1 :=
    CFSG.LocalAnalysis.ComponentInitial.sl2_neg_one_ne_one hK
  have hnegc : (-1 : Matrix.SpecialLinearGroup (Fin 2) K) ∈
      center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [mem_center_iff]
    intro g
    rw [mul_neg_one, neg_one_mul]
  set q := QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 2) K)) with hq
  have hq1 : q (-1) = 1 := (QuotientGroup.eq_one_iff _).mpr hnegc
  have hnc : x * y ≠ y * x := by
    intro h
    apply hneg
    have h1 : -1 * (y * x) = 1 * (y * x) := by rw [one_mul, ← hxy, h]
    exact mul_right_cancel h1
  have hcomm_of_center : ∀ c : Matrix.SpecialLinearGroup (Fin 2) K,
      c ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) → ∀ g, g * c = c * g :=
    fun c hc g => mem_center_iff.mp hc g
  have hx2 : q x ^ 2 = 1 := by rw [← map_pow, hx, hq1]
  have hy2 : q y ^ 2 = 1 := by rw [← map_pow, hy, hq1]
  have hx1 : q x ≠ 1 := by
    intro h
    have hxc := (QuotientGroup.eq_one_iff x).mp h
    exact hnc (hcomm_of_center x hxc y).symm
  have hy1 : q y ≠ 1 := by
    intro h
    have hyc := (QuotientGroup.eq_one_iff y).mp h
    exact hnc (hcomm_of_center y hyc x)
  have hcomm : q x * q y = q y * q x := by
    rw [← map_mul, ← map_mul, hxy, map_mul, hq1, one_mul]
  have hne : q y ∉ zpowers (q x) := by
    intro h
    rcases DihedralPair.mem_zpowers_eq_one_or_eq (orderOf_eq_prime hx2 hx1) h with h1 | h1
    · exact hy1 h1
    ·
      have h2 : q (y * x⁻¹) = 1 := by rw [map_mul, h1, map_inv, mul_inv_cancel]
      have h3 := hcomm_of_center _ ((QuotientGroup.eq_one_iff _).mp h2) x
      apply hnc
      calc x * y = x * (y * x⁻¹) * x := by group
        _ = (y * x⁻¹) * x * x := by rw [h3]
        _ = y * x := by group
  exact two_le_pRank_of_commuting (orderOf_eq_prime hx2 hx1) (orderOf_eq_prime hy2 hy1) hcomm hne

@[expose] def permA : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def permB : Equiv.Perm (Fin 7) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem permA_mem : permA ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup, permA, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  rfl

theorem permB_mem : permB ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup, permB, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  rfl

theorem two_le_pRank_alternating_seven : 2 ≤ CFSG.pRank 2 (alternatingGroup (Fin 7)) := by
  set x : alternatingGroup (Fin 7) := ⟨permA, permA_mem⟩
  set y : alternatingGroup (Fin 7) := ⟨permB, permB_mem⟩
  have hx2 : x ^ 2 = 1 := Subtype.ext (by
    change permA * permA = 1
    decide)
  have hy2 : y ^ 2 = 1 := Subtype.ext (by
    change permB * permB = 1
    decide)
  have hx1 : x ≠ 1 := fun h => by
    have h1 : permA = 1 := congrArg Subtype.val h
    revert h1
    decide
  have hy1 : y ≠ 1 := fun h => by
    have h1 : permB = 1 := congrArg Subtype.val h
    revert h1
    decide
  have hxy : y ≠ x := fun h => by
    have h1 : permB = permA := congrArg Subtype.val h
    revert h1
    decide
  have hcomm : x * y = y * x := Subtype.ext (by
    change permA * permB = permB * permA
    decide)
  have hne : y ∉ zpowers x := by
    intro h
    rcases DihedralPair.mem_zpowers_eq_one_or_eq (orderOf_eq_prime hx2 hx1) h with h1 | h1
    · exact hy1 h1
    · exact hxy h1
  exact two_le_pRank_of_commuting (orderOf_eq_prime hx2 hx1) (orderOf_eq_prime hy2 hy1) hcomm hne

theorem quotient_center_equiv_zstar (J : Type*) [Group J] :
    Nonempty ((J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J) ≃*
      J ⧸ CFSG.Open.fusionZStar J) := by
  have hle : CFSG.oddCore J ≤ CFSG.Open.fusionZStar J := by
    intro x hx
    change (QuotientGroup.mk' (CFSG.oddCore J) x : J ⧸ CFSG.oddCore J) ∈
      center (J ⧸ CFSG.oddCore J)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hmap : (CFSG.Open.fusionZStar J).map (QuotientGroup.mk' (CFSG.oddCore J)) =
      center (J ⧸ CFSG.oddCore J) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ hle)⟩

theorem statedClassicalModel_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G' ≃* G)
    {t : StatedLieTag} {n p f : ℕ} (h : StatedClassicalModel G t n p f) :
    StatedClassicalModel G' t n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

end RankSmallSources

open RankSmallSources

theorem small_source_models_force_rank_at_least_two {J : Type} [Group J] [Finite J]
    (hA : CFSG.IsQuasisimple (J ⧸ CFSG.oddCore J))
    (h : (∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧
          StatedClassicalModel (J ⧸ CFSG.oddCore J) .PSL 2 p f) ∨
      Nonempty ((J ⧸ CFSG.oddCore J) ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (J ⧸ CFSG.Open.fusionZStar J) .PSL 3 2 2) :
    2 ≤ CFSG.pRank 2 J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOodd : ¬ 2 ∣ Nat.card (CFSG.oddCore J) := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact UnbalancedCatalog.EvenCatalog.odd_card_oddCore
  have hrankJ : CFSG.pRank 2 J = CFSG.pRank 2 (J ⧸ CFSG.oddCore J) := by
    rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top,
      SectionRank.pRank_quotient_eq (CFSG.oddCore J) hOodd]
  rcases h with ⟨p, f, hp, hpodd, hf, hmodel⟩ | hAlt | hT
  ·
    obtain ⟨-, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hmodel
    have hchar : CharP K p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hcard
    have hK : ringChar K ≠ 2 := by
      rw [ringChar.eq K p]
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    rw [hrankJ, UnbalancedLayer.pRank_eq_of_mulEquiv one_lt_two
      (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)]
    exact two_le_pRank_psl_two hK
  ·
    obtain ⟨e⟩ := hAlt
    rw [hrankJ, UnbalancedLayer.pRank_eq_of_mulEquiv one_lt_two e]
    exact two_le_pRank_alternating_seven
  ·
    by_contra hlt
    have hle : CFSG.pRank 2 J ≤ 1 := by omega
    obtain ⟨-, z, hz, -, -, -, r, hr, -, -, -, -, hsylT, -⟩ :=
      rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hle hA
    obtain ⟨eT⟩ := quotient_center_equiv_zstar J
    have hT' := statedClassicalModel_of_mulEquiv eT hT
    obtain ⟨P⟩ : Nonempty (Sylow 2 ((J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J))) :=
      inferInstance
    obtain ⟨⟨eP⟩, -, -⟩ := hsylT P
    have hP : Nonempty ((P : Subgroup ((J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J))) ≃*
        DihedralGroup (2 ^ ((r - 1) - 1))) := by
      rw [show r - 1 - 1 = r - 2 by omega]
      exact ⟨eP⟩
    obtain ⟨hcases, -⟩ :=
      OutcomeLocal.dihedral_sylow_linear_model_odd_rank_one hT' (s := r - 1) (by omega) P hP
    rcases hcases with ⟨h1, -⟩ | h1 | h1
    · omega
    · simp at h1
    · simp at h1

end CFSG.ComponentClassification.UnbalancedGS
