module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4O

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ClassicalInvolution.ModelFacts
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open scoped Pointwise

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

theorem exists_spin_of_mem_elementary {E : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)}
    (hE : E ∈ elementaryGroup Q₄)
    (h : (toLinEquiv _ 𝔽₃).symm E ∈ StatedOmega (StatedQuadPlus 4 𝔽₃)) :
    ∃ x : spinGroup Q₄, spinAction Q₄ x = E ∧
      Q3T.d4Proj 𝔽₃ x = QuotientGroup.mk' _ (⟨_, h⟩ : StatedOmega (StatedQuadPlus 4 𝔽₃)) := by
  rw [← range_spinAction_quadPlus (K := 𝔽₃) (by norm_num : 3 ≤ 4)] at hE
  obtain ⟨x, rfl⟩ := hE
  refine ⟨x, rfl, ?_⟩
  rw [spinToStatedProj_apply, QuotientGroup.mk'_apply]
  congr 1
  apply Subtype.ext
  apply (toLinEquiv _ 𝔽₃).injective
  rw [toLinEquiv_spinMatrix]
  exact (MulEquiv.apply_symm_apply _ _).symm

theorem simFam_one_one : SimFam 1 1 := by
  intro φ hsim hφ2 β _ hβ
  have hK : Nat.card 𝔽₃ = 3 := ModelFacts.TG3.natCard_galoisField_three
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have hφO : φ ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [hsim, one_mul]
  have hii : φ * φ = 1 := LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, hφ2, one_smul]
    rfl
  have hQ := nondegenerate_polarBilin_quadPlus 4 𝔽₃
  have hc := isCompl_plusSp_minusSp h2 hii
  have horth : ∀ u ∈ plusSp φ, ∀ w ∈ minusSp φ, polar Q₄ u w = 0 :=
    fun u hu w hw => polar_plusSp_minusSp h2 hφO hu hw
  have hdim := Submodule.finrank_add_eq_of_isCompl hc
  rw [finrank_d4] at hdim
  obtain ⟨V', ε, hV'ε, hε, hnd, hd3⟩ : ∃ (V' : Submodule 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃)) (ε : 𝔽₃),
      (∀ x ∈ V', φ x = ε • x) ∧ ε * ε = 1 ∧
        (polarBilin ((quadPlus 4 𝔽₃).comp V'.subtype)).Nondegenerate ∧
          3 ≤ Module.finrank 𝔽₃ V' := by
    by_cases h4 : 4 ≤ Module.finrank 𝔽₃ (plusSp φ)
    · exact ⟨plusSp φ, 1, fun x hx => by rw [one_smul]; exact mem_plusSp.mp hx, one_mul 1,
        nondegenerate_comp_subtype hQ hc horth, by omega⟩
    · exact ⟨minusSp φ, -1, fun x hx => by rw [neg_one_smul]; exact mem_minusSp.mp hx,
        by ring, nondegenerate_comp_subtype hQ hc.symm
          (fun u hu w hw => by rw [polar_comm]; exact horth w hw u hu), by omega⟩
  obtain ⟨P, a, haP, hQa⟩ := exists_hypPair_and_aniso hK hnd hd3
  let T : Trip Q₄ := ⟨P.e, P.f, a, P.Q_e, P.Q_f, P.polar_ef,
    (HypPair.mem_perp.mp haP).1, (HypPair.mem_perp.mp haP).2, hQa⟩
  have hTV : T.span ≤ V' := by
    rw [Trip.span, Submodule.span_le]
    rintro x (rfl | rfl | rfl)
    · exact P.e.2
    · exact P.f.2
    · exact a.2
  have hcomm : ∀ E ∈ T.eich, φ * E = E * φ := by
    rintro _ ⟨v, w, hv, hw, -, -, rfl⟩
    have h := eichler_conj hφO v w
    rw [hV'ε v (hTV hv), hV'ε w (hTV hw), eichler_smul_left, smul_smul, hε, one_smul] at h
    calc φ * eichler Q₄ v w = φ * eichler Q₄ v w * φ⁻¹ * φ := by
          rw [inv_mul_cancel_right]
      _ = eichler Q₄ v w * φ := by rw [h]
  have hmemE : ∀ E ∈ T.eich, E ∈ elementaryGroup Q₄ := by
    rintro _ ⟨v, w, -, -, -, -, rfl⟩
    exact eichler_mem_elementaryGroup _ v w
  have hmemΩ : ∀ E ∈ T.eich, E ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q₄,
      TauCeti.QuadraticMap.orthogonalGroup Q₄⁆ := by
    intro E hE
    rw [commutator_orthogonalGroup_quadPlus (by norm_num)]
    exact hmemE E hE
  set Y : Set (D4P 𝔽₃) := {c | ∃ E ∈ T.eich, ∃ h : (toLinEquiv _ 𝔽₃).symm E ∈
    StatedOmega (StatedQuadPlus 4 𝔽₃), c = QuotientGroup.mk' _ ⟨_, h⟩} with hY
  have hβY : ∀ c ∈ Y, β c = c := by
    rintro _ ⟨E, hE, h, rfl⟩
    obtain ⟨x, hx, hxc⟩ := exists_spin_of_mem_elementary (hmemE E hE) h
    rw [← hxc]
    refine hβ x ?_
    rw [hx]
    exact (hcomm E hE).symm
  obtain ⟨v₀, hv₀, hQv₀, hp₀, hq₀, ha₀⟩ := T.exists_singular_perp
    (by rw [hK]; decide) h2 hQ (by rw [finrank_d4]; norm_num)
  refine smul_pointFamily_of_fixPoint β Y hβY (pointMk v₀ hv₀ hQv₀) ?_ ?_
  · rintro _ ⟨E, hE, h, rfl⟩
    apply Subtype.ext
    rw [statedPointAction_mk_submodule, pointMk_submodule]
    simp only [MulEquiv.apply_symm_apply]
    rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe,
      T.eich_fix hE hp₀ hq₀ ha₀]
  · intro W hW hts hall
    refine T.no_invariant_ts h2 hQ (U := W) (by rw [hW, finrank_d4]) ?_ ?_
    · intro x hx
      rw [coe_quadPlus]
      exact hts x hx
    · intro E hE
      have h := hall _ ⟨E, hE, symm_mem_statedOmega (hmemΩ E hE), rfl⟩
      rw [statedProjectiveSubspaceAction_mk_apply] at h
      simpa only [MulEquiv.apply_symm_apply] using h

end CFSG.ClassicalInvolution.Q3.TL4
