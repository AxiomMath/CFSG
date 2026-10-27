module

public import CFSG.ClassicalInvolution.Q3.TL4D4NCOneC
public import CFSG.ClassicalInvolution.Q3.TL4D4NCFam
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Center
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthEigen

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ClassicalInvolution.ModelFacts
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open scoped Pointwise

variable {K : Type} [Field K]

theorem symm_mem_statedOmega {E : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hE : E ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆) :
    (toLinEquiv _ K).symm E ∈ StatedOmega (StatedQuadPlus 4 K) := by
  rw [statedOmega_eq_comap (coe_quadPlus 4 K), Subgroup.mem_comap]
  simpa using hE

theorem toLinEquiv_mem_orthogonalGroup (g : StatedOmega (StatedQuadPlus 4 K)) :
    toLinEquiv _ K g.val ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := by
  have h := Subgroup.mem_comap.mp ((statedOmega_eq_comap (coe_quadPlus 4 K)).le g.2)
  exact Subgroup.commutator_le_self _ h

theorem finrank_d4 : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
  rw [Module.finrank_fintype_fun_eq_card]
  rfl

theorem typeI_smul [Finite K] (hK : Nat.card K = 3) (β : MulAut (D4P K))
    (g : StatedOmega (StatedQuadPlus 4 K))
    (hg2 : ∀ x, toLinEquiv _ K g.val (toLinEquiv _ K g.val x) = x)
    (hβ : ∀ c : D4P K, c * QuotientGroup.mk' _ g = QuotientGroup.mk' _ g * c → β c = c) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  set φ := toLinEquiv _ K g.val with hφ
  have hφO : φ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
    toLinEquiv_mem_orthogonalGroup g
  have hii : φ * φ = 1 := LinearEquiv.ext hg2
  have hQ := nondegenerate_polarBilin_quadPlus 4 K
  have hc := isCompl_plusSp_minusSp h2 hii
  have horth : ∀ u ∈ plusSp φ, ∀ w ∈ minusSp φ, polar (quadPlus 4 K) u w = 0 :=
    fun u hu w hw => polar_plusSp_minusSp h2 hφO hu hw
  have hdim := Submodule.finrank_add_eq_of_isCompl hc
  rw [finrank_d4] at hdim
  obtain ⟨V', ε, hV'ε, hε, hnd, hd3⟩ : ∃ (V' : Submodule K (Fin 4 ⊕ Fin 4 → K)) (ε : K),
      (∀ x ∈ V', φ x = ε • x) ∧ ε * ε = 1 ∧
        (polarBilin ((quadPlus 4 K).comp V'.subtype)).Nondegenerate ∧
          3 ≤ Module.finrank K V' := by
    by_cases h4 : 4 ≤ Module.finrank K (plusSp φ)
    · exact ⟨plusSp φ, 1, fun x hx => by rw [one_smul]; exact mem_plusSp.mp hx, one_mul 1,
        nondegenerate_comp_subtype hQ hc horth, by omega⟩
    · exact ⟨minusSp φ, -1, fun x hx => by rw [neg_one_smul]; exact mem_minusSp.mp hx,
        by ring, nondegenerate_comp_subtype hQ hc.symm
          (fun u hu w hw => by rw [polar_comm]; exact horth w hw u hu), by omega⟩
  obtain ⟨P, a, haP, hQa⟩ := exists_hypPair_and_aniso hK hnd hd3
  let T : Trip (quadPlus 4 K) := ⟨P.e, P.f, a, P.Q_e, P.Q_f, P.polar_ef,
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
    calc φ * eichler (quadPlus 4 K) v w = φ * eichler (quadPlus 4 K) v w * φ⁻¹ * φ := by
          rw [inv_mul_cancel_right]
      _ = eichler (quadPlus 4 K) v w * φ := by rw [h]
  have hmemΩ : ∀ E ∈ T.eich, E ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ := by
    rintro _ ⟨v, w, -, -, -, -, rfl⟩
    rw [commutator_orthogonalGroup_quadPlus (by norm_num)]
    exact eichler_mem_elementaryGroup _ v w
  set Y : Set (D4P K) := {c | ∃ E ∈ T.eich, ∃ h : (toLinEquiv _ K).symm E ∈
    StatedOmega (StatedQuadPlus 4 K), c = QuotientGroup.mk' _ ⟨_, h⟩} with hY
  have hβY : ∀ c ∈ Y, β c = c := by
    rintro _ ⟨E, hE, h, rfl⟩
    refine hβ _ ?_
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply (toLinEquiv _ K).injective
    change toLinEquiv _ K ((toLinEquiv _ K).symm E * g.val) =
      toLinEquiv _ K (g.val * (toLinEquiv _ K).symm E)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
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
