module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddLinear
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplecticUniversalPairExclusion
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddSymplectic

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification CFSG.Assembly.LowTwoRank

namespace EscapingNotOddSymplectic

variable {K : Type} [Field K]

theorem symplecticSignScalars_eq_spSigns {V : Type} [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) :
    CLSFourGroupScalarSquare.symplecticSignScalars B = ProjectiveSymplectic.spSigns B := by
  ext g
  rw [CLSFourGroupScalarSquare.mem_symplecticSignScalars, ProjectiveSymplectic.mem_spSigns,
    Units.ext_iff, Units.ext_iff, Units.val_one, Units.val_neg, Units.val_one]

@[expose] def projEquiv {r : ℕ} (hr : 1 ≤ r) :
    StatedProj (StatedSp r K) ≃* sesqUnitaryGroup (pairedSympForm K r) ⧸
      ProjectiveSymplectic.spSigns (pairedSympForm K r) :=
  ((CatalogueBSymplecticB.projectiveStatedEquiv hr).trans
    (OddSymplectic.symplecticProjEquiv (pairedSympForm K r)).symm).trans
      (QuotientGroup.quotientMulEquivOfEq (symplecticSignScalars_eq_spSigns _))

end EscapingNotOddSymplectic

open EscapingNotOddSymplectic

theorem commuting_block_odd_symplectic_overgroup_exclusion {G : Type} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {L : Subgroup G} (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ∀ n p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel (L ⧸ center L) .PSp n p f := by
  rintro n p f hp2 ⟨⟨hp, hf, hn, -⟩, k, _, _, hk, ⟨e⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  have hr : 1 ≤ n := by omega
  let ψ : L ⧸ center L →* sesqUnitaryGroup (pairedSympForm k n) ⧸
      ProjectiveSymplectic.spSigns (pairedSympForm k n) :=
    (projEquiv hr).toMonoidHom.comp e.toMonoidHom
  have hψ : Function.Injective ψ := (projEquiv hr).injective.comp e.injective
  have hψrange : ψ.range.Normal := by
    rw [MonoidHom.range_eq_top.2 ((projEquiv hr).surjective.comp e.surjective)]
    infer_instance
  have hfour : ∀ K ∈ block J, ∃ V : Subgroup (sesqUnitaryGroup (pairedSympForm k n) ⧸
      ProjectiveSymplectic.spSigns (pairedSympForm k n)),
      V ≤ (centerQuotientImage L K).map ψ ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
    intro K hK
    obtain ⟨V, hVK, hVe, hVc⟩ :=
      exists_four_group_centerQuotientImage hV hK.1 ((le_blockGroup hK).trans hML) hodd
    exact ⟨V.map ψ, Subgroup.map_mono hVK, CFSG.IsElementaryAbelian.map ψ,
      by rw [Subgroup.card_map_of_injective hψ, hVc]⟩
  have hlocal : ∀ K ∈ block J, ∀ K' ∈ block J, K ≠ K' →
      ∀ t ∈ (centerQuotientImage L K').map ψ, orderOf t = 2 →
        CFSG.Assembly.IsComponentOf ((centerQuotientImage L K).map ψ)
          (centralizer ({t} : Set (sesqUnitaryGroup (pairedSympForm k n) ⧸
            ProjectiveSymplectic.spSigns (pairedSympForm k n)))) := by
    intro K hK K' hK' hKK' t ht ht2
    obtain ⟨w, hw, rfl⟩ := ht
    rw [orderOf_injective ψ hψ] at ht2
    obtain ⟨t₀, ht₀K, ht₀2, rfl⟩ := exists_involution_lift_of_odd_center hodd hw ht2
    have h := (isComponentOf_map_iff hψ).2 (hloc K hK K' hK' hKK' t₀ ht₀K ht₀2).2
    rw [map_centralizer_singleton_of_injective hψ] at h
    exact isComponentOf_of_normal_inf hψrange h
  exact ProjectiveSymplectic.odd_projective_symplectic_commuting_universal_pair_exclusion hp hp2 hf
    hk hr SymplecticFlag.finrank_standard SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate
    ⟨_, _, isQuasisimple_map_of_injective hψ (hπKq K₁ hK₁).1,
      isQuasisimple_map_of_injective hψ (hπKq K₂ hK₂).1,
      by rw [← Subgroup.map_commutator, (hcomm K₁ hK₁ K₂ hK₂ hne).2, Subgroup.map_bot],
      hfour K₁ hK₁, hfour K₂ hK₂, hlocal K₁ hK₁ K₂ hK₂ hne, hlocal K₂ hK₂ K₁ hK₁ (Ne.symm hne)⟩

end CFSG.LocalAnalysis.ComponentInitial
