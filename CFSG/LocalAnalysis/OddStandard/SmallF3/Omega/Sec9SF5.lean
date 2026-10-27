module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SF4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SF3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B : Subgroup G}

private theorem sec9f_quot_of_iso {X Y F : Type} [Group X] [Group Y] [Group F] (ρ : X →* Y)
    (H : Subgroup Y) (hH : ρ.range = H) (e : ↥H ≃* F) :
    ∃ φ : X →* F, Function.Surjective φ ∧ φ.ker = ρ.ker := by
  refine ⟨((e.toMonoidHom).comp (MulEquiv.subgroupCongr hH).toMonoidHom).comp ρ.rangeRestrict,
    ?_, ?_⟩
  · exact (e.surjective.comp (MulEquiv.subgroupCongr hH).surjective).comp
      ρ.rangeRestrict_surjective
  · rw [MonoidHom.ker_comp_of_injective _ _
      (e.injective.comp (MulEquiv.subgroupCongr hH).injective), MonoidHom.ker_rangeRestrict]

theorem sec9f_exists_E1 (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB8 : Asc82Sec8B)
    (hT : Asc82Tab9M) (h6 : Asc82Tab6M) (hN : Asc82NormA6)
    (hctx : Sec9Choice G t L S z g B t₀) : ∃ E1 : Subgroup G, Sec9E1 G t L S z g B t₀ E1 := by
  have hc : Sec9Ctx G t L S z g B t₀ := hctx.toSec9Ctx
  obtain ⟨τ, hτ, hker, hK0⟩ := sec9f_exists_tau h36 h68 hB8 hT hctx
  have htop : τ.range = ⊤ :=
    (sec9f_range_bot_or_top hT h6 hc τ hτ).resolve_left
      (sec9f_range_ne_bot h36 h68 hB8 hT h6 hctx τ hτ)
  obtain ⟨E1, hAE1, hE1C, hE1O, φ, hφs, hφk⟩ := sec9f_E1_core hc τ hker hK0 htop
  obtain ⟨e⟩ := sec9f_equiv_E16 hc.B_e16
  obtain ⟨ρ, hρker, hρrange⟩ := sec9f_rho (X := centMod (Asub9 t t₀ B) B) (B := B)
    (fun x hx => hx.1)
  have hnorm : ((E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)).subgroupOf
      (centMod (Asub9 t t₀ B) B)).Normal := by
    rw [hE1O, ← hρker]
    exact MonoidHom.normal_ker ρ
  have hkerN : ((E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)).subgroupOf
      (centMod (Asub9 t t₀ B) B)) = ρ.ker := by
    rw [hE1O, hρker]
  refine ⟨E1, ⟨hctx, hAE1, hE1C.trans inf_le_left, ?_, hnorm, ?_⟩⟩
  · refine ⟨e.toMonoidHom.comp φ, e.surjective.comp hφs, ?_⟩
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, hφk]
  · rcases sec9f_top_iso h36 hT h6 hN hc τ hτ htop with ⟨⟨e2⟩⟩ | ⟨⟨e2⟩⟩
    · obtain ⟨ψ, hψs, hψk⟩ := sec9f_quot_of_iso ρ _ hρrange e2
      exact Or.inl ⟨ψ, hψs, by rw [hψk, hkerN]⟩
    · obtain ⟨ψ, hψs, hψk⟩ := sec9f_quot_of_iso ρ _ hρrange e2
      exact Or.inr ⟨ψ, hψs, by rw [hψk, hkerN]⟩

theorem asc82Fink9E1_of (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB8 : Asc82Sec8B)
    (hT : Asc82Tab9M) (h6 : Asc82Tab6M) (hN : Asc82NormA6) : Asc82Fink9E1 := by
  intro G _ _ t L S z g B t₀ hctx
  exact sec9f_exists_E1 h36 h68 hB8 hT h6 hN hctx

end CFSG.OddStandard.SmallF3.Omega
