module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsL44Std
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsKinds
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsStd

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ABGLocalTools
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd (msigma sigmaSL pstd)
open scoped MatrixGroups

theorem card_SL_four_two : Nat.card SL(4, ZMod 2) = 20160 := by
  rw [card_SL_eq (by norm_num), Nat.card_eq_fintype_card, ZMod.card]
  decide

theorem l44Input_of_extend
    (hext : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
      ∀ θ : msigma F ≃* msigma F, ∃ Θ : MulAut SL(4, F),
        (∀ x, Θ (sigmaSL F x) = sigmaSL F (Θ x)) ∧ ∀ A : msigma F, Θ (A : SL(4, F)) = θ A) :
    YamadaEnd.L44Input := by
  intro F _ _ _ hF X _ _ L₁ ψ hψ hker t htt htN χ P₁ hP₁ hχP
  have hker0 : ψ.ker = ⊥ := le_bot_iff.mp (hker.trans (center_SL_four_eq_bot hF).le)
  have hCcard : Nat.card (L₁ ⊓ centralizer ({t} : Set X) : Subgroup X) = 25920 :=
    (Nat.card_congr χ.toEquiv).symm.trans (card_msigma hF)
  obtain ⟨A, σ, ε, hε, hA, hcases⟩ := exists_cases (by norm_num) hF ψ hψ hker htN htt
  rcases hcases with ⟨rfl, -⟩ | ⟨hσ1, hσ, H, hH⟩
  ·
    exfalso
    obtain ⟨Q, hQ, hQ2, hQcard⟩ := exists_twoSubgroup_of_linear hF (Or.inl rfl) rfl ψ hker htt
      hε hA
    have hdvd : Nat.card Q ∣ 25920 := hCcard ▸ card_dvd_of_le hQ
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hk] at hdvd hQcard
    rw [hF, show (4 : ℕ) ^ (2 * 2) = 2 ^ 8 by norm_num] at hQcard
    have h8 : 8 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hQcard
    have h := (pow_dvd_pow 2 h8).trans hdvd
    norm_num at h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    exfalso
    obtain ⟨θ, hθ, hrange⟩ := exists_field_centralizer (by norm_num) ψ hψ hker hσ hH
    have h := Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv
    rw [hrange, hCcard, card_SL_four_two] at h
    norm_num at h
  ·
    obtain ⟨φ₀, hφ₀, hφ₀ker, hact⟩ := exists_std_graphField hF ψ hψ hker hσ hH
    have hσeq : σ = frobeniusEquiv F 2 := RingEquiv.ext fun c => by
      rw [hσ, frobeniusEquiv_apply, frobenius_def]
    subst hσeq
    have hker0' : φ₀.ker = ⊥ := hφ₀ker.trans hker0
    have hφ₀inj : Function.Injective φ₀ := (MonoidHom.ker_eq_bot_iff φ₀).mp hker0'
    have hC : L₁ ⊓ centralizer ({t} : Set X) = (msigma F).map (L₁.subtype.comp φ₀) := by
      rw [centralizer_eq_slUnitary hF (by norm_num) φ₀ hφ₀ (hker0' ▸ bot_le) hσ hact,
        msigma_eq_slUnitary]
    rw [← sigmaSL_eq_stdSL] at hact
    have hinj : Function.Injective (L₁.subtype.comp φ₀) := L₁.subtype_injective.comp hφ₀inj
    obtain ⟨e₀, he₀apply⟩ : ∃ e₀ : msigma F ≃* (L₁ ⊓ centralizer ({t} : Set X) : Subgroup X),
        ∀ B : msigma F, (e₀ B : X) = (φ₀ (B : SL(4, F)) : X) :=
      ⟨((msigma F).equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr hC.symm),
        fun B => rfl⟩
    obtain ⟨Θ, hΘσ, hΘ⟩ := hext F hF (χ.trans e₀.symm)
    set φ := (L₁.subtype.comp φ₀).comp Θ.toMonoidHom with hφdef
    have hφfix : ∀ B : msigma F, φ (B : SL(4, F)) = χ B := by
      intro B
      change (φ₀ (Θ (B : SL(4, F))) : X) = χ B
      rw [hΘ, ← he₀apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have hφ₀surj : Function.Surjective (φ₀.comp Θ.toMonoidHom) :=
      hφ₀.comp Θ.surjective
    refine ⟨φ, hinj.comp Θ.injective, ?_, hφfix, fun x => ?_, ?_⟩
    · rw [hφdef, MonoidHom.comp_assoc, MonoidHom.range_comp,
        MonoidHom.range_eq_top.mpr hφ₀surj, ← MonoidHom.range_eq_map, range_subtype]
    · change t * (φ₀ (Θ x) : X) * t⁻¹ = φ₀ (Θ (sigmaSL F x))
      rw [hact, hΘσ]
    ·
      set φL := φ₀.comp (Θ.toMonoidHom.comp (cJ F).toMonoidHom) with hφL
      have hφLsurj : Function.Surjective φL := hφ₀.comp (Θ.surjective.comp (cJ F).surjective)
      have hv : cJ F (u₄ F) ∈ msigma F := cJ_mem_msigma (F := F) (u₄_mem_msigma (F := F))
      have hvP : cJ F (u₄ F) ∈ pstd F := by
        rw [← pstd_eq]
        exact ⟨u₄ F, u₄_mem_unitriangular, rfl⟩
      have huP : (φL (u₄ F) : X) ∈ P₁ := by
        have := hχP ⟨_, hv⟩ hvP
        rwa [← hφfix] at this
      have hP := eq_map_unitriangular (n := 4) hF (by norm_num) φL hφLsurj u₄_mem_unitriangular
        u₄_reg hP₁ huP
      rw [hP, ← pstd_eq, Subgroup.map_map]
      rfl

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
