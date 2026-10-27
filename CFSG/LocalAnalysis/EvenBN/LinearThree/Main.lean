module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.TwoSeven
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapQuasi
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergEvenBNRankTwoFrontier

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.Seitz77 (Datum)
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover (projRad)

theorem bnFamily_of_hyp_kProper_false
    (h : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (f : ℕ), Hyp G A f →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → False) :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 3 ≤ f ∧ LieModel X .PSL 3 2 f := by
  intro G _ _ _ hnonab hK L hL hcore S hS _ _ ⟨f, hf, hm⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := ComponentInitial.EvenResidual.isPGroup_two_center hL hcore
  by_contra hodd
  have hZ : center L = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rcases k with _ | k
    · exact Subgroup.card_eq_one.1 (by rw [hk, pow_zero])
    · exact (hodd (by rw [hk]; exact Nat.even_pow.2 ⟨even_two, by omega⟩)).elim
  let e : L ≃* L ⧸ center L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hmL : LieModel L .PSL 3 2 f := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm
  exact h G L f ⟨inferInstance, hnonab, hL, hZ, isCyclic_of_isCyclic_sylow S hS, hcore, hf, hmL⟩ hK

@[expose] def CaseAExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (f : ℕ), Hyp G A f →
    ∀ (d : Datum A) (V₁ V₂ Vi : Subgroup G), Radicals d.V V₁ V₂ (2 ^ f) → (Vi = V₁ ∨ Vi = V₂) →
    ∀ (w : WData d Vi (2 ^ f)) (K : Type) [Field K] [Finite K] (D : LeviData A Vi K),
      Nat.card K = 2 ^ f → w.CaseA f D.lev.range → False

@[expose] def CaseBSwapFactors : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (f : ℕ), Hyp G A f →
    ∀ (d : Datum A) (K : Type) [Field K] [Finite K] [CharP K 2] (F : Frame A d.V K),
      Nat.card K = 2 ^ f →
    ∀ (w₀ : WData d ((projRad K 0).map F.φ) (2 ^ f)) (w₁ : WData d ((projRad K 1).map F.φ) (2 ^ f)),
      w₀.CaseB (F.leviData 0).lev.range → w₁.CaseB (F.leviData 1).lev.range →
      ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
        G₁.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
        ∀ g : G, g⁻¹ * d.t * g ∈
            normalizer ((G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) →
          g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G)

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}


theorem Hyp.false_of_inputs (hL3 : LinearThreeExclusion27) (hG23 : G2ThreeExclusion27)
    (hA : CaseAExclusion) (hB : CaseBSwapFactors)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (h : Hyp G A f) : False := by
  obtain ⟨d⟩ := h.exists_datum
  obtain ⟨K, _, _, _, hKc, ⟨e⟩⟩ := h.exists_model
  obtain ⟨F⟩ := exists_frame e d.V_isSylow
  have hR : Radicals d.V ((projRad K 0).map F.φ) ((projRad K 1).map F.φ) (2 ^ f) :=
    hKc ▸ F.radicals
  obtain ⟨w₀⟩ := h.exists_WData d hR (Or.inl rfl)
  obtain ⟨w₁⟩ := h.exists_WData d hR (Or.inr rfl)
  rcases h.seitz27_of_certificates hL3 hG23 hK d hR (Or.inl rfl) w₀ (F.leviData 0) hKc with h₀ | h₀
  · exact hA G A f h d _ _ _ hR (Or.inl rfl) w₀ K (F.leviData 0) hKc h₀
  rcases h.seitz27_of_certificates hL3 hG23 hK d hR (Or.inr rfl) w₁ (F.leviData 1) hKc with h₁ | h₁
  · exact hA G A f h d _ _ _ hR (Or.inr rfl) w₁ K (F.leviData 1) hKc h₁
  obtain ⟨G₁, hq, h₁₂, huniq⟩ := hB G A f h d K F hKc w₀ w₁ h₀ h₁
  have : IsSimpleGroup G := h.simple
  exact SeitzReduction.F4Pilot.false_of_simple_of_swap_of_isQuasisimple d.sector.t_order hq h₁₂ rfl
    huniq

theorem ctt_bn_psl3_of_inputs (hL3 : LinearThreeExclusion27) (hG23 : G2ThreeExclusion27)
    (hA : CaseAExclusion) (hB : CaseBSwapFactors) :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 3 ≤ f ∧ LieModel X .PSL 3 2 f :=
  bnFamily_of_hyp_kProper_false fun _ _ _ _ _ h hK => h.false_of_inputs hL3 hG23 hA hB hK

end Certified

end CFSG.LocalAnalysis.EvenBN.LinearThree
