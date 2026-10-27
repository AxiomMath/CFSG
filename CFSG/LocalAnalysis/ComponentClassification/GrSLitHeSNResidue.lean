module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNConn
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGoldschmidt
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNEven

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

namespace Setting

variable {a : X} {L W K : Subgroup X} (h : Setting X a L W K)
include h

theorem mem_of_relIndex_eq_two
    (hMax : MaximalTwoComponentInputHe)
    (h64 : HeldSylowElementarySixtyFour) (hOut : HeldOuterInvolutionRank) {T : Subgroup X}
    (hTsyl : IsSylowTwoIn T (normalizer (W : Set X))) (haT : a ∈ T)
    (hT₁ : IsSylowTwoIn (T ⊓ normalizer (K : Set X))
      (normalizer (W : Set X) ⊓ normalizer (K : Set X)))
    {M₀ : Subgroup X} (hM₀ : M₀ ≤ normalizer (W : Set X))
    (hidx : M₀.relIndex (normalizer (W : Set X)) = 2) {t : X}
    (htM : t ∈ normalizer (W : Set X)) (ht2 : orderOf t = 2) : t ∈ M₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup X := h.simple
  obtain ⟨e₁⟩ := h.heldK
  have hGWB := h.gwTwoBalanced
  obtain ⟨A, -, hAe, hA64, hWA⟩ := h.wGroup_eq
  have hT2 := hTsyl.isPGroup
  have h1024 := h.card_inf_eq_of_isSylow e₁ hT₁
  have h3 := h.isThreeConnected hMax h64 hOut hT2 hTsyl.1 haT hT₁
  have hTsylA : IsSylowTwoIn T (normalizer (wGroup A : Set X)) := by rw [hWA]; exact hTsyl
  obtain ⟨⟨P₀, hP₀⟩, hfus⟩ :=
    sylow_and_fusion_of_threeConnected hGWB hAe (by omega) hTsylA h3
  have hidx' : (M₀.subgroupOf (normalizer (W : Set X))).index = 2 := hidx
  have hmul : ∀ x ∈ normalizer (W : Set X), ∀ y ∈ normalizer (W : Set X),
      (x * y ∈ M₀ ↔ (x ∈ M₀ ↔ y ∈ M₀)) := fun x hx y hy => by
    have h1 := Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    simpa [mem_subgroupOf] using h1
  have hconj : ∀ m ∈ normalizer (W : Set X), ∀ x ∈ M₀, m * x * m⁻¹ ∈ M₀ := by
    intro m hm x hx
    have hxM := hM₀ hx
    rw [hmul _ (mul_mem hm hxM) _ (inv_mem hm), hmul _ hm _ hxM]
    have h1 := hmul m hm m⁻¹ (inv_mem hm)
    rw [mul_inv_cancel] at h1
    have h2 := h1.mp (one_mem _)
    exact ⟨fun h3 => h2.mp (h3.mpr hx), fun h3 => ⟨fun _ => hx, fun _ => h2.mpr h3⟩⟩
  have key : ∀ s ∈ T, orderOf s = 2 → s ∈ M₀ := by
    intro s hsT hs2
    by_contra hsM₀
    have hss : s * s = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
    have hU : (T ⊓ M₀).relIndex T = 2 := by
      rw [relIndex_eq_two_iff]
      refine ⟨s, hsT, fun b hb => ?_⟩
      have h1 := hmul b (hTsyl.1 hb) s (hTsyl.1 hsT)
      simp only [mem_inf, hb, mul_mem hb hsT, true_and]
      by_cases hbM : b ∈ M₀
      · exact Or.inr ⟨hbM, fun h2 => hsM₀ ((h1.mp h2).mp hbM)⟩
      · exact Or.inl ⟨h1.mpr ⟨fun h2 => absurd h2 hbM, fun h2 => absurd h2 hsM₀⟩, hbM⟩
    rcases goldschmidtTransferInput_holds X P₀ s (hP₀ ▸ hsT) hs2 with hall | hres
    · obtain ⟨g, hgU, hgext⟩ := hall (T ⊓ M₀) (by rw [hP₀]; exact inf_le_left)
        (by rw [hP₀]; exact hU)
      rw [hP₀] at hgext
      obtain ⟨m, hmM, hm⟩ := hfus (g⁻¹ * s * g) s hsT hgext ⟨g, rfl⟩
        (h.three_le_pRank_centralizer e₁ h64 hOut hT2 hTsyl.1 h1024 hsT hss)
      rw [hWA] at hmM
      apply hsM₀
      have h1 := hconj m⁻¹ (inv_mem hmM) _ (mem_inf.mp hgU).2
      rwa [inv_inv, ← hm] at h1
    · exact hres (mem_twoResidualOf_top' h.nonabelian s)
  obtain ⟨n, hnM, hnt⟩ := hTsyl.exists_conj_le (zpowers_le.mpr htM) (isPGroup_zpowers ht2)
  have hnt2 : orderOf (n * t * n⁻¹) = 2 := by
    rw [← ht2]
    exact (SemiconjBy.orderOf_eq n (show n * t = n * t * n⁻¹ * n by group)).symm
  have h1 := hconj n⁻¹ (inv_mem hnM) _ (key _ (hnt t (mem_zpowers t)) hnt2)
  rwa [show n⁻¹ * (n * t * n⁻¹) * n⁻¹⁻¹ = t by group] at h1

end Setting

@[expose] def HeldSingleNormalResidue : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (a : X) (L W K T : Subgroup X),
    Setting X a L W K → EvenSylow X a W K T → IsThreeConnected T →
    (∃ P : Sylow 2 X, (P : Subgroup X) = T) →
    (∀ M₀ : Subgroup X, M₀ ≤ normalizer (W : Set X) →
      M₀.relIndex (normalizer (W : Set X)) = 2 →
      ∀ t ∈ normalizer (W : Set X), orderOf t = 2 → t ∈ M₀) → False

theorem heldSingleNormalEvenStep_of_residue
    (hMax : MaximalTwoComponentInputHe) (h64 : HeldSylowElementarySixtyFour)
    (hOut : HeldOuterInvolutionRank) (hres : HeldSingleNormalResidue) :
    HeldSingleNormalEvenStep := by
  intro X _ _ a L W K T h hE
  have h3 := h.isThreeConnected hMax h64 hOut hE.isSylow.isPGroup hE.isSylow.1 hE.mem
    hE.isSylow_normalizer
  obtain ⟨A, -, hAe, hA64, hWA⟩ := h.wGroup_eq
  have hTsylA : IsSylowTwoIn T (normalizer (wGroup A : Set X)) := by rw [hWA]; exact hE.isSylow
  obtain ⟨hP, -⟩ := sylow_and_fusion_of_threeConnected h.gwTwoBalanced hAe (by omega) hTsylA h3
  exact hres X a L W K T h hE h3 hP fun M₀ hM₀ hidx t htM ht2 =>
    h.mem_of_relIndex_eq_two hMax h64 hOut hE.isSylow hE.mem hE.isSylow_normalizer hM₀ hidx htM
      ht2

end CFSG.ComponentClassification.GrSLit.HeSN
