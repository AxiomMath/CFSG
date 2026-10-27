module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanGluing
public import CFSG.GH74.Uniqueness.Bender.Dickson
public import CFSG.StronglyEmbedded.SteinbergBKSylowInheritance

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.Blueprint.NativeSporadic (IsSporadic)

theorem not_hasStronglyEmbedded_of_normalizers {L : Type} [Group L] [Finite L]
    (h : ∀ R : Sylow 2 L, ∃ F₀ F₁ : Subgroup L, F₀ ≤ R ∧ F₁ ≤ R ∧ IsElemTwo F₀ ∧
      4 ≤ Nat.card F₀ ∧ F₁ ≠ ⊥ ∧
      (⊤ : Subgroup L) ≤ normalizer (F₀ : Set L) ⊔ normalizer (F₁ : Set L) ⊔ pPrimeCore 2 L) :
    ¬ FooteLit.HasStronglyEmbedded L := by
  rintro ⟨M, hM⟩
  obtain ⟨S⟩ := (Sylow.nonempty (p := 2) (G := ↥M) : Nonempty (Sylow 2 ↥M))
  obtain ⟨R, hR⟩ :=
    (CFSG.StronglyEmbedded.SteinbergBK.strongly_embedded_sylow_inheritance hM).1 S
  have hRM : (R : Subgroup L) ≤ M := by
    rw [hR]
    exact map_subtype_le _
  obtain ⟨F₀, F₁, hF0R, hF1R, hF0e, hF04, hF1ne, htop⟩ := h R
  have hF0M : F₀ ≤ M := hF0R.trans hRM
  have hF1M : F₁ ≤ M := hF1R.trans hRM
  have hF02 : IsPGroup 2 F₀ := R.isPGroup'.to_le hF0R
  have hF12 : IsPGroup 2 F₁ := R.isPGroup'.to_le hF1R
  have hF0ne : F₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hF04
    omega
  have hN0 : normalizer (F₀ : Set L) ≤ M :=
    CFSG.GH74.Uniqueness.Bender.IsStronglyEmbedded.normalizer_le hM hF0M hF02 hF0ne
  have hN1 : normalizer (F₁ : Set L) ≤ M :=
    CFSG.GH74.Uniqueness.Bender.IsStronglyEmbedded.normalizer_le hM hF1M hF12 hF1ne
  have hOleM : pPrimeCore 2 L ≤ M := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hElem : CFSG.Open.IsElemAbelian 2 F₀ :=
      ⟨⟨⟨fun x y => Subtype.ext (hF0e.1 x x.2 y y.2)⟩⟩, fun x hx => by
        rw [pow_two]
        exact hF0e.2 x hx⟩
    have hlarge : 2 ^ (1 + 1) ≤ Nat.card F₀ := by
      norm_num
      exact hF04
    have hNorm : F₀ ≤ normalizer (pPrimeCore 2 L : Set L) := by
      intro x _
      rw [Subgroup.normalizer_eq_top_iff.mpr (pPrimeCore_normal (p := 2) (G := L))]
      exact mem_top x
    have hCop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 L)) :=
      pPrimeCore_coprime_card (p := 2) (G := L)
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation
      (GroupType := L) 2 1 Nat.prime_two F₀ (pPrimeCore 2 L) hElem hlarge hNorm hCop
    rw [← hgen]
    apply iSup_le
    intro B
    apply iSup_le
    intro hB
    obtain ⟨hBle, hBcard⟩ := (by simpa [CFSG.Open.signalizerFunctorEk] using hB)
    have hBcard' : Nat.card B = 2 := by simpa using hBcard
    have hB2 : IsPGroup 2 B :=
      IsPGroup.of_card (p := 2) (n := 1) (by rw [hBcard']; norm_num)
    have hBne : B ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hBcard'
      omega
    have hBM : B ≤ M := hBle.trans hF0M
    have hNB : normalizer (B : Set L) ≤ M :=
      CFSG.GH74.Uniqueness.Bender.IsStronglyEmbedded.normalizer_le hM hBM hB2 hBne
    exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (B : Set L)).trans hNB)
  have htopM : (⊤ : Subgroup L) ≤ M := by
    refine htop.trans ?_
    exact sup_le (sup_le hN0 hN1) hOleM
  exact hM.1 (top_le_iff.mp htopM)


theorem not_hasStronglyEmbedded_of_on
    {H : Type} [Group H] [Finite H]
    (hON : IsSporadic (H ⧸ pPrimeCore 2 H) .ONan) : ¬ FooteLit.HasStronglyEmbedded H := by
  refine not_hasStronglyEmbedded_of_normalizers fun R => ?_
  obtain ⟨F₀, F₁, hF0R, hF1R, hF0e, hF08, -, hF18, htop⟩ := exists_eight_normalizers_top_of_on hON R
  refine ⟨F₀, F₁, hF0R, hF1R, hF0e, by omega, fun hbot => ?_, htop⟩
  rw [hbot, Subgroup.card_bot] at hF18
  omega

end CFSG.ComponentClassification.GrSLit.L34Sec5S
