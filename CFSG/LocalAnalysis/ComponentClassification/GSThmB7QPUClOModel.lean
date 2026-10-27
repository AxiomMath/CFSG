module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFormEven
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOForm

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy (plus_four_conjugacy)
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open scoped Pointwise

@[expose] def OCore : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f₀ f d : ℕ) (R : GL (Fin d) K),
    ringChar K ≠ 2 → p.Prime → Nat.card K = p ^ f₀ → 1 ≤ f → 5 ≤ p ^ f → 7 ≤ d →
    (R : Matrix (Fin d) (Fin d) K)ᵀ = R → OKer (oQ R) →
    IsSimpleGroup (StatedProj (matrixDerived (oQ R))) →
    ∀ (E : Subgroup (MulAut (StatedProj (matrixDerived (oQ R)))))
      (L : Subgroup (StatedProj (matrixDerived (oQ R)))) (t : StatedProj (matrixDerived (oQ R)))
      (J J₀ : Subgroup (StatedProj (matrixDerived (oQ R)))),
      BarData E L t J J₀ p f → (∀ e ∈ E, ∃ g : similarityPairs (oQ R), e = oκ _ g) → False

theorem congr_trans_apply {A B C : Type*} [Group A] [Group B] [Group C] (φ : A ≃* B) (ψ : B ≃* C)
    (α : MulAut A) : MulAut.congr (φ.trans ψ) α = MulAut.congr ψ (MulAut.congr φ α) := by
  ext x
  rfl

theorem exists_conj_mem_familyAut_plus_four {K : Type} [Field K] [Finite K]
    {E : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))} (hE : IsPGroup 2 E) :
    ∃ β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      ∀ e ∈ E, β⁻¹ * e * β ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) with hA
  set F := projectivePointFamily (coordinateQuadPlus 4 K) with hF
  have hcard := (plus_four_conjugacy (K := K)).2
  have hodd : ¬ 2 ∣ Nat.card (MulAction.orbit A F) := by
    rcases hcard with h | h <;> rw [h] <;> decide
  obtain ⟨⟨x, β, rfl⟩, hx⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card _ hodd
  refine ⟨β, fun e he => ?_⟩
  have h1 := congrArg Subtype.val (hx ⟨e, he⟩)
  change e • β • F = β • F at h1
  rw [mem_projectivePointFamilyAut_iff]
  change (β⁻¹ * e * β) • F = F
  rw [mul_smul, mul_smul, h1, inv_smul_smul]

theorem false_of_barConfig_pomegaOdd_of_core (hcore : OCore) {P : Type} [Group P] [Finite P]
    {n p f f₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hP : StatedClassicalModel P .POmegaOdd n p f₀) (h : BarConfig P p f p f) : False := by
  have hsimp := (ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaOdd
    P n p f₀ hP).2
  have hmod := hP
  obtain ⟨⟨-, -, hn, -⟩, F, _, _, hFc, ⟨e⟩⟩ := hP
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n F)
    (regular_coordinateQuadOdd n F h2 hn).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadOdd n F v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hker := (oKer_coordinateOdd hmod F hFc e).transport 1 1 hS₁
  have hsurj := (oSurj_coordinateOdd hmod F hFc e).transport 1 1 hS₁
  set θ := (coordinateOddWitnessEquiv F e).trans (oTransport 1 1 hS₁) with hθ
  obtain ⟨E, L, t, J, J₀, hd⟩ := h.exists_barData
  exact hcore F p f₀ f (2 * n + 1) R hF hp hFc hf h5 (by omega) hR hker θ.symm.isSimpleGroup _ _ _
    _ _ (hd.map θ) fun e' _ => hsurj e'

theorem false_of_barConfig_pomegaMinus_of_core (hcore : OCore) {P : Type} [Group P] [Finite P]
    {n p f f₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hP : StatedClassicalModel P .POmegaMinus n p f₀) (h : BarConfig P p f p f) : False := by
  have hsimp := (ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus
    P n p f₀ hP).2
  have hmod := hP
  obtain ⟨⟨-, -, hn⟩, F, _, _, hFc, b, c, hirr, ⟨e⟩⟩ := hP
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hn1 : 1 ≤ n := by omega
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n F hn1 b c)
    (regular_coordinateQuadMinus n F b c hn hirr).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadMinus n F hn1 b c v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hker := (oKer_coordinateMinus hmod F hFc b c hirr e).transport 1 1 hS₁
  have hsurj := (oSurj_coordinateMinus hmod F hFc b c hirr e).transport 1 1 hS₁
  set θ := (coordinateMinusWitnessEquiv F hn1 b c e).trans (oTransport 1 1 hS₁) with hθ
  obtain ⟨E, L, t, J, J₀, hd⟩ := h.exists_barData
  exact hcore F p f₀ f (2 * n) R hF hp hFc hf h5 (by omega) hR hker θ.symm.isSimpleGroup _ _ _ _
    _ (hd.map θ) fun e' _ => hsurj e'

theorem false_of_barConfig_pomegaPlus_of_core (hcore : OCore) {P : Type} [Group P] [Finite P]
    {n p f f₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hP : StatedClassicalModel P .POmegaPlus n p f₀) (h : BarConfig P p f p f) : False := by
  have hsimp := (ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
    P n p f₀ hP).2
  have hmod := hP
  obtain ⟨⟨-, -, hn⟩, F, _, _, hFc, ⟨e⟩⟩ := hP
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n F)
    (regular_coordinateQuadPlus n F (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadPlus n F v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hker := (oKer_coordinatePlus hmod F hFc e).transport 1 1 hS₁
  set Θ := oTransport 1 1 hS₁ with hΘ
  set θ := (coordinatePlusWitnessEquiv F e).trans Θ with hθ
  obtain ⟨E, L, t, J, J₀, hd⟩ := h.exists_barData
  have hd' := hd.map θ
  obtain ⟨β, hβ⟩ : ∃ β : MulAut (StatedProj (matrixDerived (oQ R))),
      ∀ e' ∈ E.map (MulAut.congr θ).toMonoidHom, ∃ g : similarityPairs (oQ R),
        β⁻¹ * e' * β = oκ _ g := by
    rcases Nat.lt_or_ge n 5 with h4 | h5'
    · obtain rfl : n = 4 := by omega
      obtain ⟨β₀, hβ₀⟩ := exists_conj_mem_familyAut_plus_four (K := F)
        (E := (E.map (MulAut.congr θ).toMonoidHom).map (MulAut.congr Θ.symm).toMonoidHom)
        (hd'.hE.map _)
      obtain ⟨β₁, hβ₁⟩ : ∃ β₁ : MulAut (StatedProj (matrixDerived (coordinateQuadPlus 4 F))),
          β₁ = β₀ := ⟨β₀, rfl⟩
      refine ⟨MulAut.congr Θ β₁, fun e' he' => ?_⟩
      have hmem := hβ₀ _ ⟨e', he', rfl⟩
      rw [coordinate_plus_family_eq_matrixImage hmod F hFc e] at hmem
      obtain ⟨g, hg⟩ := hmem
      have hg₁ : oκ _ g = β₁⁻¹ * MulAut.congr Θ.symm e' * β₁ := by rw [hβ₁]; exact hg
      refine ⟨transPair 1 1 hS₁ g, ?_⟩
      rw [← oTransport_kappa, ← hΘ, hg₁, map_mul, map_mul, map_inv]
      congr 1
      ext x
      simp
    · have hsurj := (oSurj_coordinatePlus hmod F hFc h5' e).transport 1 1 hS₁
      refine ⟨1, fun e' _ => ?_⟩
      obtain ⟨g, hg⟩ := hsurj e'
      exact ⟨g, by rw [inv_one, one_mul, mul_one]; exact hg⟩
  set θ' := θ.trans β.symm with hθ'
  refine hcore F p f₀ f (2 * n) R hF hp hFc hf h5 (by omega) hR hker θ'.symm.isSimpleGroup _ _ _
    _ _ (hd.map θ') ?_
  rintro _ ⟨e', he', rfl⟩
  obtain ⟨g, hg⟩ := hβ _ ⟨e', he', rfl⟩
  refine ⟨g, ?_⟩
  change MulAut.congr θ' e' = _
  rw [hθ', congr_trans_apply, ← hg]
  ext x
  rfl

end CFSG.ComponentClassification.GSThmB.QPUCl
