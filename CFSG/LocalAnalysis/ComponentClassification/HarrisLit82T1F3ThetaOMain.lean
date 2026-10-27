module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Conj
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4T2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaOEven
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaOOdd
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.Blueprint

theorem pow_eq_one_of_mem_oddCentralizerCore_POmegaPlus (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {n p f : ℕ} (hp2 : p ≠ 2)
    (hn5 : 5 ≤ n) (hL : LieModel (GeneralizedFitting.subgroup X) .POmegaPlus n p f) (t : X)
    (ht : orderOf t = 2) {y : X} (hy : y ∈ oddCentralizerCore t) :
    y ^ ((p ^ f) ^ 2 - 1) = 1 := by
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hmod := hc
    obtain ⟨⟨hp, hf, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have hker₀ := oKer_coordinatePlus hmod K hKc e
    have hsurj₀ := oSurj_coordinatePlus hmod K hKc hn5 e
    obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n K)
      (regular_coordinateQuadPlus n K (by omega)).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K) : Matrix _ _ K) *ᵥ v) =
        ((1 : Kˣ) : K) * coordinateQuadPlus n K v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := hker₀.transport 1 1 hS₁
    have hsurj := hsurj₀.transport 1 1 hS₁
    set θ := (coordinatePlusWitnessEquiv K e).trans (oTransport 1 1 hS₁) with hθ
    obtain ⟨g, hg⟩ := hsurj (socleAction θ t)
    rw [← hKc]
    by_cases hσ : g.val.right = 1
    · exact inner_even_pow_eq_one hK hp hKc (by omega) hR hker hsimple hnab θ
        (hsurj.surjX θ t) ht hσ hg hy
    · rw [field_oddCentralizerCore_eq_bot hK (by omega) hp hf hKc hR hker hsimple hnab θ
        (hsurj.surjX θ t) ht hσ hg, mem_bot] at hy
      rw [hy, one_pow]
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

theorem pow_eq_one_of_mem_oddCentralizerCore_POmegaMinus (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {n p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .POmegaMinus n p f) (t : X)
    (ht : orderOf t = 2) {y : X} (hy : y ∈ oddCentralizerCore t) :
    y ^ ((p ^ f) ^ 2 - 1) = 1 := by
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hmod := hc
    obtain ⟨⟨hp, hf, hn⟩, K, _, _, hKc, b, c, hirr, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have hn1 : 1 ≤ n := by omega
    have hker₀ := oKer_coordinateMinus hmod K hKc b c hirr e
    have hsurj₀ := oSurj_coordinateMinus hmod K hKc b c hirr e
    obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n K hn1 b c)
      (regular_coordinateQuadMinus n K b c hn hirr).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K) : Matrix _ _ K) *ᵥ v) =
        ((1 : Kˣ) : K) * coordinateQuadMinus n K hn1 b c v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := hker₀.transport 1 1 hS₁
    have hsurj := hsurj₀.transport 1 1 hS₁
    set θ := (coordinateMinusWitnessEquiv K hn1 b c e).trans (oTransport 1 1 hS₁) with hθ
    obtain ⟨g, hg⟩ := hsurj (socleAction θ t)
    rw [← hKc]
    by_cases hσ : g.val.right = 1
    · exact inner_even_pow_eq_one hK hp hKc hn hR hker hsimple hnab θ
        (hsurj.surjX θ t) ht hσ hg hy
    · rw [field_oddCentralizerCore_eq_bot hK (by omega) hp hf hKc hR hker hsimple hnab θ
        (hsurj.surjX θ t) ht hσ hg, mem_bot] at hy
      rw [hy, one_pow]
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

theorem pow_eq_one_of_mem_oddCentralizerCore_POmegaPlus4 (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .POmegaPlus 4 p f) (t : X)
    (ht : orderOf t = 2) {y : X} (hy : y ∈ oddCentralizerCore t) :
    y ^ ((p ^ f) ^ 2 - 1) = 1 := by
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hmod := hc
    obtain ⟨⟨hp, hf, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have hker₀ := oKer_coordinatePlus hmod K hKc e
    set θ₀ := coordinatePlusWitnessEquiv K e with hθ₀
    have hψ₀ := socleAction_injective hsimple hnab θ₀
    obtain ⟨α, hαt, hαY⟩ := d4_triality_reduction burgoyneD4TrialityConjInput_holds
      burgoyneD4TrialityOddCoreInput_holds hK (B := (socleAction θ₀).range)
      (by rintro _ ⟨y, rfl⟩; exact conj_mem_range_socleAction _ y) ⟨t, rfl⟩
      (by rw [orderOf_injective _ hψ₀ t]; exact ht)
    have hfam := coordinate_plus_family_eq_matrixImage hmod K hKc e
    have hsemi : ∀ β ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K),
        ∃ g : similarityPairs (coordinateQuadPlus 4 K), β = oκ _ g := by
      intro β hβ
      rw [hfam] at hβ
      obtain ⟨g, hg⟩ := hβ
      exact ⟨g, hg.symm⟩
    obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus 4 K)
      (regular_coordinateQuadPlus 4 K (by omega)).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * 4)) K) : Matrix _ _ K) *ᵥ v) =
        ((1 : Kˣ) : K) * coordinateQuadPlus 4 K v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := hker₀.transport 1 1 hS₁
    set θ := (θ₀.trans α).trans (oTransport 1 1 hS₁) with hθ
    have key : ∀ x, socleAction θ x =
        MulAut.congr (oTransport 1 1 hS₁) (α * socleAction θ₀ x * α⁻¹) := fun x => by
      ext y
      rfl
    obtain ⟨g₁, hg₁⟩ := hsemi (α * socleAction θ₀ t * α⁻¹) hαt
    have hg : socleAction θ t = oκ _ (transPair 1 1 hS₁ g₁) :=
      calc socleAction θ t = MulAut.congr (oTransport 1 1 hS₁) (α * socleAction θ₀ t * α⁻¹) :=
            key t
        _ = MulAut.congr (oTransport 1 1 hS₁) (oκ _ g₁) := congrArg _ hg₁
        _ = oκ _ (transPair 1 1 hS₁ g₁) := oTransport_kappa 1 1 hS₁ g₁
    have hsurj : OSurjX θ t := by
      intro x hx
      have hmem : socleAction θ₀ x ∈ oddCoreIn (socleAction θ₀).range (socleAction θ₀ t) := by
        rw [← map_oddCentralizerCore_of_injective hψ₀]
        exact ⟨x, hx, rfl⟩
      obtain ⟨g, hgx⟩ := hsemi _ (hαY _ hmem)
      exact ⟨transPair 1 1 hS₁ g, (key x).trans ((congrArg _ hgx).trans
        (oTransport_kappa 1 1 hS₁ g))⟩
    rw [← hKc]
    by_cases hσ : (transPair 1 1 hS₁ g₁).val.right = 1
    · exact inner_even_pow_eq_one hK hp hKc le_rfl hR hker hsimple hnab θ hsurj ht hσ hg hy
    · rw [field_oddCentralizerCore_eq_bot hK (by omega) hp hf hKc hR hker hsimple hnab θ hsurj
        ht hσ hg, mem_bot] at hy
      rw [hy, one_pow]
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.O
