module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOPcCore
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOOddInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOAntiComp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenOrth2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOUnitComp

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O

variable {K : Type} [Field K] [Finite K]

theorem ClO.commute_pc (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hKc : Nat.card K = ℓ ^ e) {n : ℕ} (hn : 4 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R)) (hsurj : OSurj (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1) {c : K} (hc : c ≠ 0)
    (hA2 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left = c • 1)
    (hAR : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R =
      (-1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨H₁, hgram₁, hAH₁⟩ := exists_pc_basis hK hR hc hA2 hAR (fun _ => 1)
    (fun _ => one_ne_zero)
  obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = CatalogueBGraphForm.glTranspose (2 * n) K H₁ * R * H₁ :=
    ⟨_, rfl⟩
  have hgramR₁ : (H₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * H₁ = R₁ := by
    rw [hR₁]
    simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
  have hR₁m : (R₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)) := by
    rw [← hgramR₁, hgram₁]
    simp only [one_smul]
    rfl
  obtain ⟨hS, hg₁l, hg₁1⟩ := exists_transport_of_gram hgramR₁ hg1
  have hg₁A : ((transPair H₁⁻¹ 1 hS g).val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat c) := by
    rw [hg₁l, Units.val_mul, Units.val_mul]
    exact inv_mul_mul_eq hAH₁
  have hcd₁ : CompData ⁅isoCent R₁ (transPair H₁⁻¹ 1 hS g).val.left,
      isoCent R₁ (transPair H₁⁻¹ 1 hS g).val.left⁆ := by
    by_cases hsq : IsSquare c
    · obtain ⟨s, hs⟩ := hsq
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hc (by rw [hs, mul_zero])
      have hcs : c = s ^ 2 := by rw [hs, sq]
      exact compData_anti h2 hs0 (by omega) (by rw [hR₁m, hcs]) (by rw [hg₁A, hcs])
    · exact compData_unit hK hsq hℓ hKc (by omega) hR₁m hg₁A
  refine commute_of_congr (oTransport H₁⁻¹ 1 hS) (fun R' hR'odd hR'i hR'c => ?_) hRodd hRi hRc
  rw [oTransport_kappa] at hR'i hR'c
  have hker₁ := hker.transport H₁⁻¹ 1 hS
  have hsurj₁ := hsurj.transport H₁⁻¹ 1 hS
  have hinj₁ := ClO.conj_injective_of_mulEquiv (oTransport H₁⁻¹ 1 hS) hinj
  have hform : ∀ y ∈ R', ∃ a : similarityPairs (oQ R₁), y = oκ _ a ∧ a.val.right = 1 ∧
      ∃ x z : K, (a.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
        x • 1 + z • blkDiag n (jMat c) := by
    intro y hy
    obtain ⟨a, rfl⟩ := hsurj₁ y
    obtain ⟨hr, x, z, hl⟩ := ClO.pc_core hK (by omega) hc hR₁m hker₁ hinj₁ hg₁1 hg₁A hcd₁
      hR'odd hR'i hR'c hy
    exact ⟨a, rfl, hr, x, z, hl⟩
  intro r₁ h₁ r₂ h₂
  obtain ⟨a, rfl, ha, x₁, z₁, hal⟩ := hform r₁ h₁
  obtain ⟨b, rfl, hb, x₂, z₂, hbl⟩ := hform r₂ h₂
  exact ClO.commute_lin ha hb hal hbl

end CFSG.ComponentClassification.Foote5.OddLieCore
