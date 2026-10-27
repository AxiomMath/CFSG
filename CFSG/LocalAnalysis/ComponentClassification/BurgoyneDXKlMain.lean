module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrMain
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Kl

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation (sq_val)
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj

variable {K : Type} [Field K]

theorem false_of_k2 [Finite K] (hK : ringChar K ≠ 2) {n : ℕ} (hn : 5 ≤ n) {ℓ e : ℕ}
    (hℓ : ℓ.Prime) (he : 1 ≤ e) (hKc : Nat.card K = ℓ ^ e) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R) (hker : OKer (oQ R))
    {M : Subgroup (GL (Fin (2 * n)) K)} (hd : K2Data R M) {gs : similarityPairs (oQ R)}
    (hss : oκ _ (gs * gs) = 1) (hs1 : oκ _ gs ≠ 1)
    (hQs : (M.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ gs))
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
      (autFixed (oκ _ gs)))) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  by_cases hσ : gs.val.right = 1
  · exact false_of_k2_inner hK hℓ hKc hn hR hker hd hσ hss hs1 hQs hQc
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hℓ2 : ℓ ≠ 2 := by rw [← ringChar.eq K ℓ]; exact hK
  obtain ⟨hσ2', c, hc⟩ := hker _ hss
  have hσ2 : gs.val.right ^ 2 = 1 := by rw [← (sq_val _ gs).2]; exact hσ2'
  have hc' : gs.val.left * glFieldAut (Fin (2 * n)) K gs.val.right gs.val.left =
      GeneralLinearGroup.scalar (Fin (2 * n)) c := by rw [← (sq_val _ gs).1, hc]
  obtain ⟨e', hu, hσ'⟩ := exists_unitaryFieldData_of_involution hℓ he hKc hσ2 hσ
  obtain ⟨wF, hwF, S, ν, hS, heq⟩ :=
    exists_field_transport hu hℓ2 h2 (by omega) hR hσ' hc'
  have hd' := hd.transport S ν hS
  obtain ⟨hQs', hQc'⟩ := transport_comp hd.le S ν hS hQs hQc
  rw [heq] at hQs' hQc'
  exact false_of_k2_field hu hK hℓ2 (by omega) hwF hd' hQs' hQc'

end CFSG.ComponentClassification.Burgoyne.DX.Kl
