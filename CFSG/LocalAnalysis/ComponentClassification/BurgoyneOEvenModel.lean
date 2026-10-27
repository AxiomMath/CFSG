module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPairMat
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOOddInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSurjCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (conj_injective_of_mulEquiv)

variable {K : Type} [Field K] {d : ℕ}

theorem transPair_left_of_right {Q Q' : QuadraticForm K (Fin d → K)} (S : GL (Fin d) K)
    (ν : Kˣ) (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v)
    {g : similarityPairs Q} (hg : g.val.right = 1) :
    (transPair S ν hS g).val.left = S * g.val.left * S⁻¹ ∧ (transPair S ν hS g).val.right = 1 := by
  refine ⟨?_, hg⟩
  rw [transPair_left, hg, map_one, MulAut.one_apply]

theorem oκ_eq_pair {Q : QuadraticForm K (Fin d → K)} (hker : OKer Q) {g g' : similarityPairs Q}
    (hg' : g'.val.right = 1) (h : oκ Q g = oκ Q g') :
    g.val.right = 1 ∧ ∃ c : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) c * g'.val.left := by
  have h1 : oκ Q (g * g'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨hr, c, hc⟩ := hker _ h1
  have hinvl : (g'⁻¹).val.left = g'.val.left⁻¹ := by
    change (g'.val⁻¹).left = _
    rw [SemidirectProduct.inv_left, hg', inv_one, map_one, MulAut.one_apply]
  have hinvr : (g'⁻¹).val.right = 1 := by
    change (g'.val⁻¹).right = 1
    rw [SemidirectProduct.inv_right, hg', inv_one]
  have hgr : g.val.right = 1 := by
    have : (g * g'⁻¹).val.right = g.val.right * (g'⁻¹).val.right := rfl
    rw [hinvr, mul_one] at this
    rw [← this]
    exact hr
  refine ⟨hgr, c, ?_⟩
  have hl : (g * g'⁻¹).val.left = g.val.left * g'.val.left⁻¹ := by
    change (g.val * (g'⁻¹).val).left = _
    rw [SemidirectProduct.mul_left, hgr, map_one, MulAut.one_apply, hinvl]
  rw [hc, hl, inv_mul_cancel_right]

theorem exists_model {R : GL (Fin d) K} (hker : OKer (oQ R)) {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (htg : socleAction θ t = oκ _ g) {H R' : GL (Fin d) K}
    (hgram : (H : Matrix (Fin d) (Fin d) K)ᵀ * R * H = R') :
    ∃ (θ' : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R')))
      (g' : similarityPairs (oQ R')),
      g'.val.right = 1 ∧ g'.val.left = H⁻¹ * g.val.left * H ∧ socleAction θ' t = oκ _ g' ∧
      OKer (oQ R') ∧ OSurjX θ' t ∧
      (∀ (x : X) (gx : similarityPairs (oQ R)), socleAction θ x = oκ _ gx →
        gx.val.right = 1 → ∃ gx' : similarityPairs (oQ R'), socleAction θ' x = oκ _ gx' ∧
          gx'.val.right = 1 ∧ gx'.val.left = H⁻¹ * gx.val.left * H) ∧
      Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R')) →*
        MulAut (StatedProj (matrixDerived (oQ R')))) ∧
      (MulAut.conj : StatedProj (matrixDerived (oQ R')) →*
        MulAut (StatedProj (matrixDerived (oQ R')))).range ≤ (socleAction θ').range := by
  obtain ⟨hS, -, -⟩ := exists_transport_of_gram hgram hg1
  set θ' := θ.trans (oTransport H⁻¹ 1 hS) with hθ'
  have hker' := hker.transport H⁻¹ 1 hS
  have hT : ∀ (x : X) (gx : similarityPairs (oQ R)), socleAction θ x = oκ _ gx →
      socleAction θ' x = oκ _ (transPair H⁻¹ 1 hS gx) := by
    intro x gx hx
    rw [hθ', socleAction_trans, hx, oTransport_kappa]
  obtain ⟨hl, hr⟩ := transPair_left_of_right H⁻¹ 1 hS hg1
  refine ⟨θ', transPair H⁻¹ 1 hS g, hr, by rw [hl, inv_inv], hT t g htg, hker',
    hsurj.transport H⁻¹ 1 hS, fun x gx hx hgx => ?_,
    conj_injective_of_mulEquiv hsimple hnab θ', by
      rintro _ ⟨y, rfl⟩; exact conj_mem_range_socleAction _ y⟩
  obtain ⟨hl', hr'⟩ := transPair_left_of_right H⁻¹ 1 hS hgx
  exact ⟨_, hT x gx hx, hr', by rw [hl', inv_inv]⟩

end CFSG.ComponentClassification.Burgoyne.O
