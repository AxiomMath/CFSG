module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrAsm
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrLift
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Dr

open Module Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.B
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

attribute [local instance] GeneralizedFitting.normal

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]

theorem exc_false_of_facts {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {F : Type} [Field F] [Finite F] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP F ℓ] (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hKc : Nat.card F = ℓ ^ f) {σ : Type} [Fintype σ]
    [DecidableEq σ] {Q₀ : QuadraticForm F (σ → F)} {Q0 : (σ → F) → F} (hS : SpinFacts Q₀ Q0)
    {d : ℕ} (hd5 : 5 ≤ d) (eσ : σ ≃ Fin d) {R : GL (Fin d) F}
    (hR : (R : Matrix (Fin d) (Fin d) F)ᵀ = R) (hker : OKer (oQ R)) (hsurj : OSurj (oQ R))
    (hS₁ : ∀ v, oQ R ((1 : GL (Fin d) F).val *ᵥ v) = ((1 : Fˣ) : F) * reindexQuadraticForm eσ Q₀ v)
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* StatedProj (matrixDerived (oQ R)))
    (hneg : ∀ x₀ : spinGroup Q₀, x₀ ∈ center (spinGroup Q₀) → orderOf x₀ = 2 →
      @PropBHypII (spinGroup Q₀) _ hS.finite x₀ → x₀ = negOneR hS)
    {g : similarityPairs (oQ R)}
    (hg : socleAction θ ((rhoZ K).rangeRestrict t) = oκ _ g)
    (hσ : g.val.right = 1)
    (hpc : (g.val.left : Matrix (Fin d) (Fin d) F)ᵀ * R =
      (-1 : F) • ((R : Matrix (Fin d) (Fin d) F) * g.val.left)) : False := by
  have : Finite (spinGroup Q₀) := hS.finite
  have : Group.IsPerfect (spinGroup Q₀) := hS.perfect
  obtain ⟨hq, hM4, ht, -, -, s, hs2, hst, -, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2, hprop⟩ := id hH
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  obtain ⟨p₁, n₁, hp₁f, hp₁, hn₁, ⟨e⟩⟩ := hQiso
  have hQt : Q.map (phiO K t).toMonoidHom = Q := (hprop.1 t (subset_closure (Set.mem_insert _ _))).1
  have hF₁ : ringChar (GaloisField p₁ n₁) ≠ 2 := by
    rw [ringChar.eq (GaloisField p₁ n₁) p₁]
    exact hp₁
  have hQQ : ⁅Q, Q⁆ = Q := C.commutator_eq_of_isPComponent hQs hQc
  obtain ⟨α, hα, hαs, -⟩ := exists_coverR K hq hsimple hnab hS eσ hS₁ θ
  have hkerα := ker_coverR_le_center hα
  have hkerα2 := isPGroup_ker_coverR hα
  obtain ⟨hTQ, -, hinj⟩ := perfectLift_spec α hαs hkerα hkerα2 hQQ hF₁ e
  obtain ⟨x₀, hx₀T, hαx₀, hx₀Z, hx₀2⟩ := exists_central_lift α hkerα hTQ hinj hcZ hcQ hc2
  have hII := propBHypII_lift hS.split α hαs hkerα hkerα2 hs2 hQs hQc hp₁ hn₁ e hx₀T hx₀Z hx₀2
  have hx₀n := hneg x₀ hx₀Z hx₀2 hII
  subst hx₀n
  exact exc_false K hq hsimple hnab ht hs2 hst hQs hQc hp₁ e hcZ hcQ hc2 hQt hℓ2 hf hKc hS hd5
    eσ hR hker hsurj hS₁ θ hα hαs hαx₀ hx₀T hg hσ hpc

end CFSG.ComponentClassification.Burgoyne.DX.Dr
