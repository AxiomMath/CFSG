module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrCover
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrMain
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXAdapt
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcAsmA

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
  (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
  (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
  (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a)

include hq hsimple hnab in
theorem exc_false {t : J} (ht : orderOf (phiO K t) = 2)
    {s : MulAut (K ⧸ pPrimeCore 2 K)} (hs2 : orderOf s = 2) (hst : s * phiO K t = phiO K t * s)
    {Q : Subgroup (K ⧸ pPrimeCore 2 K)} (hQs : Q ≤ autFixed s)
    (hQc : IsPComponent 2 (Q.subgroupOf (autFixed s))) {p₁ n₁ : ℕ} [Fact p₁.Prime]
    (hp₁ : p₁ ≠ 2) (e : Q ⧸ pPrimeCore 2 Q ≃* SL(2, GaloisField p₁ n₁))
    {c : K ⧸ pPrimeCore 2 K} (hcZ : c ∈ center (K ⧸ pPrimeCore 2 K)) (hcQ : c ∈ Q)
    (hc2 : orderOf c = 2) (hQt : Q.map (phiO K t).toMonoidHom = Q)
    {F : Type} [Field F] [Finite F] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP F ℓ] (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hKc : Nat.card F = ℓ ^ f) {σ : Type} [Fintype σ] [DecidableEq σ]
    {Q₀ : QuadraticForm F (σ → F)} {Q0 : (σ → F) → F} (hS : SpinFacts Q₀ Q0) {d : ℕ}
    (hd5 : 5 ≤ d) (eσ : σ ≃ Fin d) {R : GL (Fin d) F}
    (hR : (R : Matrix (Fin d) (Fin d) F)ᵀ = R) (hker : OKer (oQ R)) (hsurj : OSurj (oQ R))
    (hS₁ : ∀ v, oQ R ((1 : GL (Fin d) F).val *ᵥ v) = ((1 : Fˣ) : F) * reindexQuadraticForm eσ Q₀ v)
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* StatedProj (matrixDerived (oQ R)))
    {α : spinGroup Q₀ →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (piR hS eσ hS₁ x))
    (hαs : Function.Surjective α) (hαc : α (negOneR hS) = c)
    (hnegQ : negOneR hS ∈ ⁅Q.comap α, Q.comap α⁆)
    {g : similarityPairs (oQ R)}
    (hg : socleAction θ ((rhoZ K).rangeRestrict t) = oκ _ g)
    (hσ : g.val.right = 1)
    (hpc : (g.val.left : Matrix (Fin d) (Fin d) F)ᵀ * R =
      (-1 : F) • ((R : Matrix (Fin d) (Fin d) F) * g.val.left)) : False := by
  have hK : ringChar F ≠ 2 := by rw [ringChar.eq F ℓ]; exact hℓ2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  have hF₁ : ringChar (GaloisField p₁ n₁) ≠ 2 := by
    rw [ringChar.eq (GaloisField p₁ n₁) p₁]
    exact hp₁
  have hQQ : ⁅Q, Q⁆ = Q := C.commutator_eq_of_isPComponent hQs hQc
  have hkerα := ker_coverR_le_center hα
  have hkerα2 := isPGroup_ker_coverR hα
  have : Finite (spinGroup Q₀) := hS.finite
  have key := perfectLift_spec α hαs hkerα hkerα2 hQQ hF₁ e
  have hZ := isPGroup_centerR hα hαs
  have hQM := map_socle_eqR hα key.1
  obtain ⟨gs, hgs⟩ := hsurj (MulAut.congr θ (socleAut K hq hsimple hnab s))
  obtain ⟨hQs', hQc'⟩ :=
    socle_comp_of_eq K hq hsimple hnab θ hZ hQs hQc hQM hgs
  have hd := excData_of_lift hS eσ hS₁ h2 α hαs hkerα hkerα2 hQs hQc hF₁ e hcZ hcQ hc2 hnegQ hαc
  have hsurjν : ∀ y, ∃ x, θ (socleHom K hq hsimple hnab x) = y := fun y =>
    (θ.surjective.comp (socleHom_surjective K hq hsimple hnab)) y
  have hgsν : ∀ x, oκ _ gs (θ (socleHom K hq hsimple hnab x)) =
      θ (socleHom K hq hsimple hnab (s x)) := fun x =>
    (DFunLike.congr_fun hgs _).symm.trans (congr_socleAut_apply K hq hsimple hnab θ s x)
  have hgν : ∀ x, oκ _ g (θ (socleHom K hq hsimple hnab x)) =
      θ (socleHom K hq hsimple hnab (phiO K t x)) := fun x =>
    (DFunLike.congr_fun hg _).symm.trans (socleAction_apply_socleHom K hq hsimple hnab θ t x)
  have hs2' : ∀ x, s (s x) = x := by
    intro x
    have h := pow_orderOf_eq_one s
    rw [hs2, pow_two] at h
    exact DFunLike.congr_fun h x
  have hss : oκ _ (gs * gs) = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hsurjν y
    calc oκ _ (gs * gs) (θ (socleHom K hq hsimple hnab x)) =
        oκ _ gs (oκ _ gs (θ (socleHom K hq hsimple hnab x))) := by
          rw [map_mul]
          rfl
      _ = oκ _ gs (θ (socleHom K hq hsimple hnab (s x))) := congrArg (oκ _ gs) (hgsν x)
      _ = θ (socleHom K hq hsimple hnab (s (s x))) := hgsν (s x)
      _ = θ (socleHom K hq hsimple hnab x) := by rw [hs2' x]
  have hs1 : oκ _ gs ≠ 1 := by
    intro h1
    have h2' : ∀ x, socleHom K hq hsimple hnab (s x) = socleHom K hq hsimple hnab x := by
      intro x
      have e1 := hgsν x
      rw [h1] at e1
      exact (θ.injective e1).symm
    have h1'' := eq_one_of_socleHom_eq K hq hsimple hnab h2'
    rw [h1'', orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  have ht2 : ∀ x, phiO K t (phiO K t x) = x := by
    intro x
    have h := pow_orderOf_eq_one (phiO K t)
    rw [ht, pow_two] at h
    exact DFunLike.congr_fun h x
  have htt : oκ _ (g * g) = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hsurjν y
    calc oκ _ (g * g) (θ (socleHom K hq hsimple hnab x)) =
        oκ _ g (oκ _ g (θ (socleHom K hq hsimple hnab x))) := by
          rw [map_mul]
          rfl
      _ = oκ _ g (θ (socleHom K hq hsimple hnab (phiO K t x))) := congrArg (oκ _ g) (hgν x)
      _ = θ (socleHom K hq hsimple hnab (phiO K t (phiO K t x))) := hgν _
      _ = θ (socleHom K hq hsimple hnab x) := by rw [ht2 x]
  have hts : oκ _ g * oκ _ gs = oκ _ gs * oκ _ g := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hsurjν y
    have hst' : phiO K t (s x) = s (phiO K t x) := (DFunLike.congr_fun hst x).symm
    calc (oκ _ g * oκ _ gs) (θ (socleHom K hq hsimple hnab x)) =
        oκ _ g (oκ _ gs (θ (socleHom K hq hsimple hnab x))) := rfl
      _ = oκ _ g (θ (socleHom K hq hsimple hnab (s x))) := congrArg (oκ _ g) (hgsν x)
      _ = θ (socleHom K hq hsimple hnab (phiO K t (s x))) := hgν _
      _ = θ (socleHom K hq hsimple hnab (s (phiO K t x))) := by rw [hst']
      _ = oκ _ gs (θ (socleHom K hq hsimple hnab (phiO K t x))) := (hgsν _).symm
      _ = oκ _ gs (oκ _ g (θ (socleHom K hq hsimple hnab x))) :=
          congrArg (oκ _ gs) (hgν x).symm
      _ = (oκ _ gs * oκ _ g) (θ (socleHom K hq hsimple hnab x)) := rfl
  have hQt' : ∀ x ∈ ((⁅Q.comap α, Q.comap α⁆.map (spinRGL hS eσ hS₁)).subgroupOf
      (matrixDerived (oQ R))).map (projH _),
      oκ _ g x ∈ ((⁅Q.comap α, Q.comap α⁆.map (spinRGL hS eσ hS₁)).subgroupOf
        (matrixDerived (oQ R))).map (projH _) := by
    rw [← hQM]
    rintro _ ⟨q, hq', rfl⟩
    have hqt : phiO K t q ∈ Q := by
      rw [← hQt]
      exact ⟨q, hq', rfl⟩
    exact ⟨phiO K t q, hqt, (hgν q).symm⟩
  exact false_of_exc hK hd5 (Fact.out : ℓ.Prime) hf hKc hR hker hd hss hs1 hQs' hQc' hσ htt hpc
    hts hQt'

end CFSG.ComponentClassification.Burgoyne.DX.Dr
