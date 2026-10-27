module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrSpin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXSocle

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Dr

open Matrix CFSG Subgroup CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.B
open CFSG.ComponentClassification.Burgoyne CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

attribute [local instance] GeneralizedFitting.normal

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]
  (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
  (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
  (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a)
  {F : Type} [Field F] {σ : Type} [Fintype σ] [DecidableEq σ]
  {Q₀ : QuadraticForm F (σ → F)} {Q0 : (σ → F) → F} (hS : SpinFacts Q₀ Q0) {d : ℕ}
  (eσ : σ ≃ Fin d) {R : GL (Fin d) F}
  (hS₁ : ∀ v, oQ R ((1 : GL (Fin d) F).val *ᵥ v) = ((1 : Fˣ) : F) * reindexQuadraticForm eσ Q₀ v)
  (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* StatedProj (matrixDerived (oQ R)))

include hq in
theorem exists_coverR :
    ∃ α : spinGroup Q₀ →* K ⧸ pPrimeCore 2 K,
      (∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (piR hS eσ hS₁ x)) ∧
        Function.Surjective α ∧ center (K ⧸ pPrimeCore 2 K) = (center (spinGroup Q₀)).map α := by
  have : Finite (spinGroup Q₀) := hS.finite
  set β : spinGroup Q₀ →* (rhoZ K).range :=
    (GeneralizedFitting.subgroup (rhoZ K).range).subtype.comp
      (θ.symm.toMonoidHom.comp (piR hS eσ hS₁)) with hβ
  have hβr : β.range = (liftHom K).range := by
    rw [liftHom_range_eq K hq hsimple hnab]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (θ.symm (piR hS eσ hS₁ x)).2
    · intro hy
      obtain ⟨x, hx⟩ := piR_surjective hS eσ hS₁ (θ ⟨y, hy⟩)
      refine ⟨x, ?_⟩
      change ((θ.symm (piR hS eσ hS₁ x) : GeneralizedFitting.subgroup _) : (rhoZ K).range) = y
      rw [hx, MulEquiv.symm_apply_apply]
  obtain ⟨α, hαβ, hαs, hZ⟩ := exists_cover K hS.split hq hβr
  have hkerβ : β.ker = center (spinGroup Q₀) := by
    rw [← ker_piR hS eσ hS₁]
    ext x
    simp only [hβ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
    constructor
    · intro h
      have h' : θ.symm (piR hS eσ hS₁ x) = 1 := Subtype.ext h
      rwa [MulEquiv.map_eq_one_iff] at h'
    · intro h
      rw [h, map_one]
      rfl
  refine ⟨α, fun x => Subtype.ext (hαβ x), hαs, ?_⟩
  rw [hZ, hkerβ]

variable {K hq hsimple hnab hS eσ hS₁ θ}

theorem ker_coverR_le_center {α : spinGroup Q₀ →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (piR hS eσ hS₁ x)) :
    α.ker ≤ center (spinGroup Q₀) := by
  intro x hx
  rw [← ker_piR hS eσ hS₁, MonoidHom.mem_ker]
  have h := hα x
  rw [MonoidHom.mem_ker.1 hx, map_one] at h
  exact (MulEquiv.map_eq_one_iff θ.symm).1 h.symm

theorem isPGroup_ker_coverR {α : spinGroup Q₀ →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (piR hS eσ hS₁ x)) :
    IsPGroup 2 α.ker :=
  hS.center2.to_le (ker_coverR_le_center hα)

theorem isPGroup_centerR {α : spinGroup Q₀ →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (piR hS eσ hS₁ x))
    (hαs : Function.Surjective α) : IsPGroup 2 (center (K ⧸ pPrimeCore 2 K)) := by
  intro z
  obtain ⟨y, hy⟩ := hαs (z : K ⧸ pPrimeCore 2 K)
  have hz : socleHom K hq hsimple hnab z = 1 := by
    rw [← MonoidHom.mem_ker, ker_socleHom]
    exact z.2
  have hy1 : piR hS eσ hS₁ y = 1 := by
    have e1 := hα y
    rw [hy, hz] at e1
    exact (MulEquiv.map_eq_one_iff θ.symm).1 e1.symm
  have hyc : y ∈ center (spinGroup Q₀) := by rw [← ker_piR hS eσ hS₁]; exact hy1
  obtain ⟨k, hk⟩ := hS.center2 ⟨y, hyc⟩
  have h1 : y ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy, ← map_pow, h1, map_one]

theorem map_socle_eqR {α : spinGroup Q₀ →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (piR hS eσ hS₁ x))
    {Q : Subgroup (K ⧸ pPrimeCore 2 K)} (hQ : ⁅Q.comap α, Q.comap α⁆.map α = Q) :
    Q.map (θ.toMonoidHom.comp (socleHom K hq hsimple hnab)) =
      ((⁅Q.comap α, Q.comap α⁆.map (spinRGL hS eσ hS₁)).subgroupOf
        (matrixDerived (oQ R))).map (projH _) := by
  have hνα : ∀ x : spinGroup Q₀, θ.toMonoidHom.comp (socleHom K hq hsimple hnab) (α x) =
      projH _ (spinR hS eσ hS₁ x) := by
    intro x
    rw [MonoidHom.comp_apply, hα]
    change θ (θ.symm (piR hS eσ hS₁ x)) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hQ' : Q.map (θ.toMonoidHom.comp (socleHom K hq hsimple hnab)) =
      (⁅Q.comap α, Q.comap α⁆.map α).map
        (θ.toMonoidHom.comp (socleHom K hq hsimple hnab)) := by rw [hQ]
  rw [hQ', Subgroup.map_map]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨spinR hS eσ hS₁ x, mem_subgroupOf.2 ⟨x, hx, rfl⟩, (hνα x).symm⟩
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨x, hx, hxX⟩ := mem_subgroupOf.1 hX
    refine ⟨x, hx, ?_⟩
    rw [MonoidHom.comp_apply, hνα]
    congr 1
    exact Subtype.ext hxX

end CFSG.ComponentClassification.Burgoyne.DX.Dr
