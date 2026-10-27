module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXParity
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Dr

open Module Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CliffordAlgebra
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj

variable {F : Type} [Field F] {σ : Type} [Fintype σ] [DecidableEq σ]

structure SpinFacts (Q₀ : QuadraticForm F (σ → F)) (Q0 : (σ → F) → F) : Prop where
  coe : ⇑Q₀ = Q0
  range : (spinMatrix Q₀).range = StatedOmega Q0
  ne_zero : Q₀ ≠ 0
  ker : ∀ x, x ∈ (spinMatrix Q₀).ker ↔ x = 1 ∨ (x : CliffordAlgebra Q₀) = -1
  nondeg : Q₀.Nondegenerate
  rad : ∀ v, (∀ w, QuadraticMap.polar Q₀ v w = 0) → v = 0
  finite : Finite (spinGroup Q₀)
  perfect : Group.IsPerfect (spinGroup Q₀)
  surj : Function.Surjective (spinToStatedProj Q₀ range)
  kerP : (spinToStatedProj Q₀ range).ker = center (spinGroup Q₀)
  split : ∀ (E : Type) [Group E] [Finite E] (π : E →* spinGroup Q₀),
    Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
      ∃ s : spinGroup Q₀ →* E, ∀ x, π (s x) = x
  center2 : IsPGroup 2 (center (spinGroup Q₀))

variable {Q₀ : QuadraticForm F (σ → F)} {Q0 : (σ → F) → F} (hS : SpinFacts Q₀ Q0) {d : ℕ}
  (e : σ ≃ Fin d) {R : GL (Fin d) F}
  (hS₁ : ∀ v, oQ R ((1 : GL (Fin d) F).val *ᵥ v) = ((1 : Fˣ) : F) * reindexQuadraticForm e Q₀ v)

abbrev negOneR : spinGroup Q₀ := spinGroup.negOne Q₀ hS.ne_zero

@[expose] def spinR : spinGroup Q₀ →* matrixDerived (oQ R) :=
  (derivedTransport 1 1 hS₁).toMonoidHom.comp
    ((statedDerivedReindexEquiv e Q₀ hS.coe).toMonoidHom.comp
      ((spinMatrix Q₀).codRestrict _ (spinMatrix_mem_of_range_eq _ hS.range)))

abbrev piR : spinGroup Q₀ →* StatedProj (matrixDerived (oQ R)) :=
  (projH (matrixDerived (oQ R))).comp (spinR hS e hS₁)

abbrev spinRGL : spinGroup Q₀ →* GL (Fin d) F :=
  (matrixDerived (oQ R)).subtype.comp (spinR hS e hS₁)

theorem spinR_val (x : spinGroup Q₀) :
    ((spinR hS e hS₁ x : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.reindex e e (spinMatrix Q₀ x : Matrix σ σ F) := by
  change (((1 : GL (Fin d) F) * (statedDerivedReindexEquiv e Q₀ hS.coe
    ⟨spinMatrix Q₀ x, spinMatrix_mem_of_range_eq _ hS.range x⟩ : GL (Fin d) F) *
      (1 : GL (Fin d) F)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = _
  rw [one_mul, inv_one, mul_one, statedDerivedReindexEquiv_val]
  rfl

theorem spinR_eq_one_iff (x : spinGroup Q₀) :
    spinR hS e hS₁ x = 1 ↔ x = 1 ∨ x = negOneR hS := by
  rw [eq_negOne_iff _ hS.ne_zero, ← hS.ker x, MonoidHom.mem_ker]
  constructor
  · intro h
    apply Units.ext
    have h' := congrArg (fun g : matrixDerived (oQ R) =>
      ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)) h
    simp only [spinR_val] at h'
    rw [Units.val_one]
    have h'' := congrArg (Matrix.reindex e.symm e.symm) h'
    simpa using h''
  · intro h
    apply Subtype.ext
    apply Units.ext
    rw [spinR_val, h]
    simp

theorem negOneR_mem_ker : spinR hS e hS₁ (negOneR hS) = 1 :=
  (spinR_eq_one_iff hS e hS₁ _).2 (Or.inr rfl)

theorem piR_eq (x : spinGroup Q₀) :
    piR hS e hS₁ x = oTransport 1 1 hS₁ (statedProjectiveReindexEquiv e Q₀ hS.coe
      (spinToStatedProj Q₀ hS.range x)) := by
  rw [spinToStatedProj_apply]
  have h1 := statedProjectiveReindexEquiv_mk e Q₀ hS.coe
    ⟨spinMatrix Q₀ x, spinMatrix_mem_of_range_eq _ hS.range x⟩
  exact ((congrArg (oTransport 1 1 hS₁) h1).trans (oTransport_proj 1 1 hS₁ _)).symm

theorem piR_surjective : Function.Surjective (piR hS e hS₁) := by
  intro y
  obtain ⟨z, hz⟩ := (statedProjectiveReindexEquiv e Q₀ hS.coe).surjective
    ((oTransport 1 1 hS₁).symm y)
  obtain ⟨x, rfl⟩ := hS.surj z
  refine ⟨x, ?_⟩
  rw [piR_eq, hz, MulEquiv.apply_symm_apply]

theorem ker_piR : (piR hS e hS₁).ker = center (spinGroup Q₀) := by
  rw [← hS.kerP]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    rw [piR_eq] at h
    have h1 : statedProjectiveReindexEquiv e Q₀ hS.coe (spinToStatedProj Q₀ hS.range x) = 1 :=
      (oTransport 1 1 hS₁).injective (h.trans (map_one _).symm)
    exact (statedProjectiveReindexEquiv e Q₀ hS.coe).injective (h1.trans (map_one _).symm)
  · intro h
    rw [piR_eq, h]
    exact (congrArg (oTransport 1 1 hS₁)
      (map_one (statedProjectiveReindexEquiv e Q₀ hS.coe))).trans (map_one _)

theorem mul_self_eq_negOne_iff (h2 : (2 : F) ≠ 0) (x : spinGroup Q₀)
    (hx : spinR hS e hS₁ (x * x) = 1) {m : ℕ}
    (hm : finrank F (LinearMap.ker (Matrix.toLin'
      ((spinR hS e hS₁ x : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) + LinearMap.id)) = m)
    (hev : Even m) : x * x = negOneR hS ↔ m % 4 = 2 := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  rw [spinR_val, finrank_ker_reindex_add_id, coe_spinMatrix, Matrix.toLin'_toMatrix'] at hm
  have hxx : ∀ v, spinAction Q₀ x (spinAction Q₀ x v) = v := by
    intro v
    have hk : x * x ∈ (spinMatrix Q₀).ker := by
      rw [hS.ker]
      rcases (spinR_eq_one_iff hS e hS₁ _).1 hx with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h, spinGroup.coe_negOne])
    have hm1 := congrArg (fun g : GL σ F => (↑g : Matrix σ σ F) *ᵥ v) (MonoidHom.mem_ker.mp hk)
    simp only [spinMatrix_mulVec, Units.val_one, Matrix.one_mulVec] at hm1
    rw [← LinearEquiv.mul_apply, ← map_mul]
    exact hm1
  have hsq := spin_mul_self_eq hS.nondeg hS.rad x hxx hm hev
  rw [neg_one_pow_choose_two_of_even hev] at hsq
  have hcoe : ((x * x : spinGroup Q₀) : CliffordAlgebra Q₀) =
      algebraMap F _ ((-1 : F) ^ (m / 2)) := by
    rw [Submonoid.coe_mul, hsq]
  have hneg1 : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  constructor
  · intro h
    rw [h, spinGroup.coe_negOne, ← map_one (algebraMap F (CliffordAlgebra Q₀)), ← map_neg] at hcoe
    have hc := algebraMap_injective' Q₀ hcoe.symm
    rcases Nat.even_or_odd (m / 2) with he | ho
    · rw [he.neg_one_pow] at hc
      exact absurd hc.symm hneg1
    · obtain ⟨k, hk⟩ := hev
      obtain ⟨j, hj⟩ := ho
      omega
  · intro h4
    apply Subtype.ext
    rw [hcoe, spinGroup.coe_negOne]
    have ho : Odd (m / 2) := by
      refine ⟨(m / 2 - 1) / 2, ?_⟩
      omega
    rw [ho.neg_one_pow, map_neg, map_one]

end CFSG.ComponentClassification.Burgoyne.DX.Dr
