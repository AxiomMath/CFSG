module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedCoverMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedDModel

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)
open CFSG.ClassicalInvolution.Upgrade (map_statedOmega map_statedOmega_conj statedQuadMinus_comp)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : Type} [Field k]

theorem toLinEquiv_symm_apply_apply (E : (ι → k) ≃ₗ[k] (ι → k)) (p q : ι) :
    (((toLinEquiv ι k).symm E : GL ι k) : Matrix ι ι k) p q = E (Pi.single q 1) p := by
  have h := toLinEquiv_apply ((toLinEquiv ι k).symm E) (Pi.single q 1)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, mulVec_single_one]
  rfl

theorem commute_of_toLinEquiv {H : Subgroup (GL ι k)} {A B : H}
    (h : Commute (toLinEquiv ι k (A : GL ι k)) (toLinEquiv ι k (B : GL ι k))) : Commute A B := by
  show A * B = B * A
  apply Subtype.ext
  apply (toLinEquiv ι k).injective
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  exact h.eq

end Lin

section Eichler

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {Q : QuadraticForm k V}

theorem commute_eichler_of_apply_eq_smul {g : V ≃ₗ[k] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u w : V} {δ : k} (hδ : δ ≠ 0)
    (hu : g u = δ • u) (hw : g w = δ⁻¹ • w) : Commute g (eichler Q u w) := by
  have h := eichler_conj hg u w
  rw [hu, hw, eichler_smul_left, smul_smul, mul_inv_cancel₀ hδ, one_smul] at h
  show g * eichler Q u w = eichler Q u w * g
  calc g * eichler Q u w = g * eichler Q u w * g⁻¹ * g := by group
    _ = eichler Q u w * g := by rw [h]

end Eichler

section Diag

variable {k : Type} [Field k]

theorem toLinEquiv_diagOmegaMinus_apply (t : Fin 3 → kˣ)
    (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) (p : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) :
    toLinEquiv _ k (diagOmegaMinus k t) v p = minusWeight k t p * v p := by
  rw [toLinEquiv_apply, diagOmegaMinus_coe, mulVec_diagonal]

theorem toLinEquiv_diagOmegaMinus_single (t : Fin 3 → kˣ) (p : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
    (a : k) :
    toLinEquiv _ k (diagOmegaMinus k t) (Pi.single p a) = minusWeight k t p • Pi.single p a := by
  funext q
  rw [toLinEquiv_diagOmegaMinus_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : q = p
  · subst h
    rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

theorem toLinEquiv_diagOmegaMinus_of_V₆_zero (t : Fin 3 → kˣ)
    {v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k} (hv : ∀ i : Fin 3 ⊕ Fin 3, v (minusEmb i) = 0) :
    toLinEquiv _ k (diagOmegaMinus k t) v = v := by
  funext p
  rw [toLinEquiv_diagOmegaMinus_apply]
  rcases p with i | i | j
  · rw [show v (Sum.inl i) = 0 from hv (Sum.inl i), mul_zero]
  · rw [show v (Sum.inr (Sum.inl i)) = 0 from hv (Sum.inr i), mul_zero]
  · rw [minusWeight_inr_inr, one_mul]

theorem toLinEquiv_diagOmegaMinus_mem [Finite k] [CharP k 2] (b c : k) (t : Fin 3 → kˣ) :
    toLinEquiv _ k (diagOmegaMinus k t) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 k b c) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [toLinEquiv_apply, CFSG.LieType.Universal.Spin.coe_quadMinus]
  exact isometry_of_mem_omegaMinus8 k ⟨_, diagOmegaMinus_mem b c t⟩ x

end Diag

section Transport

variable {k₁ k₂ : Type} [Field k₁] [Field k₂]

variable (ε₀ : k₁ ≃+* k₂) {b : k₁} (c : k₁) (hb : ε₀ b ≠ 0)

@[expose] noncomputable def twTransport :
    StatedOmega (StatedQuadMinus 4 k₁ b c) ≃*
      StatedOmega (StatedQuadMinus 4 k₂ 1 (ε₀ c / ε₀ b ^ 2)) :=
  (((glCongr ε₀).subgroupMap _).trans
      (MulEquiv.subgroupCongr (map_statedOmega ε₀ (statedQuadMinus_comp ε₀ rfl rfl)))).trans
    (((MulAut.conj (minusScale hb)).subgroupMap _).trans
      (MulEquiv.subgroupCongr
        (map_statedOmega_conj (minusScale hb) (statedQuadMinus_minusScale hb))))

theorem coe_twTransport (g : StatedOmega (StatedQuadMinus 4 k₁ b c)) :
    ((twTransport ε₀ c hb g : StatedOmega (StatedQuadMinus 4 k₂ 1 (ε₀ c / ε₀ b ^ 2))) :
      GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k₂) =
      minusScale hb * glCongr ε₀ (g : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k₁) *
        (minusScale hb)⁻¹ :=
  rfl

theorem twTransport_apply_minusEmb (g : StatedOmega (StatedQuadMinus 4 k₁ b c))
    (i j : Fin 3 ⊕ Fin 3) :
    (((twTransport ε₀ c hb g : StatedOmega (StatedQuadMinus 4 k₂ 1 (ε₀ c / ε₀ b ^ 2))) :
      GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k₂) : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k₂) (minusEmb i) (minusEmb j) =
      ε₀ ((((g : StatedOmega (StatedQuadMinus 4 k₁ b c)) :
        GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k₁) : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
          (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k₁) (minusEmb i) (minusEmb j)) := by
  rw [coe_twTransport, Units.val_mul, Units.val_mul]
  change (minusScaleMat (ε₀ b) * ((g : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k₁) :
    Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k₁).map ε₀ *
      minusScaleMat (ε₀ b)⁻¹) (minusEmb i) (minusEmb j) = _
  rw [minusScaleMat, minusScaleMat, mul_diagonal, diagonal_mul, ite_eq_right (minusEmb_ne_w i),
    ite_eq_right (minusEmb_ne_w j), one_mul, mul_one, map_apply]

variable [CharP k₁ 2] [CharP k₂ 2]

theorem twTransport_betaC (g : StatedOmega (StatedQuadMinus 4 k₁ b c)) :
    twTransport ε₀ c hb (omegaMinusBetaC k₁ b c g) =
      omegaMinusBetaC k₂ 1 (ε₀ c / ε₀ b ^ 2) (twTransport ε₀ c hb g) := by
  have hDh : minusScale hb * minusShear (ε₀ b) = minusShear 1 * minusScale hb :=
    Units.ext (minusScaleMat_mul_minusShearMat (ε₀ b))
  apply Subtype.ext
  rw [coe_twTransport, coe_omegaMinusBetaC, coe_omegaMinusBetaC, coe_twTransport, map_mul,
    map_mul, map_inv, glCongr_minusShear]
  calc minusScale hb * (minusShear (ε₀ b) * glCongr ε₀ (g : GL _ k₁) * (minusShear (ε₀ b))⁻¹) *
        (minusScale hb)⁻¹
      = (minusScale hb * minusShear (ε₀ b)) * glCongr ε₀ (g : GL _ k₁) *
          (minusScale hb * minusShear (ε₀ b))⁻¹ := by group
    _ = (minusShear 1 * minusScale hb) * glCongr ε₀ (g : GL _ k₁) *
          (minusShear 1 * minusScale hb)⁻¹ := by rw [hDh]
    _ = minusShear 1 * (minusScale hb * glCongr ε₀ (g : GL _ k₁) * (minusScale hb)⁻¹) *
          (minusShear 1)⁻¹ := by group

theorem twTransport_mem_fixedSubgroup {g : StatedOmega (StatedQuadMinus 4 k₁ b c)}
    (hg : g ∈ fixedSubgroup (omegaMinusBetaC k₁ b c)) :
    twTransport ε₀ c hb g ∈ fixedSubgroup (omegaMinusBetaC k₂ 1 (ε₀ c / ε₀ b ^ 2)) := by
  have hg' : omegaMinusBetaC k₁ b c g = g := hg
  show omegaMinusBetaC k₂ 1 (ε₀ c / ε₀ b ^ 2) (twTransport ε₀ c hb g) = twTransport ε₀ c hb g
  rw [← twTransport_betaC, hg']

variable [Finite k₁] [Finite k₂]

theorem twTransport_diag (t : Fin 3 → k₁ˣ) :
    twTransport ε₀ c hb ⟨diagOmegaMinus k₁ t, diagOmegaMinus_mem b c t⟩ =
      ⟨diagOmegaMinus k₂ (fun i => Units.map (ε₀ : k₁ →* k₂) (t i)),
        diagOmegaMinus_mem _ _ _⟩ := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_twTransport, Units.val_mul, Units.val_mul]
  change minusScaleMat (ε₀ b) * ((diagOmegaMinus k₁ t : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k₁) :
    Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k₁).map ε₀ *
      minusScaleMat (ε₀ b)⁻¹ = _
  rw [diagOmegaMinus_coe, diagOmegaMinus_coe, minusScaleMat, minusScaleMat,
    diagonal_map (map_zero ε₀), diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext p
  rcases p with i | i | j
  · rw [ite_eq_right Sum.inl_ne_inr, ite_eq_right Sum.inl_ne_inr, one_mul, mul_one]
    rfl
  · rw [ite_eq_right (fun h => Sum.inl_ne_inr (Sum.inr_injective h)),
      ite_eq_right (fun h => Sum.inl_ne_inr (Sum.inr_injective h)), one_mul, mul_one]
    rfl
  · have e1 : minusWeight k₁ t (Sum.inr (Sum.inr j)) = 1 := rfl
    have e2 : minusWeight k₂ (fun i => Units.map (ε₀ : k₁ →* k₂) (t i)) (Sum.inr (Sum.inr j)) =
      1 := rfl
    rw [e1, e2, map_one, mul_one]
    split_ifs
    · exact mul_inv_cancel₀ hb
    · exact mul_one 1

end Transport

end CFSG.SeitzReduction.F4Pilot
