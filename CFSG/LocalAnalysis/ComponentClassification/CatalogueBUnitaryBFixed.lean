module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBHyperbolic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBConjugate
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupAntiunitary

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryB

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem finrank_hypIndex_fun : finrank K (HypIndex r ε → K) = 2 * r + ε := by
  rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]

theorem hyp_fixed_pComponent_quasisimple (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (β : MulAut (hypPSU h r ε))
    (hβ : orderOf β = 2) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (M : Subgroup (FixedCommutingProduct.fixedSubgroup β)) (hM : CFSG.IsPComponent ℓ M) :
    CFSG.IsQuasisimple M := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨-, -, -, hrep⟩ := odd_unitary_automorphism_semilinear_representation h hp hr hε hn
  obtain ⟨A, σ, hx, hA, hβeq, hσ, hid, hbar⟩ := hrep β hβ
  have happly : ∀ g : hypSU h r ε,
      β (hypProj h r ε g) = hypProj h r ε ⟨_, conj_mem_hypSU hx g⟩ := by
    intro g
    rw [← hβeq]
    exact semilinearAutHom_apply h hr hε _ g
  have hdim : finrank K (HypIndex r ε → K) = 2 * r + ε := finrank_hypIndex_fun
  rcases hσ with rfl | hσ
  ·
    set a : sesqProjUnitary h (hypForm h r ε) :=
      QuotientGroup.mk (hypUnitaryEquiv h ⟨A, hA⟩) with ha_def
    have ha : orderOf a = 2 := by
      rw [ha_def, ← hypUnitaryModEquiv_mk, MulEquiv.orderOf_eq]
      exact hid rfl
    have he : ∀ y, ((hypModelEquiv h (β y) : projSpecial h (hypForm h r ε)) :
        sesqProjUnitary h (hypForm h r ε)) = MulAut.conj a (hypModelEquiv h y) := by
      intro y
      obtain ⟨g, rfl⟩ := hypProj_surjective h r ε y
      rw [happly]
      refine hypModelEquiv_conj h ⟨A, hA⟩ g _ ?_
      have hg : glAut (RingEquiv.refl K) (g : GL (HypIndex r ε) K) = (g : GL (HypIndex r ε) K) :=
        congrArg (fun φ : MulAut (GL (HypIndex r ε) K) => φ (g : GL (HypIndex r ε) K))
          (map_one glAut)
      change A * glAut (RingEquiv.refl K) (g : GL (HypIndex r ε) K) * A⁻¹ = _
      rw [hg]
    have hfix := (odd_unitary_inner_diagonal_involution_fixed_p_components h hp
      (by rw [hdim]; omega) (hypForm_isSymm h) (hypForm_separatingLeft h)).1 a ha ℓ hℓ
    exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv ℓ
      ((fixedEquivInf _ (hypModelEquiv h) β (MulAut.conj a) he).trans
        (MulEquiv.subgroupCongr (by rw [fixedSubgroup_conj]))) hfix M hM
  ·
    obtain ⟨c, hc0, hAc⟩ := hbar hσ
    have hτB := hypForm_semilinearMatrixMap h hA
    have he : ∀ y, ((hypModelEquiv h (β y) : projSpecial h (hypForm h r ε)) :
        sesqProjUnitary h (hypForm h r ε)) =
          antiProjConj h (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))
            (semilinearMatrixMap_bijective h hc0 hAc) hτB (hypModelEquiv h y) := by
      intro y
      obtain ⟨g, rfl⟩ := hypProj_surjective h r ε y
      rw [happly]
      exact hypModelEquiv_antiConj h A hc0 hAc hτB σ hσ g _
    have hfix := (odd_unitary_conjugate_semilinear_fixed_p_components h hp
      (by rw [hdim]; exact hn) (hypForm_isSymm h) (hypForm_separatingLeft h)
      (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))
      (semilinearMatrixMap_bijective h hc0 hAc) hτB (Units.mk0 c hc0)
      (semilinearMatrixMap_sq h hAc)).2 ℓ hℓ
    exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv ℓ
      (fixedEquivInf _ (hypModelEquiv h) β _ he) hfix M hM

theorem odd_unitary_involution_fixed_p_components (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    {n : ℕ} (hn : 3 ≤ n) (α : MulAut (unitaryPSU h n)) (hα : orderOf α = 2) (ℓ : ℕ)
    (hℓ : ℓ.Prime) (L : Subgroup (FixedCommutingProduct.fixedSubgroup α))
    (hL : CFSG.IsPComponent ℓ L) : CFSG.IsQuasisimple L := by
  obtain ⟨r, ε, hr, hε, rfl⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, by omega, by omega⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport h hr hε).1
  let θ := hypProjTransport h (R := R) hR
  let β : MulAut (hypPSU h r ε) := MulAut.congr θ.symm α
  have hβ : orderOf β = 2 := (MulEquiv.orderOf_eq (MulAut.congr θ.symm) α).trans hα
  have hθ : ∀ x, θ (β x) = α (θ x) := fun x => by
    change θ (θ.symm (α (θ.symm.symm x))) = α (θ x)
    rw [MulEquiv.apply_symm_apply, MulEquiv.symm_symm]
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv ℓ
    (CatalogueBOrthogonalFixedTransfer.fixedEquivOfIntertwining θ β α hθ).symm
    (hyp_fixed_pComponent_quasisimple h hp hr hε hn β hβ ℓ hℓ) L hL

end CFSG.ComponentClassification.CatalogueBUnitaryB
