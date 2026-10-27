module

public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexHomologyForm
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineBasic

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Homology

open Matrix Module Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover
  CFSG.OddSolvableUnitary CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem exists_add_bar_eq_one : ∃ μ : K, μ + hK.bar μ = 1 := by
  have : CharP K 2 := hK.charP
  obtain ⟨c, hc⟩ := hK.exists_bar_ne
  have hd0 : c + hK.bar c ≠ 0 := by
    intro h
    apply hc
    calc hK.bar c = (c + hK.bar c) + c := by
          rw [add_comm c, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = c := by rw [h, zero_add]
  have hdbar : hK.bar (c + hK.bar c) = c + hK.bar c := by
    rw [map_add, hK.bar_bar, add_comm]
  refine ⟨c * (c + hK.bar c)⁻¹, ?_⟩
  rw [map_mul, map_inv₀, hdbar, ← add_mul, mul_inv_cancel₀ hd0]

@[expose] def hyperbolicVec (μ : K) : Fin 3 → Fin 3 → K :=
  ![![1, 0, μ], ![1, 0, hK.bar μ], ![0, 1, 0]]

variable {hK}

theorem hermForm_hyperbolicVec {J : HermitianForm 3 K}
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {μ : K} (hμ : μ + hK.bar μ = 1)
    (i j : Fin 3) :
    hermForm hK J (hyperbolicVec hK μ i) (hyperbolicVec hK μ j) = if i = j then 1 else 0 := by
  have : CharP K 2 := hK.charP
  have hμ' : hK.bar μ + μ = 1 := by rw [add_comm]; exact hμ
  rw [hermForm_apply, hJ]
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicVec, dotProduct, mulVec, Fin.sum_univ_three, hK.bar_bar, hμ, hμ',
      CharTwo.add_self_eq_zero]

theorem exists_basis_eq_hyperbolicVec {J : HermitianForm 3 K}
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {μ : K} (hμ : μ + hK.bar μ = 1) :
    ∃ e : Basis (Fin 3) K (Fin 3 → K), ⇑e = hyperbolicVec hK μ := by
  have hli : LinearIndependent K (hyperbolicVec hK μ) :=
    linearIndependent_of_orthogonal hK (B := hermForm hK J)
      (fun i j hij => by rw [hermForm_hyperbolicVec hJ hμ, ite_eq_right hij])
      (fun i => by rw [hermForm_hyperbolicVec hJ hμ, ite_eq_left rfl]; exact one_ne_zero)
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, finrank_fin_fun]),
    coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩

variable (hK) in
theorem diag3_mulVec_hyperbolicVec (a b : Kˣ) (μ : K) (i : Fin 3) :
    (UnitaryAutomorphism.diag3 a b a : Matrix (Fin 3) (Fin 3) K) *ᵥ hyperbolicVec hK μ i =
      ((![a, a, b] i : Kˣ) : K) • hyperbolicVec hK μ i := by
  rw [UnitaryAutomorphism.coe_diag3]
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [hyperbolicVec, mulVec, dotProduct, Fin.sum_univ_three, mul_comm]

theorem homologySubgroup_eq_map_torusHom {J : HermitianForm 3 K}
    (hJbar : ∀ c, J.conj c = hK.bar c) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {μ : K}
    {e : Basis (Fin 3) K (Fin 3 → K)} (he : ⇑e = hyperbolicVec hK μ) :
    homologySubgroup (hermForm hK J) e =
      (UnitaryAutomorphism.torusHom J hJ).range.map
        (specialSubgroupEquiv hK hJbar).toMonoidHom := by
  have hMM : ∀ c : Kˣ, c ∈ UnitaryAutomorphism.normOne J ↔ c ∈ normOne K (2 ^ f) := fun c => by
    rw [UnitaryAutomorphism.mem_normOne, hJbar, mem_normOne_iff_norm hK, UnitaryFieldData.norm]
  have hact : ∀ a b : Kˣ, ∀ i, ((Matrix.GeneralLinearGroup.toLin (UnitaryAutomorphism.diag3 a b a) :
      LinearMap.GeneralLinearGroup K (Fin 3 → K)) : (Fin 3 → K) →ₗ[K] Fin 3 → K) (e i) =
        ((![a, a, b] i : Kˣ) : K) • e i := by
    intro a b i
    rw [toLin_apply', he]
    exact diag3_mulVec_hyperbolicVec hK a b μ i
  have hsq : ∀ c : Kˣ, c⁻¹ ^ 2 = (c * c)⁻¹ := fun c => by rw [sq, mul_inv]
  ext g
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := (mem_homologySubgroup (hermForm hK J)).1 hg
    have hd : ((glMatrix e (g : LinearMap.GeneralLinearGroup K (Fin 3 → K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
          Matrix.diagonal fun i => ((![(c : Kˣ), c, ((c : Kˣ) * c)⁻¹] i : Kˣ) : K) := by
      rw [← hc, homologyHom_apply, coe_diagHom]
    have hgact := apply_eq_smul_of_coe_glMatrix_eq_diagonal e _ hd
    have hcJ : (c : Kˣ) ∈ UnitaryAutomorphism.normOne J := (hMM c).2 c.2
    refine ⟨UnitaryAutomorphism.torusHom J hJ ⟨c, hcJ⟩, ⟨⟨c, hcJ⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [MulEquiv.coe_toMonoidHom, coe_specialSubgroupEquiv, UnitaryAutomorphism.coe_torusHom]
    refine e.ext fun i => ?_
    rw [hact, hgact, hsq]
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine (mem_homologySubgroup (hermForm hK J)).2 ⟨⟨(c : Kˣ), (hMM c).1 c.2⟩, ?_⟩
    apply Units.ext
    rw [homologyHom_apply, coe_diagHom]
    symm
    apply coe_glMatrix_eq_diagonal_of_apply e
    intro j
    rw [MulEquiv.coe_toMonoidHom, coe_specialSubgroupEquiv, UnitaryAutomorphism.coe_torusHom,
      hact, hsq]

theorem specialSubgroupEquiv_eq_smul_one {J : HermitianForm 3 K}
    (hJbar : ∀ c, J.conj c = hK.bar c) {g : J.specialSubgroup} {c : K}
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c) :
    ((specialSubgroupEquiv hK hJbar g : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
      (Fin 3 → K) →ₗ[K] Fin 3 → K) = c • 1 := by
  refine LinearMap.ext fun x => ?_
  rw [coe_specialSubgroupEquiv, toLin_apply', hg, LinearMap.smul_apply, Module.End.one_apply]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Homology
