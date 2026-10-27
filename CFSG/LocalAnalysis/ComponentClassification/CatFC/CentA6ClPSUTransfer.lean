module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerUGraph
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerULift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

section Transfer

variable {n : ℕ} {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)

@[expose] def PSUIsTransfer (σ : MulAut (primeFormP h (idGram K n))) {Q : Type} [Group Q]
    (ι : Q →* LinearMap.GeneralLinearGroup K (Fin n → K)) (ρ : Q →* ↥(fixedSubgroup σ)) : Prop :=
  ∀ x, ∃ g : ↥(gramSU h (idGram K n)), Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) = ι x ∧
    ((ρ x : ↥(fixedSubgroup σ)) : primeFormP h (idGram K n)) = QuotientGroup.mk g

theorem PSUIsTransfer.commute {σ : MulAut (primeFormP h (idGram K n))} {Q₁ Q₂ : Type} [Group Q₁]
    [Group Q₂] {ι₁ : Q₁ →* LinearMap.GeneralLinearGroup K (Fin n → K)}
    {ι₂ : Q₂ →* LinearMap.GeneralLinearGroup K (Fin n → K)} {ρ₁ : Q₁ →* ↥(fixedSubgroup σ)}
    {ρ₂ : Q₂ →* ↥(fixedSubgroup σ)} (h₁ : PSUIsTransfer h σ ι₁ ρ₁) (h₂ : PSUIsTransfer h σ ι₂ ρ₂)
    (hc : ∀ x y, ι₁ x * ι₂ y = ι₂ y * ι₁ x) (x : Q₁) (y : Q₂) :
    ρ₁ x * ρ₂ y = ρ₂ y * ρ₁ x := by
  obtain ⟨g₁, hg₁, hρ₁⟩ := h₁ x
  obtain ⟨g₂, hg₂, hρ₂⟩ := h₂ y
  have hgg : g₁ * g₂ = g₂ * g₁ := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.toLin.injective
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, hg₁, hg₂]
    exact hc x y
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hρ₁, hρ₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    hgg]

theorem psu_exists_hom_fixed (σ : MulAut (primeFormP h (idGram K n)))
    (ψ : MulAut ↥(gramSU h (idGram K n)))
    (hψ : ∀ g : ↥(gramSU h (idGram K n)),
      σ (QuotientGroup.mk g : primeFormP h (idGram K n)) = QuotientGroup.mk (ψ g))
    {Q : Type} [Group Q] (ι : Q →* LinearMap.GeneralLinearGroup K (Fin n → K))
    (hι : Function.Injective ι) (hS : ∀ x, ι x ∈ sesqSpecialUnitaryGroup (idForm h n))
    (hfix : ∀ (g : ↥(gramSU h (idGram K n))) (x : Q),
      Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) = ι x → ψ g = g) :
    ∃ ρ : Q →* ↥(fixedSubgroup σ), PSUIsTransfer h σ ι ρ ∧ ρ.ker ≤ Subgroup.center Q := by
  classical
  let toLinE : GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K) :=
    Matrix.GeneralLinearGroup.toLin
  have hmem : ∀ x, toLinE.symm (ι x) ∈ gramSU h (idGram K n) := fun x => by
    rw [← toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n),
      show Matrix.GeneralLinearGroup.toLin (toLinE.symm (ι x)) = ι x from
        toLinE.apply_symm_apply _]
    exact hS x
  let ι' : Q →* ↥(gramSU h (idGram K n)) :=
    (toLinE.symm.toMonoidHom.comp ι).codRestrict _ hmem
  have hι'coe : ∀ x, ((ι' x : ↥(gramSU h (idGram K n))) : GL (Fin n) K) = toLinE.symm (ι x) :=
    fun x => rfl
  let π : ↥(gramSU h (idGram K n)) →* primeFormP h (idGram K n) :=
    QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)
  have hfixσ : ∀ x, π (ι' x) ∈ fixedSubgroup σ := by
    intro x
    change σ (π (ι' x)) = π (ι' x)
    have h1 : ψ (ι' x) = ι' x := hfix (ι' x) x (by rw [hι'coe]; exact toLinE.apply_symm_apply _)
    rw [show π (ι' x) = (QuotientGroup.mk (ι' x) : primeFormP h (idGram K n)) from rfl, hψ, h1]
  refine ⟨(π.comp ι').codRestrict _ hfixσ, fun x => ⟨ι' x, hι'coe x ▸ ?_, rfl⟩, ?_⟩
  · exact toLinE.apply_symm_apply _
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : π (ι' x) = 1 := congrArg Subtype.val hx
  rw [show π (ι' x) = (QuotientGroup.mk (ι' x) : primeFormP h (idGram K n)) from rfl,
    QuotientGroup.eq_one_iff] at h1
  obtain ⟨c, -, -, hc⟩ := h1
  have hιx : ι x = Matrix.GeneralLinearGroup.toLin (GeneralLinearGroup.scalar (Fin n) c) := by
    have := congrArg toLinE hc
    rw [hι'coe, MulEquiv.apply_symm_apply] at this
    exact this
  rw [Subgroup.mem_center_iff]
  intro y
  apply hι
  rw [map_mul, map_mul, hιx]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, CatLeafProof.OddInner.toLin_scalar, smul_mul_assoc, one_mul,
    mul_smul_comm, mul_one]

theorem psu_exists_hom_fixed_inner (A : primeFormUnitary h (idGram K n))
    {Q : Type} [Group Q] (ι : Q →* LinearMap.GeneralLinearGroup K (Fin n → K))
    (hι : Function.Injective ι) (hS : ∀ x, ι x ∈ sesqSpecialUnitaryGroup (idForm h n))
    (hcomm : ∀ x, ι x * Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) * ι x) :
    ∃ ρ : Q →* ↥(fixedSubgroup (primeFormConjHom h (idGram K n) A)),
      PSUIsTransfer h (primeFormConjHom h (idGram K n) A) ι ρ ∧ ρ.ker ≤ Subgroup.center Q := by
  refine psu_exists_hom_fixed h _ (primeFormConjSU h (idGram K n) A)
    (fun g => primeFormConjHom_mk h _ A g) ι hι hS ?_
  intro g x hgx
  apply Subtype.ext
  change (A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹ = g
  rw [mul_inv_eq_iff_eq_mul]
  apply Matrix.GeneralLinearGroup.toLin.injective
  rw [map_mul, map_mul, hgx]
  exact (hcomm x).symm

theorem psu_graph_fix_of_commute (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x) (g : ↥(gramSU h (idGram K n)))
    (u : LinearMap.GeneralLinearGroup K (Fin n → K))
    (hgu : Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) = u)
    (hcomm : ∀ v, ((u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        (Fin n → K) →ₗ[K] (Fin n → K))
          (semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v) =
      semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        (((u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          (Fin n → K) →ₗ[K] (Fin n → K)) v)) :
    (primeFormConjSU h (idGram K n) A *
      primeFormFieldSU h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) φ) g = g := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have htoLin : ∀ (g : GL (Fin n) K) (v : Fin n → K),
      ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        (Fin n → K) →ₗ[K] (Fin n → K)) v = (g : Matrix (Fin n) (Fin n) K) *ᵥ v :=
    fun g v => by
      rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
  have hcg : ∀ v, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v =
      semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
    intro v
    have h1 := hcomm v
    rw [← hgu, htoLin, htoLin] at h1
    exact h1
  have hga := (CatLeafProof.OddInner.commute_semilinearMatrixMap_iff h _ _).mp hcg
  apply Subtype.ext
  change (A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = g
  rw [mul_inv_eq_iff_eq_mul, ← Units.val_inj, Units.val_mul, Units.val_mul, coe_glAut]
  have hmap : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar :=
    Matrix.ext fun i j => hφ _
  rw [hmap]
  exact hga.symm

theorem psu_graph_hψ (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (g : ↥(gramSU h (idGram K n))) :
    (primeFormPsi h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩)
      (QuotientGroup.mk g : primeFormP h (idGram K n)) =
    QuotientGroup.mk ((primeFormConjSU h (idGram K n) A *
      primeFormFieldSU h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) φ) g) := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  rw [primeFormPsi_apply, MulAut.mul_apply, MulAut.mul_apply]
  change primeFormConjAut h _ A (primeFormFieldAut h hC φ (QuotientGroup.mk g)) = _
  rw [primeFormFieldAut_mk, primeFormConjAut_mk]

theorem psu_exists_hom_fixed_graph (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x)
    {Q : Type} [Group Q] (ι : Q →* LinearMap.GeneralLinearGroup K (Fin n → K))
    (hι : Function.Injective ι) (hS : ∀ x, ι x ∈ sesqSpecialUnitaryGroup (idForm h n))
    (hcomm : ∀ x v, ((ι x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        (Fin n → K) →ₗ[K] (Fin n → K))
          (semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v) =
      semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        (((ι x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          (Fin n → K) →ₗ[K] (Fin n → K)) v)) :
    ∃ ρ : Q →* ↥(fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)),
      PSUIsTransfer h (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) ι ρ ∧
        ρ.ker ≤ Subgroup.center Q :=
  psu_exists_hom_fixed h _ (primeFormConjSU h (idGram K n) A * primeFormFieldSU h
    (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) φ) (psu_graph_hψ h A φ) ι hι hS
    (fun g x hgx => psu_graph_fix_of_commute h A φ hφ g (ι x) hgx (hcomm x))

theorem psu_exists_elt_fixed_graph (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x) (u : LinearMap.GeneralLinearGroup K (Fin n → K))
    (hS : u ∈ sesqSpecialUnitaryGroup (idForm h n))
    (hcomm : ∀ v, ((u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        (Fin n → K) →ₗ[K] (Fin n → K))
          (semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v) =
      semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        (((u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          (Fin n → K) →ₗ[K] (Fin n → K)) v)) :
    ∃ g : ↥(gramSU h (idGram K n)), Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) = u ∧
      (QuotientGroup.mk g : primeFormP h (idGram K n)) ∈
        fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) := by
  let toLinE : GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K) :=
    Matrix.GeneralLinearGroup.toLin
  have hmem : toLinE.symm u ∈ gramSU h (idGram K n) := by
    rw [← toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n),
      show Matrix.GeneralLinearGroup.toLin (toLinE.symm u) = u from toLinE.apply_symm_apply _]
    exact hS
  have hgu : Matrix.GeneralLinearGroup.toLin (toLinE.symm u) = u := toLinE.apply_symm_apply _
  refine ⟨⟨toLinE.symm u, hmem⟩, hgu, ?_⟩
  change (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) (QuotientGroup.mk _) = _
  rw [psu_graph_hψ h A φ ⟨toLinE.symm u, hmem⟩,
    psu_graph_fix_of_commute h A φ hφ ⟨toLinE.symm u, hmem⟩ u hgu hcomm]
  rfl

end Transfer

end CFSG.ComponentClassification.CatFC
