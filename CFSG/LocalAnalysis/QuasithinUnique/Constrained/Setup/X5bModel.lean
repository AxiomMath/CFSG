module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bInvol
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.QuasithinUnique.Setup.X5

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

noncomputable abbrev idForm : (Fin 3 → K) →ₛₗ[h.bar] (Fin 3 → K) →ₗ[K] K :=
  gramForm h (1 : Matrix (Fin 3) (Fin 3) K)

theorem idForm_isSymm : (idForm h).IsSymm :=
  gramForm_isSymm h (by simp [Matrix.map_one])

theorem idForm_separatingLeft : (idForm h).SeparatingLeft :=
  gramForm_separatingLeft h (by simp)

theorem finrank_idForm : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K

theorem map_gramSU_eq :
    (gramSU h (1 : Matrix (Fin 3) (Fin 3) K)).map
      (Matrix.GeneralLinearGroup.toLin : GL (Fin 3) K ≃* _).toMonoidHom =
        sesqSpecialUnitaryGroup (idForm h) := by
  ext g
  rw [Subgroup.mem_map_equiv, ← toLin_mem_sesqSpecialUnitaryGroup_iff h 1,
    MulEquiv.apply_symm_apply]

@[expose] noncomputable def matrixSUEquiv :
    unitarySU 2 f K 3 ≃* sesqSpecialUnitaryGroup (idForm h) :=
  (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)).trans
    ((Matrix.GeneralLinearGroup.toLin.subgroupMap _).trans
      (MulEquiv.subgroupCongr (map_gramSU_eq h)))

theorem coe_matrixSUEquiv (g : unitarySU 2 f K 3) :
    ((matrixSUEquiv h g : sesqSpecialUnitaryGroup (idForm h)) :
      LinearMap.GeneralLinearGroup K (Fin 3 → K)) =
        Matrix.GeneralLinearGroup.toLin (g : GL (Fin 3) K) := rfl

theorem matrixSUEquiv_scalar {g : unitarySU 2 f K 3} (hg : g ∈ unitaryScalars h 3) :
    matrixSUEquiv h g ∈ FourGroupOddUnitary.unitaryScalars (idForm h) := by
  obtain ⟨c, -, -, hc⟩ := hg
  refine (FourGroupOddUnitary.mem_unitaryScalars (idForm h)).mpr ⟨c, ?_⟩
  rw [coe_matrixSUEquiv, hc]
  ext x i
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.GeneralLinearGroup.coe_scalar]
  simp [Pi.single_apply]

theorem matrix_quotient_involutions_isConj {Q : Type*} [Group Q] [FiniteDimensional K (Fin 3 → K)]
    {π : unitarySU 2 f K 3 →* Q} (hπ : Function.Surjective π) (hker : π.ker ≤ unitaryScalars h 3)
    {q₁ q₂ : Q} (h1 : q₁ * q₁ = 1) (h1' : q₁ ≠ 1) (h2 : q₂ * q₂ = 1) (h2' : q₂ ≠ 1) :
    IsConj q₁ q₂ := by
  refine quotient_involutions_isConj h finrank_idForm (idForm_isSymm h) (idForm_separatingLeft h)
    (π := π.comp (matrixSUEquiv h).symm.toMonoidHom) ?_ ?_ h1 h1' h2 h2'
  · exact hπ.comp (matrixSUEquiv h).symm.surjective
  · intro z hz
    have hz' : π ((matrixSUEquiv h).symm z) = 1 := hz
    have hk : (matrixSUEquiv h).symm z ∈ π.ker := hz'
    have := matrixSUEquiv_scalar h (hker hk)
    simpa using this

theorem matrix_quotient_card_elemAbelian_le {Q : Type*} [Group Q]
    {π : unitarySU 2 f K 3 →* Q} (hπ : Function.Surjective π) (hker : π.ker ≤ unitaryScalars h 3)
    (E : Subgroup Q) (hE : IsElemAbelianTwo E) : Nat.card E ≤ 2 ^ f := by
  refine quotient_card_elemAbelian_le h finrank_idForm (idForm_isSymm h) (idForm_separatingLeft h)
    (π := π.comp (matrixSUEquiv h).symm.toMonoidHom) ?_ ?_ E hE
  · exact hπ.comp (matrixSUEquiv h).symm.surjective
  · intro z hz
    have hz' : π ((matrixSUEquiv h).symm z) = 1 := hz
    have hk : (matrixSUEquiv h).symm z ∈ π.ker := hz'
    have := matrixSUEquiv_scalar h (hker hk)
    simpa using this

end CFSG.QuasithinUnique.Setup.X5
