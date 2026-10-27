module

public import CFSG.Fischer.Classification.Orthogonal3.MinusFive.Iso

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.ClassicalGroups.Orthogonal Matrix QuadraticMap

theorem Orth2.fischerLinearModel_of_mulEquiv_orthogonalGroup {G : Type} [Group G] {D : Set G}
    {n : ℕ} {Q : QuadraticForm (ZMod 2) (Fin n → ZMod 2)}
    (Φ : G ≃* TauCeti.QuadraticMap.orthogonalGroup Q) (hΦ : Φ '' D = Orth2.reflClass Q) :
    fischerLinearModel D (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1) := by
  have hH : (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x).map
      (toLinEquiv (Fin n) (ZMod 2) : GL (Fin n) (ZMod 2) →* _) =
        TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [fischerMatrixGroup_isometry_eq_comap]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv _ _).surjective _
  let ψ := ((toLinEquiv (Fin n) (ZMod 2)).subgroupMap
    (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)).trans (MulEquiv.subgroupCongr hH)
  have hψ : ∀ M, ((ψ M : TauCeti.QuadraticMap.orthogonalGroup Q) :
      (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) =
        toLinEquiv (Fin n) (ZMod 2) (M : GL (Fin n) (ZMod 2)) := fun M => rfl
  refine ⟨Φ.trans ψ.symm, fun g => ?_⟩
  have hM : ψ ((Φ.trans ψ.symm) g) = Φ g := ψ.apply_symm_apply (Φ g)
  constructor
  · intro hg
    obtain ⟨v, hv, hgv⟩ : Φ g ∈ Orth2.reflClass Q := hΦ ▸ ⟨g, hg, rfl⟩
    have : (((Φ.trans ψ.symm) g : _) : GL (Fin n) (ZMod 2)) = orthTransvectionGL Q v := by
      apply (toLinEquiv (Fin n) (ZMod 2)).injective
      rw [← hψ, hM, hgv, toLinEquiv_orthTransvectionGL]
    rw [this]
    exact orthTransvectionGL_mem_fischerTransvections hv
  · intro hg
    obtain ⟨v, hv, hMv⟩ := eq_orthTransvectionGL_of_mem_fischerTransvections hg
    have hmem : Φ g ∈ Orth2.reflClass Q := by
      refine ⟨v, hv, ?_⟩
      rw [← hM, hψ, hMv, toLinEquiv_orthTransvectionGL]
    rw [← hΦ] at hmem
    obtain ⟨g', hg', hgg'⟩ := hmem
    rwa [← Φ.injective hgg']

theorem orth_or_unitary_of_reflection_five {G : Type} [Group G] {D : Set G}
    {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)} (hsymm : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmod : fischerCentralQuotientModel D
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    (∃ Q : QuadraticForm (ZMod 2) (Fin (2 * 3) → ZMod 2),
        (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
        fischerLinearModel D (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
          (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) ∨
      fischerCentralQuotientModel D
        (fischerMatrixGroup fun A => A.det = 1 ∧
          ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
        (fischerTransvections (fischerHermitianF4 4)
          fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0) := by
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨φ, hφ⟩ := (fischerCentralQuotientModel_iff D).1 hmod
  have hφD : φ '' D = D3 f := by
    ext q
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hφ g).1 hg
    · intro hq
      exact ⟨φ.symm q, (hφ _).2 (by rwa [MulEquiv.apply_symm_apply]), φ.apply_symm_apply q⟩
  rcases R3_five_cases hf with ⟨h45, -⟩ | ⟨-, ψ, hψ⟩
  · right
    obtain ⟨χ, hχ⟩ := exists_mulEquiv_U2_four_of_ncard hf h45
    refine fischerCentralQuotientModel_iff_U2.2 ⟨φ.trans χ, ?_⟩
    rw [MulEquiv.coe_trans, Set.image_comp, hφD, hχ]
  · left
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_orthogonalGroup_R3_diagF3_five_two
    refine ⟨MinusFive.qMinusSix, MinusFive.polar_qMinusSix_nondegenerate,
      Orth2.fischerLinearModel_of_mulEquiv_orthogonalGroup ((φ.trans ψ).trans Φ) ?_⟩
    rw [MulEquiv.coe_trans, MulEquiv.coe_trans, Set.image_comp, Set.image_comp, hφD, hψ, hΦ]

end CFSG.Fischer.Classification
