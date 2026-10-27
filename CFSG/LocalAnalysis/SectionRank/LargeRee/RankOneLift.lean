module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.LieType.Steinberg CFSG.SectionRank.EvenCover CFSG.BenderSuzuki.MatrixGroups Matrix

section Suzuki

variable {a : ℕ} {K : Type} [Field K] [Finite K] {G E : Type*} [Group G] [Group E] [Finite E]
  {π : E →* G}

theorem existsUnique_suzukiGroup_lift (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (ψ : CFSG.Blueprint.suzukiGroup a K →* G) :
    ∃! ρ : CFSG.Blueprint.suzukiGroup a K →* E, π.comp ρ = ψ := by
  obtain ⟨a', ha', ⟨e⟩⟩ :=
    CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel
      (G := CFSG.Blueprint.suzukiGroup a K) (p := 2) (f := 2 * a + 1)
      ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨MulEquiv.refl _⟩⟩
  set ψ' : SuzukiMatrixGroup a' →* G := ψ.comp e.symm.toMonoidHom with hψ'
  obtain ⟨⟨σ, hσ, huniq⟩, -⟩ := suzuki_odd_central_extension_splitting a' (by omega)
    (pullbackFst π ψ') (pullbackFst_surjective hπ ψ') (pullbackFst_ker_le_center hcen ψ')
    (hodd.of_dvd_nat (card_pullbackFst_ker_dvd π ψ'))
  have hσ' : ∀ g, pullbackFst π ψ' (σ g) = g := fun g => DFunLike.congr_fun hσ g
  set ρ' : SuzukiMatrixGroup a' →* E :=
    (MonoidHom.snd _ E).comp ((pullback π ψ').subtype.comp σ) with hρ'def
  have hρ' : π.comp ρ' = ψ' := comp_snd_section σ hσ'
  refine ⟨ρ'.comp e.toMonoidHom, ?_, fun ρ hρ => ?_⟩
  · ext x
    have h := DFunLike.congr_fun hρ' (e x)
    simp only [MonoidHom.comp_apply, hψ', MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h
    simpa using h
  ·
    have hρe : ∀ s, ψ' s = π (ρ (e.symm s)) := fun s => by
      rw [hψ', MonoidHom.comp_apply, ← hρ]
      rfl
    let τ : SuzukiMatrixGroup a' →* pullback π ψ' :=
      ((MonoidHom.id _).prod (ρ.comp e.symm.toMonoidHom)).codRestrict _ fun s => hρe s
    have hτ : (pullbackFst π ψ').comp τ = MonoidHom.id _ := by
      ext s
      rfl
    have hτσ := huniq τ hτ
    ext x
    have h := congrArg (fun f : SuzukiMatrixGroup a' →* pullback π ψ' =>
      ((f (e x) : pullback π ψ') : SuzukiMatrixGroup a' × E).2) hτσ
    simpa [τ, ρ'] using h

theorem exists_suzukiGroup_lift (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (ψ : CFSG.Blueprint.suzukiGroup a K →* G) :
    ∃ ρ : CFSG.Blueprint.suzukiGroup a K →* E, π.comp ρ = ψ :=
  (existsUnique_suzukiGroup_lift ha hK hπ hcen hodd ψ).exists

end Suzuki

section SLTwo

variable {K : Type} [Field K]

theorem coe_sl2Weyl :
    ((sl2Weyl : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] :=
  rfl

theorem coe_sl2Diag (t : Kˣ) :
    ((sl2Diag t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] :=
  rfl

theorem sl2Weyl_conj_sl2Diag (t : Kˣ) :
    sl2Weyl * sl2Diag t * sl2Weyl⁻¹ = (sl2Diag t)⁻¹ := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_sl2Weyl,
    coe_sl2Diag]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]

variable [CharP K 2]

theorem sl2Weyl_mul_self : (sl2Weyl : SpecialLinearGroup (Fin 2) K) * sl2Weyl = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Weyl, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

theorem sl2Weyl_mul_sl2Upper_mul_sl2Weyl (c : K) (hc : c ≠ 0) :
    sl2Weyl * sl2Upper c * sl2Weyl =
      sl2Diag (Units.mk0 c hc)⁻¹ * sl2Upper c * sl2Weyl * sl2Upper c⁻¹ := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Weyl, coe_sl2Diag, coe_sl2Upper]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, hc, CharTwo.add_self_eq_zero]

theorem sl2Weyl_mul_sl2Upper_zero_mul_sl2Weyl :
    (sl2Weyl : SpecialLinearGroup (Fin 2) K) * sl2Upper 0 * sl2Weyl = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Weyl, coe_sl2Upper,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

end SLTwo

end CFSG.SectionRank.LargeRee
