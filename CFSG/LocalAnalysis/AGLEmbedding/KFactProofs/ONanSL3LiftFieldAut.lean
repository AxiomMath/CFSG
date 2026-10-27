module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldArith
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftFrame
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

variable {k : Type} [Field k]

@[expose] def SemiBy (ζ : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)) (τ : k ≃+* k)
    (g : GL (Fin 3) k) : Prop :=
  ∀ s : Matrix.SpecialLinearGroup (Fin 3) k,
    Matrix.SpecialLinearGroup.toGL (ζ s) =
      g * Matrix.GeneralLinearGroup.map (τ : k →+* k) (Matrix.SpecialLinearGroup.toGL s) * g⁻¹

theorem map_map_apply (τ τ' : k ≃+* k) (x : GL (Fin 3) k) :
    Matrix.GeneralLinearGroup.map (τ : k →+* k) (Matrix.GeneralLinearGroup.map (τ' : k →+* k) x) =
      Matrix.GeneralLinearGroup.map ((τ * τ' : k ≃+* k) : k →+* k) x := by
  apply Units.ext
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

theorem SemiBy.mul {ζ ζ' : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)} {τ τ' : k ≃+* k}
    {g g' : GL (Fin 3) k} (h : SemiBy ζ τ g) (h' : SemiBy ζ' τ' g') :
    SemiBy (ζ * ζ') (τ * τ') (g * Matrix.GeneralLinearGroup.map (τ : k →+* k) g') := by
  intro s
  rw [MulAut.mul_apply, h, h', map_mul, map_mul, map_inv, map_map_apply]
  group

theorem semiBy_fieldAut (τ : k ≃+* k) : SemiBy (slFieldAut (Fin 3) k τ) τ 1 := by
  intro s
  rw [one_mul, inv_one, mul_one]
  exact toGL_slFieldEquiv (Fin 3) τ s

theorem semiBy_one_iff {ζ : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)} {g : GL (Fin 3) k} :
    SemiBy ζ 1 g ↔ IsConjBy ζ g := by
  have hid : Matrix.GeneralLinearGroup.map ((1 : k ≃+* k) : k →+* k) =
      MonoidHom.id (GL (Fin 3) k) := Matrix.GeneralLinearGroup.map_id
  constructor
  · intro h t
    have := congrArg Units.val (h t)
    simpa [hid] using this
  · intro h t
    apply Units.ext
    have := h t
    simpa [hid] using this

theorem semiBy_of_conj_fieldAut (H : GL (Fin 3) k) (σ : k ≃+* k) :
    SemiBy (slConjugation 3 k H * slFieldAut (Fin 3) k σ * (slConjugation 3 k H)⁻¹) σ
      (H * Matrix.GeneralLinearGroup.map (σ : k →+* k) H⁻¹) := by
  intro s
  have hF : ∀ t : Matrix.SpecialLinearGroup (Fin 3) k,
      Matrix.SpecialLinearGroup.toGL (slFieldAut (Fin 3) k σ t) =
        Matrix.GeneralLinearGroup.map (σ : k →+* k) (Matrix.SpecialLinearGroup.toGL t) := by
    intro t
    simpa using semiBy_fieldAut σ t
  rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply, toGL_slConjugation, hF, toGL_slConjugation]
  simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]

theorem exists_isConjBy_or_conj_fieldAut [Finite k]
    (β : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)) (hβ : β ^ 3 = 1) :
    (∃ g : GL (Fin 3) k, IsConjBy β g) ∨
      ∃ (σ : k ≃+* k) (H : GL (Fin 3) k), orderOf σ = 3 ∧
        β = slConjugation 3 k H * slFieldAut (Fin 3) k σ * (slConjugation 3 k H)⁻¹ := by
  by_cases hD : descendAut 3 k β ∈ linearAutGroup 3 k
  · obtain ⟨A, hA⟩ := exists_eq_slConjugation_of_descendAut_mem hD
    exact Or.inl ⟨A, fun t => by rw [hA]; exact slConjugation_matrix 3 k A t⟩
  · right
    have hα3 : descendAut 3 k β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
    obtain ⟨σ, hσ3, H, hαH⟩ := linear_order_three_field_descent le_rfl _ hα3 hD
    exact ⟨σ, H, hσ3, eq_of_descendAut_eq (by rw [hαH, map_mul, map_mul, map_inv]; rfl)⟩

theorem exists_isConjBy_or_semiBy [Finite k] (β : MulAut (Matrix.SpecialLinearGroup (Fin 3) k))
    (hβ : β ^ 3 = 1) :
    (∃ g : GL (Fin 3) k, IsConjBy β g) ∨
      ∃ (σ : k ≃+* k) (g : GL (Fin 3) k), orderOf σ = 3 ∧ SemiBy β σ g := by
  rcases exists_isConjBy_or_conj_fieldAut β hβ with h | ⟨σ, H, hσ, hβ'⟩
  · exact Or.inl h
  · exact Or.inr ⟨σ, _, hσ, hβ' ▸ semiBy_of_conj_fieldAut H σ⟩

theorem exists_isConjBy_mul_pow [Finite k] {τ : k ≃+* k} (hτ : orderOf τ = 3)
    (β : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)) (hβ : β ^ 3 = 1) :
    ∃ (m : ℕ) (g : GL (Fin 3) k), IsConjBy (β * slFieldAut (Fin 3) k τ ^ m) g := by
  rcases exists_isConjBy_or_semiBy β hβ with ⟨g, hg⟩ | ⟨σ, g, hσ, hg⟩
  · exact ⟨0, g, by rwa [pow_zero, mul_one]⟩
  · obtain ⟨hcyc, hfin⟩ := isCyclic_ringEquiv k
    have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    obtain ⟨j, hj, hσj⟩ := exists_pow_eq_of_pow_three_eq_one hτ hσ3
    have hτ3 : τ ^ 3 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hσj
      rw [hσj, orderOf_one] at hσ
      exact absurd hσ (by norm_num)
    have h1 : SemiBy (slFieldAut (Fin 3) k τ ^ (3 - j)) (τ ^ (3 - j)) 1 := by
      rw [← map_pow]
      exact semiBy_fieldAut _
    have h2 := hg.mul h1
    have hone : σ * τ ^ (3 - j) = 1 := by
      rw [hσj, ← pow_add, show j + (3 - j) = 3 by omega, hτ3]
    rw [hone] at h2
    exact ⟨3 - j, _, semiBy_one_iff.1 h2⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField
