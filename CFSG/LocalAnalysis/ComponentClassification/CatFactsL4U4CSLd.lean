module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLc
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLg

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace CSL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag DiagL

variable {F : Type} [Field F] [Finite F]

theorem conj_injective : Function.Injective (MulAut.conj : projectiveSL 4 F →* _) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨Z, rfl⟩ := proj_surjective 4 F x
  rw [← conjAut_toGL] at hx
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).1 hx
  rw [proj_eq_one_iff]
  apply mem_scalars_of_toGL_mem_center
  rw [← hc, GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨c, rfl⟩

theorem exists_lift_eK (h4 : (4 : F) ≠ 0) {x : projectiveSL 4 F}
    (hx : MulAut.conj x ∈ CA F neg_one_ne_zero') :
    ∃ U : SpecialLinearGroup (Fin 4) F, proj 4 F U = x ∧
      ∃ a b : F, (U : Matrix (Fin 4) (Fin 4) F) = eK (-1) a b := by
  obtain ⟨U, rfl⟩ := proj_surjective 4 F x
  have hAK : MulAut.conj (proj 4 F U) ∈ AK F neg_one_ne_zero' :=
    Subgroup.mem_inf.2 ⟨hx, SpecialLinearGroup.toGL U, conjAut_toGL U⟩
  have hl1 : (-1 : F) ≠ 1 := by
    intro h
    exact h4 (by linear_combination (-2 : F) * h)
  obtain ⟨B, a, b, hB, hBe⟩ := exists_of_mem_AK h4 neg_one_ne_zero' hl1 hAK
  rw [← conjAut_toGL] at hB
  have h1 : conjAut 4 F ((SpecialLinearGroup.toGL U)⁻¹ * B) = 1 := by
    rw [map_mul, map_inv, hB, inv_mul_cancel]
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).1 h1
  refine ⟨U, rfl, a * ((c⁻¹ : Fˣ) : F), b * ((c⁻¹ : Fˣ) : F), ?_⟩
  have h2 : SpecialLinearGroup.toGL U = B * (GeneralLinearGroup.scalar (Fin 4) c)⁻¹ := by
    rw [hc]; group
  have h3 := congrArg (fun A : GL (Fin 4) F => (A : Matrix (Fin 4) (Fin 4) F)) h2
  simp only [Units.val_mul, ← map_inv, GeneralLinearGroup.coe_scalar] at h3
  change (U : Matrix (Fin 4) (Fin 4) F) = _ at h3
  rw [h3, hBe, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
    Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eK, mul_comm]

omit [Finite F] in
theorem conj_mem_CA_of_normalizes {x : projectiveSL 4 F}
    (hx : ∀ y, y ∈ JK F neg_one_ne_zero' ↔ x * y * x⁻¹ ∈ JK F neg_one_ne_zero')
    {g : MulAut (projectiveSL 4 F)} (hg : g ∈ CA F neg_one_ne_zero') :
    (MulAut.conj x)⁻¹ * g * MulAut.conj x ∈ CA F neg_one_ne_zero' := by
  intro y hy
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hg _ ((hx y).1 hy), ← map_inv,
    MulAut.conj_apply]
  group

theorem eq_one_or_eq_kG (h4 : (4 : F) ≠ 0) {τ' : MulAut (projectiveSL 4 F)}
    (hτ : τ' ∈ CA F neg_one_ne_zero') {x₁ x₂ : projectiveSL 4 F}
    (hx₁J : ∀ y, y ∈ JK F neg_one_ne_zero' ↔ x₁ * y * x₁⁻¹ ∈ JK F neg_one_ne_zero')
    (hx₂J : ∀ y, y ∈ JK F neg_one_ne_zero' ↔ x₂ * y * x₂⁻¹ ∈ JK F neg_one_ne_zero')
    (hx₁k : x₁ * proj 4 F kSL = proj 4 F kSL * x₁)
    (hx₂k : x₂ * proj 4 F kSL = proj 4 F kSL * x₂) {c : F} (hc : (2 * c ^ 2) ^ 2 = 1)
    (h₁ : τ' * MulAut.conj (x₁ * proj 4 F (uSL hc) * x₁⁻¹) =
      MulAut.conj (x₁ * proj 4 F (uSL hc) * x₁⁻¹) * τ')
    (h₂ : τ' * MulAut.conj (x₂ * proj 4 F sSL * x₂⁻¹) =
      MulAut.conj (x₂ * proj 4 F sSL * x₂⁻¹) * τ') :
    τ' = 1 ∨ τ' = conjAut 4 F (kG neg_one_ne_zero') := by
  classical
  have hl1 : (-1 : F) ≠ 1 := by
    intro h
    exact h4 (by linear_combination (-2 : F) * h)
  have hll : (-1 : F) * (-1) = 1 := by norm_num
  have hσl : ∀ σ : F ≃+* F, σ (-1) = -1 := fun σ => by rw [map_neg, map_one]
  have hfix : ∀ {g : MulAut (projectiveSL 4 F)} {x : projectiveSL 4 F},
      g * MulAut.conj x = MulAut.conj x * g → g x = x := by
    intro g x h
    apply conj_injective
    rw [← mul_conj_mul_inv, h, mul_inv_cancel_right]
  set u₁ := x₁ * proj 4 F (uSL hc) * x₁⁻¹ with hu₁
  have hu₁CA : MulAut.conj u₁ ∈ CA F neg_one_ne_zero' := by
    intro y hy
    have hy' : x₁⁻¹ * y * x₁ ∈ JK F neg_one_ne_zero' := by
      rw [hx₁J]
      have e : x₁ * (x₁⁻¹ * y * x₁) * x₁⁻¹ = y := by group
      rwa [e]
    have hu := conj_uSL_mem_CA hc _ hy'
    rw [MulAut.conj_apply] at hu ⊢
    calc u₁ * y * u₁⁻¹ = x₁ * (proj 4 F (uSL hc) * (x₁⁻¹ * y * x₁) *
        (proj 4 F (uSL hc))⁻¹) * x₁⁻¹ := by rw [hu₁]; group
      _ = y := by rw [hu]; group
  have hk1 : proj 4 F (kSL : SpecialLinearGroup (Fin 4) F) ≠ 1 := by
    intro h
    have := conjAut_kG_ne_one (F := F) neg_one_ne_zero'
    rw [conjAut_kG_eq, h, map_one] at this
    exact this rfl
  have hu₁sq : u₁ ^ 2 = proj 4 F kSL := by
    have e : u₁ ^ 2 = x₁ * proj 4 F (uSL hc) ^ 2 * x₁⁻¹ := by rw [hu₁, sq, sq]; group
    rw [e, proj_uSL_sq, hx₁k, mul_inv_cancel_right]
  have hrange : τ' ∈ (conjAut 4 F).range := by
    by_contra hnot
    rcases mem_or_exists_mul_dualAut τ' with hE | ⟨e₀, he₀, he⟩
    · exact hnot (mem_range_of_mem_CA h4 neg_one_ne_zero' hl1 hτ hE)
    obtain ⟨B, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 he₀
    obtain ⟨U, hU, a, b, hUe⟩ := exists_lift_eK h4 hu₁CA
    have hinv := apply_of_mem_CA_dual h4 neg_one_ne_zero' hl1 hll B σ (hσl σ) (he ▸ hτ) U hUe
    rw [← he, hU] at hinv
    have hfx := hfix h₁
    rw [hinv] at hfx
    apply hk1
    rw [← hu₁sq, sq]
    nth_rewrite 1 [← hfx]
    exact inv_mul_cancel u₁
  obtain ⟨B, hB⟩ := hrange
  set τ'' := (MulAut.conj x₂)⁻¹ * τ' * MulAut.conj x₂ with hτ''
  have hτ''CA : τ'' ∈ CA F neg_one_ne_zero' := conj_mem_CA_of_normalizes hx₂J hτ
  have hτ''range : τ'' ∈ (conjAut 4 F).range := by
    obtain ⟨X₂, rfl⟩ := proj_surjective 4 F x₂
    refine ⟨(SpecialLinearGroup.toGL X₂)⁻¹ * B * SpecialLinearGroup.toGL X₂, ?_⟩
    rw [map_mul, map_mul, map_inv, conjAut_toGL, hB]
  have hAK : τ'' ∈ AK F neg_one_ne_zero' := Subgroup.mem_inf.2 ⟨hτ''CA, hτ''range⟩
  obtain ⟨B'', a, b, hB'', hB''e⟩ := exists_of_mem_AK h4 neg_one_ne_zero' hl1 hAK
  have hcomm : MulAut.conj (proj 4 F sSL) * τ'' = τ'' * MulAut.conj (proj 4 F sSL) := by
    have e : MulAut.conj (x₂ * proj 4 F sSL * x₂⁻¹) =
        MulAut.conj x₂ * MulAut.conj (proj 4 F sSL) * (MulAut.conj x₂)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [e] at h₂
    calc MulAut.conj (proj 4 F sSL) * τ''
        = (MulAut.conj x₂)⁻¹ * ((MulAut.conj x₂ * MulAut.conj (proj 4 F sSL) *
          (MulAut.conj x₂)⁻¹) * τ') * MulAut.conj x₂ := by rw [hτ'']; group
      _ = (MulAut.conj x₂)⁻¹ * (τ' * (MulAut.conj x₂ * MulAut.conj (proj 4 F sSL) *
          (MulAut.conj x₂)⁻¹)) * MulAut.conj x₂ := by rw [h₂]
      _ = τ'' * MulAut.conj (proj 4 F sSL) := by rw [hτ'']; group
  have hsinv := conj_sSL_inv hB''e
  rw [← hB''] at hsinv
  have hsq : τ'' ^ 2 = 1 := by
    have e : τ'' = τ''⁻¹ := by rw [← hsinv, hcomm, mul_inv_cancel_right]
    rw [sq]
    nth_rewrite 2 [e]
    exact mul_inv_cancel τ''
  have hback : τ' = MulAut.conj x₂ * τ'' * (MulAut.conj x₂)⁻¹ := by rw [hτ'']; group
  rcases eq_one_or_eq_of_sq h4 neg_one_ne_zero' hl1 hAK hsq with h | h
  · left
    rw [hback, h, mul_one, mul_inv_cancel]
  · right
    rw [hback, h, conjAut_kG_eq, mul_conj_mul_inv, MulAut.conj_apply, hx₂k,
      mul_inv_cancel_right]

end CSL

end CFSG.ComponentClassification.CatFactsL4U4
