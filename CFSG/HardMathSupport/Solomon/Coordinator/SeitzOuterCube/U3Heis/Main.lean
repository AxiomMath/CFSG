module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis.MainOne
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (monomGL diagGL)

theorem modelHyperGen_of_eq_map_conj {M : Type*} [Group M] {p : ℕ} {B B' : Subgroup (MulAut M)}
    (α : MulAut M) (hB : B' = B.map (MulAut.conj α).toMonoidHom) (hgen : ModelHyperGen p B) :
    ModelHyperGen p B' := by
  refine modelHyperGen_of_map_conj α⁻¹ ?_
  rw [hB, Subgroup.map_map]
  have e : (MulAut.conj α⁻¹).toMonoidHom.comp (MulAut.conj α).toMonoidHom =
      MonoidHom.id (MulAut M) := by
    ext x y
    simp [MulAut.conj_apply]
  rw [e, Subgroup.map_id]
  exact hgen

theorem sup_zpowers_eq {G : Type*} [Group G] {a b K : G} {k : ℕ} :
    Subgroup.zpowers (a ^ k * b) ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers K) =
      Subgroup.zpowers b ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers K) := by
  have ha : ∀ {H : Subgroup G}, Subgroup.zpowers a ⊔ Subgroup.zpowers K ≤ H →
      a ^ k ∈ H := fun hH => hH (Subgroup.mem_sup_left (Subgroup.npow_mem_zpowers a k))
  apply le_antisymm
  · refine sup_le (Subgroup.zpowers_le.2 ?_) le_sup_right
    exact mul_mem (ha le_sup_right) (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
  · refine sup_le (Subgroup.zpowers_le.2 ?_) le_sup_right
    have h1 : a ^ k * b ∈ Subgroup.zpowers (a ^ k * b) ⊔
        (Subgroup.zpowers a ⊔ Subgroup.zpowers K) :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have h2 : (a ^ k)⁻¹ ∈ Subgroup.zpowers (a ^ k * b) ⊔
        (Subgroup.zpowers a ⊔ Subgroup.zpowers K) := inv_mem (ha le_sup_right)
    have := mul_mem h2 h1
    rwa [inv_mul_cancel_left] at this

variable {ℓ f : ℕ} {F : Type} [Field F]

theorem diagGL_val (a b c : Fˣ) :
    ((diagGL F a b c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![(a : F), b, c] := rfl

theorem diagGL_mem_unitaryIsom3 (h : UnitaryFieldData ℓ f F) {a b c : Fˣ}
    (ha : h.bar (a : F) * a = 1) (hb : h.bar (b : F) * b = 1) (hc : h.bar (c : F) * c = 1) :
    diagGL F a b c ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, diagGL_val]
  exact unitary_diagonal (norm_one_vec ha hb hc)

theorem monomGL_one_mem_unitaryIsom3 (h : UnitaryFieldData ℓ f F) :
    monomGL F 1 ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, monomGL_one_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permP, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.one_apply]


theorem u3ThreeHeisGen_holds : U3ThreeHeisGen := by
  intro ℓ f F _ h hq2 h3 hq8 σ hσ lam ω D X hlam hω hD hX
  have := h.finite
  have hln : h.bar (lam : F) * lam = 1 := by
    have hU := mem_unitaryIsom3.1 X.2
    have e := congrFun (congrFun hU 2) 2
    rw [hX] at e
    simpa [monomGL, Matrix.mul_apply, Fin.sum_univ_three] using e
  obtain ⟨ν, hν3, hνn⟩ := exists_cube_root_of_fixed h hσ h3 hlam hln
  have hν0 := norm_one_ne_zero hνn
  set νu : Fˣ := Units.mk0 ν hν0 with hνu
  have hνuv : (νu : F) = ν := rfl
  have hνin : h.bar ((νu⁻¹ : Fˣ) : F) * ((νu⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, hνuv]
    exact norm_one_inv hνn
  have hδU : diagGL F 1 νu⁻¹ (νu⁻¹ ^ 2) ∈ unitaryIsom3 h :=
    diagGL_mem_unitaryIsom3 h (by rw [Units.val_one, map_one, one_mul]) hνin
      (by rw [Units.val_pow_eq_pow_val]; exact norm_one_pow hνin 2)
  set δ : unitaryIsom3 h := ⟨diagGL F 1 νu⁻¹ (νu⁻¹ ^ 2), hδU⟩ with hδ
  set X₁ : unitaryIsom3 h := ⟨monomGL F 1, monomGL_one_mem_unitaryIsom3 h⟩ with hX₁
  have hω3u : ω ^ 3 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hω.pow_eq_one, Units.val_one])
  have hσω : σ (ω : F) = ω := A2Heis.fixed_primitive_cube_root hσ hω
  have hh1 : HeisHypU h σ 1 ω D X₁ := ⟨hσ, hω3u, map_one σ, hσω, hD, rfl⟩
  have hgen := modelHyperGen_one h hq2 h3 hq8 hh1 hω
  refine modelHyperGen_of_eq_map_conj (psuConj h δ) ?_ hgen
  have hcD : MulAut.conj (psuConj h δ) (psuConj h D) = psuConj h D := by
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD, hδ]
    change diagonal _ * diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hcX : MulAut.conj (psuConj h δ) (psuConj h X₁) = psuConj h X := by
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    refine psuConj_eq_of_eq_scalar_mul (c := νu⁻¹) ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hX, hδ,
      hX₁]
    change diagonal _ * ((monomGL F 1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      scalar (Fin 3) _ * ((monomGL F lam : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        diagonal _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [monomGL, Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply, hνuv, ← hν3] <;>
      field_simp
  have hζ3 : (σ ν / ν) ^ 3 = 1 := by
    rw [div_pow, ← map_pow, hν3, hlam, div_self (Units.ne_zero lam)]
  obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one hζ3
  have hcf : MulAut.conj (psuConj h δ) (psuField h σ) = psuConj h D ^ k * psuField h σ := by
    have e1 := psuField_mul_psuConj_mul_inv σ δ⁻¹
    rw [MulAut.conj_apply]
    have e2 : psuConj h δ * psuField h σ * (psuConj h δ)⁻¹ =
        psuConj h δ * (psuField h σ * psuConj h δ⁻¹ * (psuField h σ)⁻¹) * psuField h σ := by
      rw [map_inv]
      group
    rw [e2, e1, ← map_mul, ← map_pow]
    congr 1
    refine psuConj_eq_of_eq_scalar_mul (c := (1 : Fˣ)) ?_
    rw [map_one, one_mul, Subgroup.coe_mul, Subgroup.coe_pow, hD]
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    change ((diagGL F 1 νu⁻¹ (νu⁻¹ ^ 2) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((glAut σ (diagGL F 1 νu⁻¹ (νu⁻¹ ^ 2))⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((diagGL F 1 ω (ω ^ 2) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ k
    have hinv : ((diagGL F 1 νu⁻¹ (νu⁻¹ ^ 2))⁻¹ : GL (Fin 3) F) = diagGL F 1 νu (νu ^ 2) := by
      apply Units.ext
      rw [diagGL_val]
      exact Units.inv_eq_of_mul_eq_one_left (by
        rw [diagGL_val, diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        fin_cases i <;> simp)
    rw [coe_glAut, hinv, diagGL_val, diagGL_val, diagGL_val, diagonal_map (map_zero σ),
      diagonal_mul_diagonal, diagonal_pow]
    congr 1
    funext i
    fin_cases i
    · simp
    · change (ν⁻¹ : F) * σ ν = (ω : F) ^ k
      rw [hk, mul_comm, ← div_eq_mul_inv]
    · change (ν⁻¹ ^ 2 : F) * σ (ν ^ 2) = ((ω : F) ^ 2) ^ k
      rw [← pow_mul, mul_comm 2 k, pow_mul, hk, map_pow, div_pow, inv_pow, mul_comm,
        ← div_eq_mul_inv]
  rw [heisCubeU, heisCubeU, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  change _ = Subgroup.zpowers (MulAut.conj (psuConj h δ) (psuField h σ)) ⊔
    (Subgroup.zpowers (MulAut.conj (psuConj h δ) (psuConj h D)) ⊔
      Subgroup.zpowers (MulAut.conj (psuConj h δ) (psuConj h X₁)))
  rw [hcf, hcD, hcX, sup_zpowers_eq]

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis
