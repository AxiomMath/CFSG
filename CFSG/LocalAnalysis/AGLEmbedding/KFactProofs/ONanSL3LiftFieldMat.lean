module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftFrame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

open Matrix Polynomial CFSG.LocalAnalysis.RankThreeTheoremC
  CFSG.ComponentClassification.CatalogueBHigherLinearAction

theorem exists_cube_root_or_det_eq {k : Type*} [Field k] (s : Matrix (Fin 3) (Fin 3) k) {ζ : k}
    (hs : s ^ 3 = ζ • (1 : Matrix (Fin 3) (Fin 3) k)) :
    (∃ η : k, η ^ 3 = ζ) ∨ s.det = ζ := by
  by_cases hno : ∃ η : k, η ^ 3 = ζ
  · exact Or.inl hno
  right
  have hno' : ∀ η : k, η ^ 3 ≠ ζ := fun η hη => hno ⟨η, hη⟩
  have hPmonic : (X ^ 3 - C ζ : k[X]).Monic := monic_X_pow_sub_C ζ (by norm_num)
  have hPdeg : (X ^ 3 - C ζ : k[X]).natDegree = 3 := natDegree_X_pow_sub_C
  have hPirr : Irreducible (X ^ 3 - C ζ : k[X]) := by
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [hPdeg]; simp
    · intro x hx
      apply hno' x
      simpa [IsRoot, sub_eq_zero] using hx
  have hPaeval : aeval s (X ^ 3 - C ζ : k[X]) = 0 := by
    simp [hs, Algebra.algebraMap_eq_smul_one]
  have hmin := minpoly.eq_of_irreducible_of_monic hPirr hPaeval hPmonic
  have hdvd := Matrix.minpoly_dvd_charpoly s
  rw [← hmin] at hdvd
  have hχ : s.charpoly = X ^ 3 - C ζ := by
    refine eq_of_monic_of_dvd_of_natDegree_le hPmonic (Matrix.charpoly_monic s) hdvd ?_
    rw [Matrix.charpoly_natDegree_eq_dim, hPdeg]
    simp
  have h0 := Matrix.det_eq_sign_charpoly_coeff s
  rw [hχ] at h0
  simp [coeff_sub, coeff_X_pow, coeff_C] at h0
  linear_combination h0

@[expose] def descend {k : Type*} [Field k] (k₀ : Subfield k) (M : Matrix (Fin 3) (Fin 3) k)
    (hM : ∀ i j, M i j ∈ k₀) : Matrix (Fin 3) (Fin 3) k₀ :=
  Matrix.of fun i j => ⟨M i j, hM i j⟩

theorem descend_map {k : Type*} [Field k] (k₀ : Subfield k) (M : Matrix (Fin 3) (Fin 3) k)
    (hM : ∀ i j, M i j ∈ k₀) : (descend k₀ M hM).map k₀.subtype = M := by
  ext i j
  rfl

theorem descend_pow_three {k : Type*} [Field k] (k₀ : Subfield k) (M : Matrix (Fin 3) (Fin 3) k)
    (hM : ∀ i j, M i j ∈ k₀) {c : k} (hc : c ∈ k₀)
    (hM3 : M ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) k)) :
    descend k₀ M hM ^ 3 = (⟨c, hc⟩ : k₀) • (1 : Matrix (Fin 3) (Fin 3) k₀) := by
  apply Matrix.map_injective k₀.subtype.injective
  show (descend k₀ M hM ^ 3).map k₀.subtype =
    ((⟨c, hc⟩ : k₀) • (1 : Matrix (Fin 3) (Fin 3) k₀)).map k₀.subtype
  have h1 : (descend k₀ M hM ^ 3).map k₀.subtype = ((descend k₀ M hM).map k₀.subtype) ^ 3 := by
    simpa using (map_pow (RingHom.mapMatrix k₀.subtype) (descend k₀ M hM) 3)
  rw [h1, descend_map, hM3]
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem exists_cube_root_or_det_eq_of_subfield {k : Type*} [Field k] (k₀ : Subfield k)
    (M : Matrix (Fin 3) (Fin 3) k) (hM : ∀ i j, M i j ∈ k₀) {c : k} (hc : c ∈ k₀)
    (hM3 : M ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) k)) :
    (∃ η ∈ k₀, η ^ 3 = c) ∨ M.det = c := by
  rcases exists_cube_root_or_det_eq (descend k₀ M hM) (descend_pow_three k₀ M hM hc hM3) with
    ⟨η, hη⟩ | hdet
  · exact Or.inl ⟨η, η.2, congrArg Subtype.val hη⟩
  · right
    have h1 := RingHom.map_det k₀.subtype (descend k₀ M hM)
    rw [RingHom.mapMatrix_apply, descend_map, hdet] at h1
    exact h1.symm

theorem exists_rational_diagonal {k : Type*} [Field k] (k₀ : Subfield k)
    (M : Matrix (Fin 3) (Fin 3) k) (hM : ∀ i j, M i j ∈ k₀) {ε w : k} (hε : ε ∈ k₀)
    (hε0 : ε ≠ 0) (hw : w ∈ k₀) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hM3 : M ^ 3 = (ε ^ 3) • (1 : Matrix (Fin 3) (Fin 3) k)) :
    ∃ (P : GL (Fin 3) k) (u : Fin 3 → k), (∀ i j, (P : Matrix (Fin 3) (Fin 3) k) i j ∈ k₀) ∧
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * M * (P : Matrix (Fin 3) (Fin 3) k) =
        Matrix.diagonal u := by
  let ι : k₀ →+* k := k₀.subtype
  let M₀ := descend k₀ M hM
  have hM₀ : M₀.map ι = M := descend_map k₀ M hM
  let ε₀ : k₀ := ⟨ε, hε⟩
  let w₀ : k₀ := ⟨w, hw⟩
  have hw₀3 : w₀ ^ 3 = 1 := Subtype.ext (by simpa [w₀] using hw3)
  have hw₀1 : w₀ ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have hε₀0 : ε₀ ≠ 0 := fun h => hε0 (congrArg Subtype.val h)
  have hM₀3 : M₀ ^ 3 = (ε₀ ^ 3) • (1 : Matrix (Fin 3) (Fin 3) k₀) := by
    have := descend_pow_three k₀ M hM (pow_mem hε 3) hM3
    rwa [show (⟨ε ^ 3, pow_mem hε 3⟩ : k₀) = ε₀ ^ 3 from Subtype.ext rfl] at this
  have hprod := SL3Lift.prod_sub_cube_roots M₀ hw₀3 hw₀1 hM₀3
  have hinj := SL3Lift.injective_cube_roots hε₀0 hw₀3 hw₀1
  obtain ⟨P₀, a, b, ha, -⟩ := SL3Lift.exists_joint_diagonal M₀ M₀ rfl
    (fun j : Fin 3 => ε₀ * w₀ ^ j.val) (fun j : Fin 3 => ε₀ * w₀ ^ j.val) hinj hinj hprod hprod
  refine ⟨Matrix.GeneralLinearGroup.map ι P₀, fun i => (a i : k), fun i j => ?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.map_apply]
    exact (P₀ i j).2
  · have h1 := congrArg (fun N : Matrix (Fin 3) (Fin 3) k₀ => N.map ι) ha
    simp only [Matrix.map_mul] at h1
    rw [hM₀] at h1
    have e1 : ((Matrix.GeneralLinearGroup.map ι P₀ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        (P₀ : Matrix (Fin 3) (Fin 3) k₀).map ι := rfl
    have e2 : (((Matrix.GeneralLinearGroup.map ι P₀)⁻¹ : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) = ((P₀⁻¹ : GL (Fin 3) k₀) : Matrix (Fin 3) (Fin 3) k₀).map ι := by
      rw [← map_inv]
      rfl
    rw [e1, e2, h1]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [ι]
    · simp [hij]

@[expose] def diagSL {k : Type*} [Field k] (d : Fin 3 → kˣ) (h : ∏ i, (d i : k) = 1) :
    SpecialLinearGroup (Fin 3) k :=
  ⟨Matrix.diagonal fun i => (d i : k), by rw [Matrix.det_diagonal]; exact h⟩

theorem diagSL_mul_transvection {k : Type*} [Field k] (d : Fin 3 → kˣ)
    (h : ∏ i, (d i : k) = 1) {a b : Fin 3} (hab : a ≠ b) (ρ : k) (hρ : (d a : k) = ρ * d b) :
    diagSL d h * SpecialLinearGroup.transvection hab 1 =
      SpecialLinearGroup.transvection hab ρ * diagSL d h := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change ((Matrix.diagonal (fun i => (d i : k)) : Matrix (Fin 3) (Fin 3) k) *
      (1 + Matrix.single a b 1 : Matrix (Fin 3) (Fin 3) k)) i j =
    ((1 + Matrix.single a b ρ : Matrix (Fin 3) (Fin 3) k) *
      (Matrix.diagonal (fun i => (d i : k)) : Matrix (Fin 3) (Fin 3) k)) i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hc : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := hc
    simp [hab, hρ]
  · by_cases hij : i = j
    · subst hij
      simp [hc]
    · simp [hc, hij]

theorem eq_top_of_conj_transvection_diag {k : Type*} [Field k] (P : GL (Fin 3) k)
    (H : Subgroup (SpecialLinearGroup (Fin 3) k))
    (hX : ∀ (a b : Fin 3) (hab : a ≠ b),
      slConjugation 3 k P (SpecialLinearGroup.transvection hab 1) ∈ H)
    (hD : ∀ (d : Fin 3 → kˣ) (hd : ∏ i, (d i : k) = 1), slConjugation 3 k P (diagSL d hd) ∈ H) :
    H = ⊤ := by
  set φ := slConjugation 3 k P with hφ
  have hmem : ∀ x ∈ CFSG.LinearGroups.elementarySet 3 k, φ x ∈ H := by
    rintro x ⟨a, b, hab, t, rfl⟩
    by_cases ht : t = 0
    · subst ht
      have h1 : SpecialLinearGroup.transvection hab (0 : k) = 1 := by
        refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
        simp
      rw [h1, map_one]
      exact H.one_mem
    · let d : Fin 3 → kˣ := fun i =>
        if i = a then Units.mk0 t ht else if i = b then 1 else (Units.mk0 t ht)⁻¹
      have hd : ∏ i, (d i : k) = 1 := by
        fin_cases a <;> fin_cases b <;> simp_all [d, Fin.prod_univ_three]
      have hρ : (d a : k) = t * d b := by simp [d, hab.symm]
      have key : SpecialLinearGroup.transvection hab t =
          diagSL d hd * SpecialLinearGroup.transvection hab 1 * (diagSL d hd)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        exact (diagSL_mul_transvection d hd hab t hρ).symm
      rw [key, map_mul, map_mul, map_inv]
      exact H.mul_mem (H.mul_mem (hD d hd) (hX a b hab)) (H.inv_mem (hD d hd))
  have hgen : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 k) = ⊤ :=
    CFSG.LinearGroups.special_linear_elementary_generation
  rw [eq_top_iff]
  calc (⊤ : Subgroup (SpecialLinearGroup (Fin 3) k))
      = (Subgroup.closure (CFSG.LinearGroups.elementarySet 3 k)).map φ.toMonoidHom := by
        rw [hgen, Subgroup.map_top_of_surjective _ φ.surjective]
    _ = Subgroup.closure (φ.toMonoidHom '' CFSG.LinearGroups.elementarySet 3 k) :=
        MonoidHom.map_closure _ _
    _ ≤ H := (Subgroup.closure_le H).2 (by rintro _ ⟨x, hx, rfl⟩; exact hmem x hx)

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField
