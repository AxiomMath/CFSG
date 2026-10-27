module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.CharacterTheory.Semidihedral.MatrixTorus

public section

namespace CFSG.GH74.GLS.IVK.L2Torus

open Matrix CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.MatrixCoverData
  CFSG.Assembly.LowTwoRank

theorem scalar_sq_facts {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (g : Matrix (Fin 2) (Fin 2) F)
    (c : F) (hdet : g.det ≠ 0) (hg2 : g * g = c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hns : ¬ ∃ s : F, g = s • (1 : Matrix (Fin 2) (Fin 2) F)) :
    g 1 1 = -g 0 0 ∧ c = -g.det ∧
      ∃ v : Fin 2 → F, v 0 * (g.mulVec v) 1 - (g.mulVec v) 0 * v 1 ≠ 0 := by
  have h00 := congrFun (congrFun hg2 0) 0
  have h01 := congrFun (congrFun hg2 0) 1
  have h10 := congrFun (congrFun hg2 1) 0
  have h11 := congrFun (congrFun hg2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have hd := Matrix.det_fin_two g
  have htr : g 1 1 = -g 0 0 := by
    by_contra hne
    have hs : g 0 0 + g 1 1 ≠ 0 := fun h => hne (by linear_combination h)
    have hb : g 0 1 = 0 := by
      have : g 0 1 * (g 0 0 + g 1 1) = 0 := by linear_combination h01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : g 1 0 = 0 := by
      have : g 1 0 * (g 0 0 + g 1 1) = 0 := by linear_combination h10
      exact (mul_eq_zero.1 this).resolve_right hs
    have had : g 0 0 = g 1 1 := by
      have : (g 0 0 - g 1 1) * (g 0 0 + g 1 1) = 0 := by
        rw [hb, hc] at h00 h11
        linear_combination h00 - h11
      exact sub_eq_zero.mp ((mul_eq_zero.1 this).resolve_right hs)
    apply hns
    refine ⟨g 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had]
  refine ⟨htr, ?_, ?_⟩
  · rw [hd, htr]
    linear_combination (-1 : F) * h00
  · by_cases hc : g 1 0 = 0
    · by_cases hb : g 0 1 = 0
      · refine ⟨![1, 1], ?_⟩
        have hdet' : g 0 0 ≠ 0 := by
          intro ha
          apply hdet
          rw [hd, htr, ha, hb]
          ring
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hb, hc, htr]
        intro h
        apply hdet'
        have : (2 : F) * g 0 0 = 0 := by linear_combination -h
        exact (mul_eq_zero.1 this).resolve_left h2
      · refine ⟨![0, 1], ?_⟩
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hb]
    · refine ⟨![1, 0], ?_⟩
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc]

variable {F : Type*} [Field F]

theorem exists_conj_J_det (h2 : (2 : F) ≠ 0) (g : GL2 F) (c : F)
    (hg2 : (g : Matrix (Fin 2) (Fin 2) F) * g = c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hns : ¬ ∃ s : F, (g : Matrix (Fin 2) (Fin 2) F) = s • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ∃ P : GL2 F, g = P * J F (GeneralLinearGroup.det g) * P⁻¹ ∧
      c = -((GeneralLinearGroup.det g : Fˣ) : F) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    simpa using (GeneralLinearGroup.det g).ne_zero
  obtain ⟨htr, hc, v, hv⟩ := scalar_sq_facts h2 (g : Matrix (Fin 2) (Fin 2) F) c hdet hg2 hns
  have hdetg : ((GeneralLinearGroup.det g : Fˣ) : F) = (g : Matrix (Fin 2) (Fin 2) F).det := rfl
  let M : Matrix (Fin 2) (Fin 2) F :=
    !![v 0, ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) 0; v 1,
      ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) 1]
  have hM : M.det ≠ 0 := by simpa [M, Matrix.det_fin_two_of] using hv
  have hac : c = -((GeneralLinearGroup.det g : Fˣ) : F) := by rw [hdetg]; exact hc
  refine ⟨GeneralLinearGroup.mkOfDetNeZero M hM, ?_, hac⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  have hgv : (g : Matrix (Fin 2) (Fin 2) F).mulVec ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) =
      c • v := by
    rw [Matrix.mulVec_mulVec, hg2, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h0 := congrFun hgv 0
  have h1 := congrFun hgv 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at h0 h1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, J_matrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
  · rw [h0, hc]; ring
  · rw [h1, hc]; ring

theorem centralizer_comap_eq_map_torus (g P : GL2 F) (a : Fˣ) (hP : g = P * J F a * P⁻¹) :
    (Subgroup.centralizer ({g} : Set (GL2 F))).comap
        (SpecialLinearGroup.toGL : SL F →* GL2 F) =
      (Torus F a).map (slConjugation F P).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv]
  obtain ⟨y', rfl⟩ := (slConjugation F P).surjective y
  rw [MulEquiv.symm_apply_apply, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  have hTorus : y' ∈ Torus F a ↔
      SpecialLinearGroup.toGL y' * J F a = J F a * SpecialLinearGroup.toGL y' := by
    change SpecialLinearGroup.toGL y' ∈ Subgroup.centralizer {J F a} ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff]
  rw [hTorus, slConjugation_toGL, hP]
  have e1 : P * SpecialLinearGroup.toGL y' * P⁻¹ * (P * J F a * P⁻¹) =
      P * (SpecialLinearGroup.toGL y' * J F a) * P⁻¹ := by group
  have e2 : P * J F a * P⁻¹ * (P * SpecialLinearGroup.toGL y' * P⁻¹) =
      P * (J F a * SpecialLinearGroup.toGL y') * P⁻¹ := by group
  rw [e1, e2, mul_left_inj, mul_right_inj]

end CFSG.GH74.GLS.IVK.L2Torus

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.MatrixCoverData

theorem slCentralizer_outer_involution {F : Type} [Field F] [Finite F] (hF : L2Field F) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hq : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (d : ℕ)
    (hd : (d : ℤ) = Nat.card F + ε) (g : GL (Fin 2) F)
    (hg2 : ∃ c : F, (g : Matrix (Fin 2) (Fin 2) F) * g = c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hns : ¬ ∃ s : F, (g : Matrix (Fin 2) (Fin 2) F) = s • (1 : Matrix (Fin 2) (Fin 2) F))
    (hdet : ¬ IsSquare (g : Matrix (Fin 2) (Fin 2) F).det) :
    IsCyclic ↥(slCentralizer g) ∧ Nat.card ↥(slCentralizer g) = d := by
  classical
  obtain ⟨c, hc⟩ := hg2
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hF.1
  obtain ⟨P, hP, hcdet⟩ := L2Torus.exists_conj_J_det h2 g c hc hns
  set a : Fˣ := Matrix.GeneralLinearGroup.det g with ha
  have hadet : (a : F) = (g : Matrix (Fin 2) (Fin 2) F).det := rfl
  let e := specialLinearGroupEquivStatedSL 2 F
  have hcent : slCentralizer g = ((Subgroup.centralizer ({g} : Set (GL (Fin 2) F))).comap
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F)).map
        e.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv]
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [MulEquiv.symm_apply_apply]
    exact Iff.rfl
  rw [hcent, L2Torus.centralizer_comap_eq_map_torus g P a hP, Subgroup.map_map]
  set cc : Matrix.SpecialLinearGroup (Fin 2) F →* StatedSL 2 F :=
    e.toMonoidHom.comp (slConjugation F P).toMonoidHom with hcc
  have hinj : Function.Injective cc := e.injective.comp (slConjugation F P).injective
  have eq1 := Subgroup.equivMapOfInjective (Torus F a) cc hinj
  have hcard : Nat.card ((Torus F a).map cc) = Nat.card (Torus F a) :=
    Subgroup.card_map_of_injective hinj
  have hsqiff : IsSquare (-1 : F) ↔ Nat.card F % 4 ≠ 3 := by
    have := Fintype.ofFinite F
    rw [FiniteField.isSquare_neg_one_iff, Nat.card_eq_fintype_card]
  have hq4 : (Nat.card F : ℤ) % 4 = ε % 4 := hq
  have hqpos : 0 < Nat.card F := Nat.card_pos
  rcases hε with rfl | rfl
  ·
    have h41 : Nat.card F % 4 = 1 := by omega
    have hs1 : IsSquare (-1 : F) := hsqiff.2 (by omega)
    have hns' : ¬ IsSquare (-(a : F)) := by
      intro hsq
      apply hdet
      have : IsSquare ((-1 : F) * -(a : F)) := hs1.mul hsq
      simpa [hadet] using this
    refine ⟨?_, ?_⟩
    · exact eq1.isCyclic.1 (nonsplit_torus_cyclic F a hns')
    · rw [hcard, nonsplit_torus_card F a hns']
      omega
  ·
    have h43 : Nat.card F % 4 = 3 := by omega
    have hn1 : ¬ IsSquare (-1 : F) := fun h => (hsqiff.1 h) h43
    have hsq : IsSquare (-(a : F)) := by
      have := Fintype.ofFinite F
      have ha0 : (a : F) ≠ 0 := a.ne_zero
      have hχ1 : quadraticChar F (-1) = -1 := quadraticChar_neg_one_iff_not_isSquare.2 hn1
      have hχa : quadraticChar F (a : F) = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.2 (by rw [hadet]; exact hdet)
      have : quadraticChar F (-(a : F)) = 1 := by
        have h' : -(a : F) = (-1 : F) * a := by ring
        rw [h', map_mul, hχ1, hχa]
        norm_num
      exact (quadraticChar_one_iff_isSquare (neg_ne_zero.2 ha0)).1 this
    refine ⟨?_, ?_⟩
    · exact eq1.isCyclic.1 (split_torus_cyclic F a h2 hsq)
    · rw [hcard, split_torus_card F a h2 hsq]
      omega

end CFSG.GH74.GLS.IVK
