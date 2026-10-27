module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegCrit
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSLComplex
import CFSG.RankThree.PartTwo.Census.OddClassical.Component

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ClassicalInvolution.Q3
open scoped MatrixGroups commutatorElement

theorem componentAt_quotient {H : Type*} [Group H] (N : Subgroup H) [N.Normal] {t : H}
    {J : Subgroup H} (hJt : ∀ j ∈ J, j * t * j⁻¹ * t⁻¹ ∈ N)
    (hJn : ∀ g : H, g * t * g⁻¹ * t⁻¹ ∈ N → ∀ j ∈ J, g * j * g⁻¹ ∈ J)
    (hJN : IsPGroup 2 (J ⊓ N : Subgroup H)) (hperf : ⁅J, J⁆ = J)
    (hJ2 : ∀ M : Subgroup H, M ≤ J → (∀ g ∈ J, ∀ m ∈ M, g * m * g⁻¹ ∈ M) → IsPGroup 2 M →
      M ≤ Subgroup.centralizer (J : Set H))
    (hJ : ¬ IsPGroup 2 J) : ComponentAt (QuotientGroup.mk t : H ⧸ N) := by
  set π := QuotientGroup.mk' N with hπ
  have h2elt : ∀ x ∈ J, ∀ k : ℕ, π (x ^ 2 ^ k) = 1 → ∃ l : ℕ, x ^ 2 ^ l = 1 := by
    intro x hx k hk
    have hmem : x ^ 2 ^ k ∈ J ⊓ N :=
      Subgroup.mem_inf.mpr ⟨J.pow_mem hx _, (QuotientGroup.eq_one_iff _).mp hk⟩
    obtain ⟨l, hl⟩ := hJN ⟨_, hmem⟩
    refine ⟨k + l, ?_⟩
    have := congrArg Subtype.val hl
    rw [pow_add, pow_mul]
    simpa using this
  have hcomm : ∀ g : H, g * t * g⁻¹ * t⁻¹ ∈ N ↔ π g * π t = π t * π g := by
    intro g
    rw [← QuotientGroup.eq_one_iff (N := N)]
    change π (g * t * g⁻¹ * t⁻¹) = 1 ↔ _
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    constructor
    · intro h
      calc π g * π t = π g * π t * (π g)⁻¹ * (π t)⁻¹ * (π t * π g) := by group
        _ = π t * π g := by rw [h, one_mul]
    · intro h
      rw [h]
      group
  refine ⟨J.map π, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm j).mp (hJt j hj)
  · intro g hg e he
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective N g
    obtain ⟨j, hj, rfl⟩ := he
    have h1 := (hcomm g').mpr (Subgroup.mem_centralizer_singleton_iff.mp hg)
    exact ⟨g' * j * g'⁻¹, hJn g' h1 j hj, by rw [map_mul, map_mul, map_inv]⟩
  · rw [← Subgroup.map_commutator, hperf]
  · intro h2
    apply hJ
    intro x
    obtain ⟨k, hk⟩ := h2 ⟨π x, ⟨x, x.2, rfl⟩⟩
    have hk' : π ((x : H) ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    obtain ⟨l, hl⟩ := h2elt _ x.2 k hk'
    exact ⟨l, Subtype.ext (by simpa using hl)⟩
  · intro M hMJ hMn hM2
    set M' : Subgroup H := (M.comap π) ⊓ J
    have hM'2 : IsPGroup 2 M' := by
      intro x
      obtain ⟨k, hk⟩ := hM2 ⟨π x, (Subgroup.mem_inf.mp x.2).1⟩
      have hk' : π ((x : H) ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      obtain ⟨l, hl⟩ := h2elt _ (Subgroup.mem_inf.mp x.2).2 k hk'
      exact ⟨l, Subtype.ext (by simpa using hl)⟩
    have hM'n : ∀ g ∈ J, ∀ m ∈ M', g * m * g⁻¹ ∈ M' := by
      intro g hg m hm
      obtain ⟨hmM, hmJ⟩ := Subgroup.mem_inf.mp hm
      refine Subgroup.mem_inf.mpr ⟨?_, J.mul_mem (J.mul_mem hg hmJ) (J.inv_mem hg)⟩
      change π (g * m * g⁻¹) ∈ M
      rw [map_mul, map_mul, map_inv]
      exact hMn (π g) ⟨g, hg, rfl⟩ (π m) hmM
    have hM'c := hJ2 M' inf_le_right hM'n hM'2
    intro x hx
    obtain ⟨j, hj, rfl⟩ := hMJ hx
    have hjM' : j ∈ M' := Subgroup.mem_inf.mpr ⟨hx, hj⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j', hj', rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hM'c hjM') j' hj'
    rw [← map_mul, ← map_mul, this]

section Conj

variable {F : Type} [Field F]

@[expose] def gaussConjMatrix (F : Type) [Field F] :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F :=
  Matrix.diagonal fun x => if x.2 = 0 then 1 else -1

theorem gaussConjMatrix_mul_self : gaussConjMatrix F * gaussConjMatrix F = 1 := by
  rw [gaussConjMatrix, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  split_ifs <;> simp

theorem det_gaussConjMatrix : (gaussConjMatrix F).det = 1 := by
  simp [gaussConjMatrix, Matrix.det_diagonal, Fintype.prod_prod_type, Fin.prod_univ_two]

theorem gaussConjMatrix_mul_gaussIota_mul (A : Matrix (Fin 2) (Fin 2) (GaussField F)) :
    gaussConjMatrix F * gaussIota 2 A * gaussConjMatrix F =
      gaussIota 2 (A.map (starRingEnd (GaussField F))) := by
  ext ⟨k, p⟩ ⟨l, q⟩
  rw [gaussConjMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul, gaussIota_apply,
    gaussIota_apply]
  fin_cases p <;> fin_cases q <;> simp [gaussRho, starRingEnd_apply]

theorem starRingEnd_gaussOmega : starRingEnd (GaussField F)
    (QuadraticAlgebra.omega : GaussField F) = -QuadraticAlgebra.omega := by
  ext <;> simp [starRingEnd_apply]

theorem gaussConjMatrix_mul_gaussOmega :
    gaussConjMatrix F * gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F))
      = -(gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)) *
        gaussConjMatrix F) := by
  set G := gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)) with hG
  have h := gaussConjMatrix_mul_gaussIota_mul (F := F)
    (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F))
  have h2 : (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)).map
      (starRingEnd (GaussField F)) =
        -Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F) := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply, starRingEnd_gaussOmega]
    · simp [Matrix.scalar_apply, hij]
  rw [h2, map_neg, ← hG] at h
  calc gaussConjMatrix F * G
      = gaussConjMatrix F * G * gaussConjMatrix F * gaussConjMatrix F := by
        rw [Matrix.mul_assoc _ (gaussConjMatrix F) (gaussConjMatrix F), gaussConjMatrix_mul_self,
          Matrix.mul_one]
    _ = -G * gaussConjMatrix F := by rw [h]
    _ = -(G * gaussConjMatrix F) := Matrix.neg_mul _ _

@[expose] def gaussConjSL (F : Type) [Field F] : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F :=
  ⟨gaussConjMatrix F, det_gaussConjMatrix⟩

theorem coe_gaussConjSL : ((gaussConjSL F : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) = gaussConjMatrix F := rfl

theorem gaussConjSL_mul_self : gaussConjSL F * gaussConjSL F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_gaussConjSL, gaussConjMatrix_mul_self,
    Matrix.SpecialLinearGroup.coe_one]

theorem gaussConjSL_inv : (gaussConjSL F)⁻¹ = gaussConjSL F :=
  inv_eq_of_mul_eq_one_right gaussConjSL_mul_self

end Conj

section Normalizer

variable {F : Type} [Field F] [Finite F] [Fact (¬ IsSquare (-1 : F))]

theorem gaussConjSL_mul_gaussTheta_mul (hF : Nat.card F = 3)
    (S : Matrix.SpecialLinearGroup (Fin 2) (GaussField F)) :
    gaussConjSL F * gaussTheta hF (le_refl 2) S * gaussConjSL F =
      gaussTheta hF (le_refl 2)
        (Matrix.SpecialLinearGroup.map (starRingEnd (GaussField F)) S) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_gaussTheta,
    coe_gaussTheta, coe_gaussConjSL, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply]
  exact gaussConjMatrix_mul_gaussIota_mul _

theorem conj_gaussTheta_mem_range_of_commute (hF : Nat.card F = 3)
    {g b : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F}
    (hg : (g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) =
      gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)))
    (hb : b * g = g * b) (S : Matrix.SpecialLinearGroup (Fin 2) (GaussField F)) :
    b * gaussTheta hF (le_refl 2) S * b⁻¹ ∈ (gaussTheta hF (le_refl 2)).range := by
  have hcomm : ∀ x : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F, x * g = g * x →
      (x : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) *
        gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)) =
      gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)) * x := by
    intro x hx
    have h' := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F =>
      (y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F)) hx
    simpa only [Matrix.SpecialLinearGroup.coe_mul, hg] using h'
  obtain ⟨A, hA⟩ := exists_gaussIota_of_commute 2 (hcomm b hb)
  obtain ⟨A', hA'⟩ := exists_gaussIota_of_commute 2 (hcomm b⁻¹ (Commute.inv_left hb).eq)
  have hAA : A * A' = 1 := by
    apply gaussIota_injective 2
    rw [map_mul, hA, hA', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, map_one]
  have hdet : (A * (S : Matrix (Fin 2) (Fin 2) (GaussField F)) * A').det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, S.2, mul_one, ← Matrix.det_mul, hAA, Matrix.det_one]
  refine ⟨⟨A * (S : Matrix (Fin 2) (Fin 2) (GaussField F)) * A', hdet⟩, ?_⟩
  apply Subtype.ext
  show gaussIota 2 (A * (S : Matrix (Fin 2) (Fin 2) (GaussField F)) * A') =
    ((b * gaussTheta hF (le_refl 2) S * b⁻¹ : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) :
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, map_mul, map_mul,
    hA, hA', coe_gaussTheta]

theorem conj_gaussTheta_mem_range_of_anticommute (hF : Nat.card F = 3)
    {g b : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F}
    (hg : (g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) =
      gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)))
    (hb : (b : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) * g =
      -((g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) * b))
    (S : Matrix.SpecialLinearGroup (Fin 2) (GaussField F)) :
    b * gaussTheta hF (le_refl 2) S * b⁻¹ ∈ (gaussTheta hF (le_refl 2)).range := by
  have hτg : ((gaussConjSL F : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) :
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) * g =
      -((g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) *
        (gaussConjSL F : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F)) := by
    rw [hg, coe_gaussConjSL]
    exact gaussConjMatrix_mul_gaussOmega
  have hc : gaussConjSL F * b * g = g * (gaussConjSL F * b) := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    calc ((gaussConjSL F : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) :
          Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) * b * g
        = (gaussConjSL F : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) *
          ((b : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) * g) := Matrix.mul_assoc _ _ _
      _ = (gaussConjSL F : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) *
          -((g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) * b) := by rw [hb]
      _ = -((gaussConjSL F : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) * g * b) := by
          rw [Matrix.mul_neg, Matrix.mul_assoc]
      _ = -(-((g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) *
            (gaussConjSL F : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F)) * b) := by rw [hτg]
      _ = g * ((gaussConjSL F : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) * b) := by
          rw [Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  obtain ⟨S', hS'⟩ := conj_gaussTheta_mem_range_of_commute hF hg hc S
  have hbS : b * gaussTheta hF (le_refl 2) S * b⁻¹ =
      gaussConjSL F * (gaussConjSL F * b * gaussTheta hF (le_refl 2) S *
        (gaussConjSL F * b)⁻¹) * gaussConjSL F := by
    calc b * gaussTheta hF (le_refl 2) S * b⁻¹
        = (gaussConjSL F)⁻¹ * (gaussConjSL F * b * gaussTheta hF (le_refl 2) S *
            (gaussConjSL F * b)⁻¹) * gaussConjSL F := by group
      _ = _ := by rw [gaussConjSL_inv]
  rw [hbS, ← hS', gaussConjSL_mul_gaussTheta_mul]
  exact ⟨_, rfl⟩

theorem componentAt_gaussOmega (hF : Nat.card F = 3)
    (hZ : IsPGroup 2 (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F)))
    (g : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F)
    (hg : (g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) =
      gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F))) :
    ComponentAt (QuotientGroup.mk g : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F)) := by
  have h4 : 4 ≤ Nat.card (GaussField F) := by rw [card_gaussField_eq_nine hF]; norm_num
  have hodd : Odd (Nat.card (GaussField F)) := by rw [card_gaussField_eq_nine hF]; decide
  let e : ↥(gaussTheta hF (le_refl 2)).range ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaussField F) :=
    (MonoidHom.ofInjective (gaussTheta_injective hF (le_refl 2))).symm
  have hscal : ∀ A : Matrix (Fin 2) (Fin 2) (GaussField F),
      A * Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F) =
        Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F) * A := fun A =>
    (Matrix.scalar_commute _ (fun r => Commute.all _ r) A).eq.symm
  have hJc : ∀ S : Matrix.SpecialLinearGroup (Fin 2) (GaussField F),
      gaussTheta hF (le_refl 2) S * g = g * gaussTheta hF (le_refl 2) S := by
    intro S
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, coe_gaussTheta,
      ← map_mul, ← map_mul, hscal]
  refine componentAt_quotient (Subgroup.center _) (J := (gaussTheta hF (le_refl 2)).range) ?_ ?_
    (hZ.to_le inf_le_right)
    (CFSG.RankThree.PartTwo.Census.commutator_eq_self_of_mulEquiv_sl2 h4 e)
    (CFSG.RankThree.PartTwo.Census.le_centralizer_of_mulEquiv_sl2 h4 hodd e)
    (CFSG.RankThree.PartTwo.Census.not_isPGroup_two_of_mulEquiv_sl2 hodd e)
  · rintro _ ⟨S, rfl⟩
    rw [hJc S]
    simp
  · intro b hb j hj
    obtain ⟨S, rfl⟩ := hj
    obtain ⟨r, hr, hrb⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hb
    have h2 : (b : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) * g =
        Matrix.scalar (Fin 2 × Fin 2) r * g * b := by
      generalize hz : b * g * b⁻¹ * g⁻¹ = z at hrb
      have h1 : b * g = z * g * b := by rw [← hz]; group
      have h3 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F =>
        (x : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F)) h1
      simp only [Matrix.SpecialLinearGroup.coe_mul] at h3
      rw [← hrb] at h3
      exact h3
    have hr1 : r = 1 ∨ r = -1 := by
      have h4 : (r ^ 2) ^ 2 = 1 := by
        rw [Fintype.card_prod, Fintype.card_fin] at hr
        rw [← pow_mul]
        simpa using hr
      rcases sq_eq_one_iff.mp h4 with h | h
      · exact sq_eq_one_iff.mp h
      · exact absurd ⟨r, by rw [← h]; ring⟩ (Fact.out : ¬ IsSquare (-1 : F))
    rcases hr1 with rfl | rfl
    · refine conj_gaussTheta_mem_range_of_commute hF hg ?_ S
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      simpa using h2
    · refine conj_gaussTheta_mem_range_of_anticommute hF hg ?_ S
      rw [h2, map_neg, map_one]
      simp

end Normalizer

theorem exists_gaussBasis {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) {n : ℕ}
    (hn : 3 ≤ n) (g : Matrix.SpecialLinearGroup (Fin n) F)
    (hg2 : (g : Matrix (Fin n) (Fin n) F) * g = -1) :
    ∃ (m : ℕ) (c : Module.Basis (Fin m × Fin 2) F (Fin n → F)), n = m * 2 ∧
      ((specialLinearBasisEquiv c g : Matrix.SpecialLinearGroup (Fin m × Fin 2) F) :
        Matrix (Fin m × Fin 2) (Fin m × Fin 2) F) =
        gaussIota m (Matrix.scalar (Fin m) (QuadraticAlgebra.omega : GaussField F)) := by
  have hns := not_isSquare_neg_one_of_card_eq_three hF
  have hnpos : 0 < n := by omega
  have : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  set f : Module.End F (Fin n → F) :=
    Matrix.toLinAlgEquiv' (R := F) (n := Fin n) (g : Matrix (Fin n) (Fin n) F) with hf_def
  have hff : f * f = (-1 : F) • (1 : Module.End F (Fin n → F)) := by
    rw [hf_def, ← map_mul, hg2, map_neg, map_one]
    exact (neg_one_smul F _).symm
  have hf : ∀ c : F, f ≠ c • (1 : Module.End F (Fin n → F)) := by
    intro c hc
    apply hns
    refine ⟨c, ?_⟩
    have h1 : (g : Matrix (Fin n) (Fin n) F) = c • 1 := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [← hf_def, hc, map_smul, map_one]
    have h2 := congrFun (congrFun hg2 ⟨0, hnpos⟩) ⟨0, hnpos⟩
    rw [h1] at h2
    simp at h2
    linear_combination -h2
  have hd : ∀ l : F, l ^ 2 ≠ -1 := fun l hl => hns ⟨l, by rw [← hl]; ring⟩
  obtain ⟨m, c, hc⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.exists_pair_basis hf hff hd
  set c' : Module.Basis (Fin m × Fin 2) F (Fin n → F) :=
    c.reindex (Equiv.prodComm (Fin 2) (Fin m)) with hc'
  have hc'_apply : ∀ k p, c' (k, p) = c (p, k) := fun k p => by simp [hc']
  have hf0 : ∀ l, f (c' (l, 0)) = c' (l, 1) := fun l => by
    rw [hc'_apply, hc'_apply]
    exact (hc l).symm
  have hf1 : ∀ l, f (c' (l, 1)) = - c' (l, 0) := fun l => by
    rw [← hf0, ← Module.End.mul_apply, hff]
    simp
  have hnm : n = m * 2 := by
    have h1 := Module.finrank_eq_card_basis c'
    rw [Module.finrank_fin_fun] at h1
    simpa using h1
  refine ⟨m, c', hnm, ?_⟩
  rw [coe_specialLinearBasisEquiv]
  ext ⟨k, p⟩ ⟨l, q⟩
  rw [gaussIota_omega_apply, LinearMap.toMatrix_apply]
  have hfg : Matrix.toLin' (g : Matrix (Fin n) (Fin n) F) = f := rfl
  rw [hfg]
  by_cases hkl : k = l
  · subst hkl
    fin_cases p <;> fin_cases q <;> simp [hf0, hf1]
  · fin_cases p <;> fin_cases q <;> simp [hf0, hf1, hkl]

theorem componentAt_psl4_of_sq_eq_neg_one (g : SL(4, ZMod 3))
    (hg2 : (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * g = -1) :
    ComponentAt (QuotientGroup.mk g : SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3)) := by
  have hF : Nat.card (ZMod 3) = 3 := Nat.card_zmod 3
  have := Fact.mk (not_isSquare_neg_one_of_card_eq_three hF)
  obtain ⟨m, c, hnm, hψg⟩ := exists_gaussBasis hF (n := 4) (by norm_num) g hg2
  obtain rfl : m = 2 := by omega
  have hZ : IsPGroup 2 (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2 × Fin 2) (ZMod 3))) :=
    (CenterExp.of_mulEquiv (specialLinearBasisEquiv c).symm
      (centerExp_specialLinear_of_pos (k := 1) (by rw [hF]; norm_num)
        (by norm_num : 1 ≤ 4))).isPGroup
  have key := componentAt_gaussOmega hF hZ _ hψg
  let e := QuotientGroup.congr (Subgroup.center SL(4, ZMod 3))
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2 × Fin 2) (ZMod 3)))
    (specialLinearBasisEquiv c) (Subgroup.map_center_eq _)
  have h1 : e (QuotientGroup.mk g) = QuotientGroup.mk (specialLinearBasisEquiv c g) := rfl
  have := ComponentAt.map e.symm key
  rwa [← h1, MulEquiv.symm_apply_apply] at this

end CFSG.CGT.PushingUpLit.SolKNA
