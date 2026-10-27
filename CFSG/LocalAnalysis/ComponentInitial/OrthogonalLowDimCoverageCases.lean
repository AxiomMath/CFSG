module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageThree
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageNonsplit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveSimilarity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixSimilarity

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

theorem sq_mem_commutator_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ∀ x : H, x ^ 2 ∈ commutator H) (g : G) : g ^ 2 ∈ commutator G := by
  rw [commutator_eq_map_symm e]
  exact ⟨(e g) ^ 2, h _, by simp⟩

theorem normal_subgroupOf_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {L J : Subgroup G} (hLJ : L ≤ J) (h : (L.subgroupOf J).Normal) :
    ((L.map e.toMonoidHom).subgroupOf (J.map e.toMonoidHom)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hLJ] at h
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hLJ)]
  rintro _ _ ⟨l, hl, rfl⟩ ⟨j, hj, rfl⟩
  exact ⟨j * l * j⁻¹, h l j hl hj, by simp⟩

variable {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem orthogonal_three_derived (hodd : Odd (Nat.card K)) (hK3 : Nat.card K ≠ 3)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K W = 3) :
    ∃ (d : Kˣ) (ψ : W ≃ₗ[K] traceZeroSubmodule K)
      (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
        TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)),
      (∀ v, Q v = (d : K) * traceZeroForm K (ψ v)) ∧
      (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : traceZeroSubmodule K),
        (e g).val X = ψ (g.val (ψ.symm X))) ∧
      commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
        (traceZeroSpecialImage K).map e.symm.toMonoidHom ∧
      CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q,
        g ^ 2 ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  obtain ⟨d, ψ, e, hψ, he, -⟩ :=
    CatalogueBOrthogonalThreeSimilarity.exists_trace_zero_similarity_and_orthogonal_equiv
      hodd Q hQ hdim
  have hc := traceZero_commutator_eq hodd hK3
  have hcomm : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
      (traceZeroSpecialImage K).map e.symm.toMonoidHom := by
    rw [commutator_eq_map_symm e, hc]
  refine ⟨d, ψ, e, hψ, fun g X => by rw [he g]; rfl, hcomm, ?_, ?_⟩
  · rw [hcomm]
    exact isQuasisimple_map_mulEquiv e.symm (traceZeroSpecialImage_quasisimple hK2 hK3)
  · exact sq_mem_commutator_of_mulEquiv e fun x => hc ▸ traceZero_sq_mem_specialImage h2 x

theorem orthogonal_split_four_derived (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ (ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
      (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃* DeterminantIsometries K),
      (∀ v, Q v = (ψ v).det) ∧
      (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : Matrix (Fin 2) (Fin 2) K),
        (e g).val X = ψ (g.val (ψ.symm X))) ∧
      commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
        (determinantLeftFactor K).map e.symm.toMonoidHom ⊔
          (determinantRightFactor K).map e.symm.toMonoidHom ∧
      CFSG.IsQuasisimple ((determinantLeftFactor K).map e.symm.toMonoidHom) ∧
      CFSG.IsQuasisimple ((determinantRightFactor K).map e.symm.toMonoidHom) ∧
      (((determinantLeftFactor K).map e.symm.toMonoidHom).subgroupOf
        (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))).Normal ∧
      (((determinantRightFactor K).map e.symm.toMonoidHom).subgroupOf
        (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))).Normal ∧
      (∀ x ∈ (determinantLeftFactor K).map e.symm.toMonoidHom,
        ∀ y ∈ (determinantRightFactor K).map e.symm.toMonoidHom, x * y = y * x) ∧
      Group.IsPerfect (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q,
        g ^ 2 ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  obtain ⟨S, hSdim, hSQ⟩ := hS
  obtain ⟨ψ, e, hψ, he, -⟩ := split_four_determinant_form_isometry Q hQ hdim S hSdim hSQ
  have hc := determinant_commutator_eq (K := K) hK2 hK3
  have hcomm : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
      (specialImage K).map e.symm.toMonoidHom := by
    rw [commutator_eq_map_symm e, hc]
  have hsup : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
      (determinantLeftFactor K).map e.symm.toMonoidHom ⊔
        (determinantRightFactor K).map e.symm.toMonoidHom := by
    rw [hcomm, ← Subgroup.map_sup, determinantFactors_sup]
  refine ⟨ψ, e, hψ, he, hsup, isQuasisimple_map_mulEquiv e.symm
    (determinantLeftFactor_quasisimple hK2 hK3), isQuasisimple_map_mulEquiv e.symm
    (determinantRightFactor_quasisimple hK2 hK3), ?_, ?_, ?_, ?_,
    sq_mem_commutator_of_mulEquiv e fun x => hc ▸ determinant_sq_mem_specialImage x⟩
  · rw [hcomm]
    exact normal_subgroupOf_map_mulEquiv e.symm determinantLeftFactor_le
      determinantLeftFactor_normal
  · rw [hcomm]
    exact normal_subgroupOf_map_mulEquiv e.symm determinantRightFactor_le
      determinantRightFactor_normal
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, determinantFactors_commute hx hy]
  · rw [hcomm]
    let := determinantSpecialImage_isPerfect hK2 hK3
    exact Group.IsPerfect.ofSurjective (f := ((specialImage K).equivMapOfInjective
      e.symm.toMonoidHom e.symm.injective).toMonoidHom) (MulEquiv.surjective _)

theorem orthogonal_nonsplit_four_derived (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K W = 4)
    (hno : ¬ ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ (δ : Kˣ), ¬ IsSquare (δ : K) ∧ ∃ (d : Kˣ)
      (ψ : W ≃ₗ[K] CatalogueBOrthogonalFourNonsplit.hermitianSubmodule (δ : K))
      (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
        CatalogueBOrthogonalFourNonsplit.HermitianIsometries (δ : K)),
      (∀ v, Q v = (d : K) * CatalogueBOrthogonalFourNonsplit.hermitianForm (δ : K) (ψ v)) ∧
      (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q)
        (X : CatalogueBOrthogonalFourNonsplit.hermitianSubmodule (δ : K)),
        (e g).val X = ψ (g.val (ψ.symm X))) ∧
      commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
        (CatalogueBOrthogonalFourNonsplit.specialImage (δ : K)
          (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).map e.symm.toMonoidHom ∧
      CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q,
        g ^ 2 ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hns, d, ψ, e, hψ, he, -⟩ :=
    CatalogueBOrthogonalFourNonsplit.exists_hermitian_similarity_and_orthogonal_equiv hodd Q hQ
      hdim hno
  have : Fact (¬ IsSquare (δ : K)) := ⟨hns⟩
  have hc := hermitian_commutator_eq (δ : K) h2
  have hcomm : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
      (CatalogueBOrthogonalFourNonsplit.specialImage (δ : K) h2).map e.symm.toMonoidHom := by
    rw [commutator_eq_map_symm e, hc]
  refine ⟨δ, hns, d, ψ, e, hψ, he, hcomm, ?_, ?_⟩
  · rw [hcomm]
    exact isQuasisimple_map_mulEquiv e.symm (hermitianSpecialImage_quasisimple (δ : K) h2)
  · exact sq_mem_commutator_of_mulEquiv e fun x => hc ▸ hermitian_sq_mem_specialImage _ h2 x

theorem orthogonal_five_derived (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K W = 5) :
    ∃ (d : Kˣ) (ψ : W ≃ₗ[K] CatalogueBOrthogonalFive.selfAdjointSubmodule K)
      (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
        TauCeti.QuadraticMap.orthogonalGroup (CatalogueBOrthogonalFive.selfAdjointForm K)),
      (∀ v, Q v = (d : K) * CatalogueBOrthogonalFive.selfAdjointForm K (ψ v)) ∧
      (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q)
        (X : CatalogueBOrthogonalFive.selfAdjointSubmodule K),
        (e g).val X = ψ (g.val (ψ.symm X))) ∧
      commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
        (CatalogueBOrthogonalFive.selfAdjointSymplecticImage
          (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).map e.symm.toMonoidHom ∧
      CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q,
        g ^ 2 ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  obtain ⟨d, ψ, e, hψ, he, -⟩ :=
    CatalogueBOrthogonalFive.finite_odd_five_selfAdjoint_form_similarity hodd Q hQ hdim
  have hc := selfAdjoint_commutator_eq (K := K) hodd
  have hcomm : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
      (CatalogueBOrthogonalFive.selfAdjointSymplecticImage
        (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).map e.symm.toMonoidHom := by
    rw [commutator_eq_map_symm e, hc]
  refine ⟨d, ψ, e, hψ, he, hcomm, ?_, ?_⟩
  · rw [hcomm]
    exact isQuasisimple_map_mulEquiv e.symm (selfAdjointSymplecticImage_quasisimple hodd)
  · exact sq_mem_commutator_of_mulEquiv e fun x => hc ▸ selfAdjoint_sq_mem_symplecticImage _ x

theorem orthogonal_nonsplit_six_derived (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K W = 6)
    (hno : ¬ ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ∃ (δ : Kˣ) (_ : Fact (¬ IsSquare (δ : K))) (d : Kˣ)
      (ψ : W ≃ₗ[K] CatalogueBOrthogonalSix.sixSubmodule (δ : K))
      (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
        CatalogueBOrthogonalSix.SixIsometries (δ : K)),
      (∀ v, Q v = (d : K) * CatalogueBOrthogonalSix.sixForm (δ : K) (ψ v)) ∧
      (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q)
        (X : CatalogueBOrthogonalSix.sixSubmodule (δ : K)),
        (e g).val X = ψ (g.val (ψ.symm X))) ∧
      commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
        (CatalogueBOrthogonalSix.sixSpecialImage (δ : K)
          (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).map e.symm.toMonoidHom ∧
      CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q,
        g ^ 2 ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hns, d, ψ, e, hψ, -, -, -, -, he, -⟩ :=
    CatalogueBOrthogonalSixSimilarity.nonsplit_six_unitary_skew_form_similarity hodd Q hQ
      hdim hno
  have hfact : Fact (¬ IsSquare (δ : K)) := ⟨hns⟩
  have hc := six_commutator_eq (δ : K) h2
  have hcomm : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
      (CatalogueBOrthogonalSix.sixSpecialImage (δ : K) h2).map e.symm.toMonoidHom := by
    rw [commutator_eq_map_symm e, hc]
  refine ⟨δ, hfact, d, ψ, e, hψ, he, hcomm, ?_, ?_⟩
  · rw [hcomm]
    exact isQuasisimple_map_mulEquiv e.symm (sixSpecialImage_quasisimple (δ : K) h2)
  · exact sq_mem_commutator_of_mulEquiv e fun x => hc ▸ six_sq_mem_specialImage _ h2 x

end CFSG.LocalAnalysis.ComponentInitial
