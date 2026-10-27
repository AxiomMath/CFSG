module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalPSL
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityStd
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusGram

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL conjAut dualAut fieldAut)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (even_linear_pure_graph_involution_normal_forms)

section Component

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem graphNormal_isComponent_top {f : ℕ} (h : LieModel X .PSp 3 2 f) :
    IsComponent (⊤ : Subgroup X) ∧ LieModel (⊤ : Subgroup X) .PSp 3 2 f := by
  have hs : IsSimpleGroup X := isSimpleGroup_of_lieModel_PSp h
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
    have hp : (Nat.card X).Prime := IsSimpleGroup.prime_card
    have h9 := two_pow_nine_dvd_card_of_lieModel_PSp_three_two h
    rcases (Nat.dvd_prime hp).1 h9 with h1 | h1
    · norm_num at h1
    · rw [← h1] at hp
      norm_num at hp
  have hq : IsQuasisimple X := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  exact ⟨⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq,
      Subgroup.IsSubnormal.top⟩,
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv Subgroup.topEquiv.symm h⟩


theorem graphNormal_false_of_notSp6Components {f : ℕ} (h : LieModel X .PSp 3 2 f)
    (hN : NotSp6Components X) : False := by
  obtain ⟨hc, hm⟩ := graphNormal_isComponent_top h
  exact false_of_notSp6Components lieModel_PSp_three_two_unique_classicalOrSuzuki hN hc hm

end Component

section NormalForm


variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem graphNormal_nonempty_fixed_conj_equiv {P : Type} [Group P] (φ α : MulAut P) :
    Nonempty (fixedSubgroup (φ * α * φ⁻¹) ≃* fixedSubgroup α) :=
  ⟨((fixedSubgroupCongrEquiv φ α).trans (MulEquiv.subgroupCongr (congrArg fixedSubgroup
    (MulEquiv.ext fun _ => rfl : MulAut.congr φ α = φ * α * φ⁻¹)))).symm⟩

theorem graphNormal_exists (hn : 3 ≤ n) {f f' : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (α : MulAut (projectiveSL n F)) (hα2 : α * α = 1)
    (hαo : α ∉ (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range)
    (hfix : LieModel (fixedSubgroup α) .PSp 3 2 f') :
    ∃ H C : GL (Fin n) F,
      α = conjAut n F H * (conjAut n F C * dualAut n F) * (conjAut n F H)⁻¹ ∧
      (((C : Matrix (Fin n) (Fin n) F) = 1 ∧ ¬ Even n) ∨
        ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) F) =
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ n r) := by
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hF
  have hfalse : NotSp6Components (fixedSubgroup α) → False :=
    graphNormal_false_of_notSp6Components hfix
  have hα2' : α ^ 2 = 1 := by rw [sq]; exact hα2
  have hα1 : α ≠ 1 := fun h => hαo ⟨1, by rw [h, map_one]⟩
  have hord : orderOf α = 2 := orderOf_eq_prime hα2' hα1
  have htr : ∀ β : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) F),
      MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n F) α = β →
      NotSp6Components (fixedSubgroup β) → False := by
    intro β hβ hN
    exact hfalse (notSp6Components_of_mulEquiv ((fixedSubgroupCongrEquiv
      (CatalogueBLinearHigherB.nativeEquiv n F) α).trans
        (MulEquiv.subgroupCongr (congrArg fixedSubgroup hβ))) hN)
  obtain ⟨A, σ, ε, hε, hα⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation (K := F) hn).2 α
  interval_cases ε
  · rw [pow_zero, mul_one] at hα
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hα
      obtain ⟨y, -, hy⟩ := LinearPilot.exists_conjAut_eq_mulAut_conj hn A (hα ▸ hα2')
      exact absurd ⟨y, by rw [hα, hy]⟩ hαo
    · exfalso
      have hc : MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n F) α =
          CatalogueBLinearSemilinear.semilinearAction n F A σ := by
        rw [hα]
        exact CatalogueBLinearHigherB.congr_semilinear A σ
      have hsq : CatalogueBLinearSemilinear.semilinearAction n F A σ ^ 2 = 1 := by
        rw [← hc, ← map_pow, hα2', map_one]
      exact htr _ hc (notSp6Components_psl_field (by omega) hf hF A σ hσ hsq)
  · rw [pow_one] at hα
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hα
      obtain ⟨-, ⟨H, C, -, hconj, hC⟩, -⟩ :=
        even_linear_pure_graph_involution_normal_forms hf hF hn A (hα ▸ hα2')
      refine ⟨H, C, hα.trans hconj, ?_⟩
      rcases hC with ⟨h1, -⟩ | ⟨r, hr, hJ, -⟩
      · refine Or.inl ⟨h1, fun hev => hfalse ?_⟩
        have hC1 : C = 1 := Units.ext h1
        have hδ : conjAut n F C * dualAut n F = dualAut n F := by rw [hC1, map_one, one_mul]
        obtain ⟨ε'⟩ := graphNormal_nonempty_fixed_conj_equiv (conjAut n F H)
          (conjAut n F C * dualAut n F)
        have hn4 : 4 ≤ n := by
          obtain ⟨k, hk⟩ := hev
          omega
        have hch := CFSG.ComponentClassification.CatLeafProof.isCharacteristicP_fixed_dualAut hf hF
          hn4 hev
        rw [← hδ] at hch
        rw [hα.trans hconj]
        exact notSp6Components_of_mulEquiv ε' (notSp6Components_of_isCharacteristicP hch)
      · exact Or.inr ⟨r, hr, hJ⟩
    · exfalso
      have hc : MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n F) α =
          CatalogueBGraphField.graphFieldAction n F A σ := by
        rw [hα]
        exact CatalogueBLinearHigherB.congr_graphField A σ
      have hord' : orderOf (CatalogueBGraphField.graphFieldAction n F A σ) = 2 := by
        rw [← hc]
        exact (orderOf_injective
          (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n F)).toMonoidHom
          (MulAut.congr _).injective α).trans hord
      exact htr _ hc (notSp6Components_psl_graphField hn hf hF A σ hσ hord')

end NormalForm

section Main


variable {F : Type} [Field F] [Finite F]

theorem exists_eq_conj_graphGram6 {f f' : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (α : MulAut (projectiveSL 6 F)) (hα2 : α * α = 1)
    (hαo : α ∉ (MulAut.conj : projectiveSL 6 F →* MulAut (projectiveSL 6 F)).range)
    (hfix : LieModel (fixedSubgroup α) .PSp 3 2 f') :
    ∃ H : GL (Fin 6) F,
      α = conjAut 6 F H * (conjAut 6 F (graphGram6 F) * dualAut 6 F) * (conjAut 6 F H)⁻¹ := by
  obtain ⟨H, C, hHC, hC⟩ := graphNormal_exists (by norm_num) hf hF α hα2 hαo hfix
  rcases hC with ⟨-, hodd⟩ | ⟨r, hr, hJ⟩
  · exact absurd (by decide : Even 6) hodd
  · obtain rfl : r = 3 := by omega
    have hCJ : C = graphGram6 F := Units.ext hJ
    exact ⟨H, hCJ ▸ hHC⟩

omit [Finite F] in
theorem graphNormal_sq_graphGram7 :
    (conjAut 7 F (graphGram7 F) * dualAut 7 F) ^ 2 = 1 := by
  obtain ⟨-, -, -, hdd, hdc, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.standard_automorphism_transport (n := 7) (K := F)
  have hT : Matrix.GeneralLinearGroup.inverseTranspose (graphGram7 F) = graphGram7 F := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, graphGram7_inv, coe_graphGram7,
      transpose_gram7]
  have hsq : graphGram7 F * graphGram7 F = 1 := Units.ext (gram7_mul_self F)
  rw [sq]
  calc conjAut 7 F (graphGram7 F) * dualAut 7 F * (conjAut 7 F (graphGram7 F) * dualAut 7 F) =
      conjAut 7 F (graphGram7 F) * (dualAut 7 F * conjAut 7 F (graphGram7 F) * dualAut 7 F) := by
        simp only [mul_assoc]
    _ = 1 := by rw [hdc, hT, ← map_mul, hsq, map_one]

theorem exists_eq_conj_graphGram7 {f f' : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (α : MulAut (projectiveSL 7 F)) (hα2 : α * α = 1)
    (hαo : α ∉ (MulAut.conj : projectiveSL 7 F →* MulAut (projectiveSL 7 F)).range)
    (hfix : LieModel (fixedSubgroup α) .PSp 3 2 f') :
    ∃ H : GL (Fin 7) F,
      α = conjAut 7 F H * (conjAut 7 F (graphGram7 F) * dualAut 7 F) * (conjAut 7 F H)⁻¹ := by
  obtain ⟨H, C, hHC, hC⟩ := graphNormal_exists (by norm_num) hf hF α hα2 hαo hfix
  have hC1 : C = 1 := by
    rcases hC with ⟨h1, -⟩ | ⟨r, hr, -⟩
    · exact Units.ext h1
    · omega
  rw [hC1, map_one, one_mul] at hHC
  obtain ⟨-, ⟨H', C', -, hconj', hC'⟩, -⟩ :=
    even_linear_pure_graph_involution_normal_forms hf hF (by norm_num) (graphGram7 F)
      graphNormal_sq_graphGram7
  have hC'1 : C' = 1 := by
    rcases hC' with ⟨h1, -⟩ | ⟨r, hr, -, -⟩
    · exact Units.ext h1
    · omega
  rw [hC'1, map_one, one_mul] at hconj'
  refine ⟨H * H'⁻¹, ?_⟩
  rw [hHC, hconj', map_mul, map_inv]
  group

end Main

end CFSG.SeitzReduction.F4Pilot
