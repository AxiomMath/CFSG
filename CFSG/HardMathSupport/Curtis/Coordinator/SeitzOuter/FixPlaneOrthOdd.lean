module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.FixPlaneOrthGeneric
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.OrthFixedLeDerived
public import CFSG.LieType.SeitzGeneration.OuterOrthCat
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.FixPlaneInner

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.LieType.SeitzGeneration
  CFSG.AGLEmbeddingD2
open CFSG.Open (IsElemAbelian)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadOdd StatedQuadPlus StatedLieAdmissible
  StatedClassicalModel)

theorem fixPlaneGen_orthOdd
    {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    (hadm : StatedLieAdmissible .POmegaOdd n ℓ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hNJ : ∀ e, OrthFixedLeDerived .POmegaOdd n ℓ e p)
    (hrk : RankLE2 p (matrixProjectiveDerived (coordinateQuadOdd n K))) :
    FixPlaneGen (matrixProjectiveDerived (coordinateQuadOdd n K)) p := by
  classical
  obtain ⟨hℓ, hf, hn3, hℓ2⟩ := id hadm
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n K))) .POmegaOdd n ℓ f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadOdd n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaOdd (Or.inl rfl) n ℓ f hM
      K hK (MulEquiv.refl _)
  refine fixPlaneGen_matrixProjectiveDerived _ hℓ hf hK hp
    (fun σ _ => coordinateQuadOdd_fieldAut n σ) ?_ ?_
  · intro α hα
    obtain ⟨hE, hD⟩ := outer_mem_E_not_D hg hp hp3 hα
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent _ .POmegaOdd (Or.inl rfl)
      n ℓ f p hM hp hp3 hpℓ K hK (MulEquiv.refl _) α hE hD hα.1
    exact exists_conj_fieldAutT_of_descent _ hE hdesc (fun σ _ => coordinateQuadOdd_fieldAut n σ)
      (fun U Q₀ _ hdisp => by
        obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
        exact ⟨S, ν', hSQ, hSA⟩)
  · intro σ hσ A hA hAa hAc
    obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
    obtain ⟨e, rfl⟩ := hpf
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · rw [h0, mul_zero] at hf
        omega
      · exact h0
    rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
    have hK' : Nat.card K = ℓ ^ (e * p) := by rw [hK, mul_comm]
    have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
    have hadm0 : StatedLieAdmissible .POmegaOdd n ℓ e := ⟨hℓ, he, hn3, hℓ2⟩
    obtain ⟨-, hconc⟩ :=
      orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional .POmegaOdd
        (Or.inl rfl) n ℓ e p hadm0 hp hp3 hpℓ K (semilinearFixedSubfield σ) hcardk hK' σ hσ hσk
    have hNJ' := hNJ e hadm0 hp hp3 hpℓ K (semilinearFixedSubfield σ) hcardk hK' σ hσ hσk
    obtain ⟨⟨hinj, -, -⟩, -, hfixiff, hJN, -⟩ := hconc
    have hrange : fixedSubgroup (fieldAutT (coordinateQuadOdd n K) σ
        (coordinateQuadOdd_fieldAut n σ)) =
        (incl (semilinearFixedSubfield σ) (coordinateQuadOdd_isExtension _ n)).range :=
      (Subgroup.ext hfixiff).trans (le_antisymm hNJ' hJN)
    set k := semilinearFixedSubfield σ with hk
    let q0 : TauCeti.PrimePower := ⟨ℓ, e, hℓ, he⟩
    have hv : (TauCeti.LieTypeIndex.B n q0).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
    let d0 : TauCeti.ValidLieTypeIndex := ⟨.B n q0, hv⟩
    have hF0 : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField d0) = ℓ ^ e :=
      CFSG.RankThree.PartOne.CTP.card_fixedField_B n q0 hv
    have hF0fin : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField d0) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hM1 : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n
        ↥(TauCeti.ValidLieTypeIndex.fixedField d0)))) .POmegaOdd n ℓ e :=
      ⟨hadm0, _, inferInstance, inferInstance, hF0, ⟨MulEquiv.refl _⟩⟩
    have hkfin : Finite k := inferInstance
    have hM0 : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadOdd n k))
        .POmegaOdd n ℓ e :=
      ⟨hadm0, k, inferInstance, inferInstance, hcardk,
        ⟨(coordinateOddWitnessEquiv (n := n) k (MulEquiv.refl _)).symm⟩⟩
    obtain ⟨ε₁⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hM1 hM0
    let ε : Cat d0 ≃* matrixProjectiveDerived (coordinateQuadOdd n k) :=
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n q0 hv hℓ2
        hn3).trans ε₁
    obtain ⟨-, hnt, hsimp0, hperf0⟩ := orth_facts_of_model (Or.inl rfl) hM0
    have := hsimp0
    have hnab0 : ∃ a b : matrixProjectiveDerived (coordinateQuadOdd n k), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hcon a b⟩⟩
    have hrk0 : RankLE2 p (matrixProjectiveDerived (coordinateQuadOdd n k)) :=
      rankLE2_of_injective _ hinj hrk
    have hpd : p ≠ d0.1.characteristic := by
      have : d0.1.characteristic = ℓ := by simp [d0, q0]
      rw [this]; exact hpℓ
    have hexc : ¬ IsD2SeitzException p d0.1 := by
      simp [IsD2SeitzException, d0]
      omega
    have hM := closure_comm_planes_of_index hnab0 ε hp (by omega) hpd hexc
      (by simp [IsClassicalIndex, d0]) hrk0
    rw [hrange] at hA ⊢
    exact planeGenIn_range _ hinj hM A hA hAa hAc

theorem fixPlaneGen_orthPlus
    {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    (hadm : StatedLieAdmissible .POmegaPlus n ℓ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hNJ : ∀ e, OrthFixedLeDerived .POmegaPlus n ℓ e p)
    (hrk : RankLE2 p (matrixProjectiveDerived (coordinateQuadPlus n K))) :
    FixPlaneGen (matrixProjectiveDerived (coordinateQuadPlus n K)) p := by
  classical
  obtain ⟨hℓ, hf, hn4⟩ := id hadm
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus n ℓ f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadPlus n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus (Or.inr (Or.inl rfl)) n ℓ f hM
      K hK (MulEquiv.refl _)
  refine fixPlaneGen_matrixProjectiveDerived _ hℓ hf hK hp
    (fun σ _ => coordinateQuadPlus_fieldAut n σ) ?_ ?_
  · intro α hα
    obtain ⟨hE, hD⟩ := outer_mem_E_not_D hg hp hp3 hα
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent _ .POmegaPlus (Or.inr (Or.inl rfl))
      n ℓ f p hM hp hp3 hpℓ K hK (MulEquiv.refl _) α hE hD hα.1
    exact exists_conj_fieldAutT_of_descent _ hE hdesc (fun σ _ => coordinateQuadPlus_fieldAut n σ)
      (fun U Q₀ _ hdisp => by
        obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
        exact ⟨S, ν', hSQ, hSA⟩)
  · intro σ hσ A hA hAa hAc
    obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
    obtain ⟨e, rfl⟩ := hpf
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · rw [h0, mul_zero] at hf
        omega
      · exact h0
    rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
    have hK' : Nat.card K = ℓ ^ (e * p) := by rw [hK, mul_comm]
    have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
    have hadm0 : StatedLieAdmissible .POmegaPlus n ℓ e := ⟨hℓ, he, hn4⟩
    obtain ⟨-, hconc⟩ :=
      orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional .POmegaPlus
        (Or.inr (Or.inl rfl)) n ℓ e p hadm0 hp hp3 hpℓ K (semilinearFixedSubfield σ) hcardk hK' σ hσ hσk
    have hNJ' := hNJ e hadm0 hp hp3 hpℓ K (semilinearFixedSubfield σ) hcardk hK' σ hσ hσk
    obtain ⟨⟨hinj, -, -⟩, -, hfixiff, hJN, -⟩ := hconc
    have hrange : fixedSubgroup (fieldAutT (coordinateQuadPlus n K) σ
        (coordinateQuadPlus_fieldAut n σ)) =
        (incl (semilinearFixedSubfield σ) (coordinateQuadPlus_isExtension _ n)).range :=
      (Subgroup.ext hfixiff).trans (le_antisymm hNJ' hJN)
    set k := semilinearFixedSubfield σ with hk
    let q0 : TauCeti.PrimePower := ⟨ℓ, e, hℓ, he⟩
    have hv : (TauCeti.LieTypeIndex.D n q0).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨hn4, fun h => h⟩
    let d0 : TauCeti.ValidLieTypeIndex := ⟨.D n q0, hv⟩
    have hF0 : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField d0) = ℓ ^ e :=
      by
      rw [card_fixedField_eq]
      simp [d0, q0, TauCeti.ValidLieTypeIndex.characteristic,
        TauCeti.ValidLieTypeIndex.fieldExponent]
    have hF0fin : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField d0) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hM1 : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n
        ↥(TauCeti.ValidLieTypeIndex.fixedField d0)))) .POmegaPlus n ℓ e :=
      ⟨hadm0, _, inferInstance, inferInstance, hF0, ⟨MulEquiv.refl _⟩⟩
    have hkfin : Finite k := inferInstance
    have hM0 : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n k))
        .POmegaPlus n ℓ e :=
      ⟨hadm0, k, inferInstance, inferInstance, hcardk,
        ⟨(coordinatePlusWitnessEquiv (n := n) k (MulEquiv.refl _)).symm⟩⟩
    obtain ⟨ε₁⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hM1 hM0
    let ε : Cat d0 ≃* matrixProjectiveDerived (coordinateQuadPlus n k) :=
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n q0 hv).trans ε₁
    obtain ⟨-, hnt, hsimp0, hperf0⟩ := orth_facts_of_model (Or.inr (Or.inl rfl)) hM0
    have := hsimp0
    have hnab0 : ∃ a b : matrixProjectiveDerived (coordinateQuadPlus n k), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hcon a b⟩⟩
    have hrk0 : RankLE2 p (matrixProjectiveDerived (coordinateQuadPlus n k)) :=
      rankLE2_of_injective _ hinj hrk
    have hpd : p ≠ d0.1.characteristic := by
      have : d0.1.characteristic = ℓ := by simp [d0, q0]
      rw [this]; exact hpℓ
    have hexc : ¬ IsD2SeitzException p d0.1 := by
      simp [IsD2SeitzException, d0]
    have hM := closure_comm_planes_of_index hnab0 ε hp (by omega) hpd hexc
      (by simp [IsClassicalIndex, d0]) hrk0
    rw [hrange] at hA ⊢
    exact planeGenIn_range _ hinj hM A hA hAa hAc

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
