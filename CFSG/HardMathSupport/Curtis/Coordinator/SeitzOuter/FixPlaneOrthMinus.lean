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
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.LieType.SeitzGeneration
  CFSG.AGLEmbeddingD2
open CFSG.Open (IsElemAbelian)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadMinus StatedLieAdmissible
  StatedLieTag StatedClassicalModel)

theorem fixPlaneGen_minus_rational
    {n ℓ e p : ℕ} {K : Type} [Field K] [Finite K] (hn : 4 ≤ n) (hn1 : 1 ≤ n)
    (hℓ : ℓ.Prime) (he : 1 ≤ e) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) {k : Subfield K}
    (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) {σ₀ : K ≃+* K}
    (hσ₀ : orderOf σ₀ = p) (hfix : ∀ x, x ∈ k ↔ σ₀ x = x) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) (hNJ : OrthFixedLeDerived .POmegaMinus n ℓ e p)
    (hrk : RankLE2 p (matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K)))) :
    FixPlaneGen (matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K))) p := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
  have hfixall := fun σ (h : orderOf σ = p) => fixed_of_orderOf_orth hℓ he hp hK hσ₀ hfix h
  have hirrK : ∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0 :=
    rootFree_of_odd_degree k hp hp2 (finrank_subfield_eq k hℓ he hk hK) b c hirr
  have hM : StatedClassicalModel
      (StatedProj (StatedOmega (StatedQuadMinus n K (b : K) (c : K)))) .POmegaMinus n ℓ (e * p) :=
    ⟨⟨hℓ, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirrK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadMinus n K hn1 (b : K) (c : K)) (e * p) :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ (e * p) hM hn1 K hK b c hirrK (MulEquiv.refl _)
  refine fixPlaneGen_matrixProjectiveDerived _ hℓ hf hK hp
    (fun σ h v => coordinateQuadMinus_fieldAut k n hn1 (hfixall σ h) b c v) ?_ ?_
  · intro α hα
    obtain ⟨hE, hD⟩ := outer_mem_E_not_D hg hp hp3 hα
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ (e * p) p hM hp hp3 hpℓ hn1 K hK b c hirrK (MulEquiv.refl _) α hE hD
      hα.1
    refine exists_conj_fieldAutT_of_descent _ hE hdesc
      (fun σ h v => coordinateQuadMinus_fieldAut k n hn1 (hfixall σ h) b c v) ?_
    intro U Q₀ hord hdisp
    obtain ⟨b', c', hirr', ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
    have hfixV := hfixall U.val.right hord
    have hσk' : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
      fun x => RingHom.mem_eqLocusField
    have hb'k : (b' : K) ∈ k := (hfixV _).2 ((hσk' _).1 b'.2)
    have hc'k : (c' : K) ∈ k := (hfixV _).2 ((hσk' _).1 c'.2)
    have hirrkK : ∀ s ∈ k, s ^ 2 + (b : K) * s + (c : K) ≠ 0 := fun s hs hz =>
      hirr ⟨s, hs⟩ (Subtype.ext (by simpa using hz))
    have hirr'kK : ∀ s ∈ k, s ^ 2 + (b' : K) * s + (c' : K) ≠ 0 := by
      intro s hs hz
      have hsV : s ∈ KCOrthogonalDescent.fixedField U.val := (hσk' s).2 ((hfixV s).1 hs)
      exact hirr' ⟨s, hsV⟩ (Subtype.ext (by simpa using hz))
    obtain ⟨μ, hμk, hμQ⟩ :=
      SEITZ2.exists_tail_isometry k hn1 b.2 c.2 hb'k hc'k hirrkK hirr'kK
    have hμσ : glFieldAut (Fin (2 * n)) K U.val.right μ = μ :=
      Units.ext (Matrix.ext fun i j => (hfixV _).1 (hμk i j))
    refine ⟨μ * S, ν', fun v => ?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (hμQ _).trans (hSQ v)
    · rw [mul_assoc, hSA, map_mul, hμσ]
  · intro σ hσ A hA hAa hAc
    obtain ⟨-, hconc⟩ :=
      orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional .POmegaMinus
        (Or.inr (Or.inr rfl)) n ℓ e p ⟨hℓ, he, hn⟩ hp hp3 hpℓ hn1 K k hk hK σ hσ (hfixall σ hσ)
        b c hirr
    have hNJ' := hNJ ⟨hℓ, he, hn⟩ hp hp3 hpℓ hn1 K k hk hK σ hσ (hfixall σ hσ) b c hirr
    obtain ⟨⟨hinj, -, -⟩, -, hfixiff, hJN, -⟩ := hconc
    have hrange : fixedSubgroup (fieldAutT (coordinateQuadMinus n K hn1 (b : K) (c : K)) σ
        (coordinateQuadMinus_fieldAut k n hn1 (hfixall σ hσ) b c)) =
        (incl k (coordinateQuadMinus_isExtension k n hn1 b c)).range :=
      (Subgroup.ext hfixiff).trans (le_antisymm hNJ' hJN)
    have hadm0 : StatedLieAdmissible .POmegaMinus n ℓ e := ⟨hℓ, he, hn⟩
    let q0 : TauCeti.PrimePower := ⟨ℓ, e, hℓ, he⟩
    have hv : (TauCeti.LieTypeIndex.twistedD n q0).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨hn, fun h => h⟩
    let d0 : TauCeti.ValidLieTypeIndex := ⟨.twistedD n q0, hv⟩
    have hF0 : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField d0) = ℓ ^ e := by
      rw [card_fixedField_eq]
      simp [d0, q0, TauCeti.ValidLieTypeIndex.characteristic,
        TauCeti.ValidLieTypeIndex.fieldExponent]
    have hF0fin : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField d0) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    obtain ⟨b0, c0, hirr0, ⟨eD⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        n q0 hv
    have hMcat : StatedClassicalModel (Cat d0) .POmegaMinus n ℓ e :=
      ⟨hadm0, _, inferInstance, inferInstance, hF0, b0, c0, hirr0, ⟨eD⟩⟩
    have hkfin : Finite k := inferInstance
    have hM0 : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c))
        .POmegaMinus n ℓ e :=
      ⟨hadm0, k, inferInstance, inferInstance, hk, b, c, hirr,
        ⟨(coordinateMinusWitnessEquiv k hn1 b c (MulEquiv.refl _)).symm⟩⟩
    obtain ⟨ε⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hMcat hM0
    obtain ⟨-, hnt, hsimp0, hperf0⟩ := orth_facts_of_model (Or.inr (Or.inr rfl)) hM0
    have := hsimp0
    have hnab0 : ∃ a b' : matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c),
        a * b' ≠ b' * a := by
      by_contra hcon
      push Not at hcon
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b' => hcon a b'⟩⟩
    have hrk0 : RankLE2 p (matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c)) :=
      rankLE2_of_injective _ hinj hrk
    have hpd : p ≠ d0.1.characteristic := by
      have : d0.1.characteristic = ℓ := by simp [d0, q0]
      rw [this]; exact hpℓ
    have hexc : ¬ IsD2SeitzException p d0.1 := by
      simp [IsD2SeitzException, d0]
    have hM := closure_comm_planes_of_index hnab0 ε hp hp2 hpd hexc
      (by simp [IsClassicalIndex, d0]) hrk0
    rw [hrange] at hA ⊢
    exact planeGenIn_range _ hinj hM A hA hAa hAc

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
