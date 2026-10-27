module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSLGraph
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenUnitaryComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldTransfer

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial FourGroupEvenCanonical UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer

theorem isCharacteristicP_matrixIsometryGroup_one {k : Type} [Field k] [Finite k] [CharP k 2]
    {n : ℕ} (hn : Even n) (hn3 : 3 ≤ n) :
    IsCharacteristicP 2 (matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k)) := by
  obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine RankTwoChar2C0.isCharacteristicP_of_le_normalizer
    (Q := NonalternatingRadical.radicalGroup i) (NonalternatingRadical.radicalGroup_le hn i)
    (fun g => ⟨1, Subtype.ext (by
      rw [SubgroupClass.coe_pow, pow_one, sq, OneMemClass.coe_one]
      exact NonalternatingRadical.mul_self_of_mem_radicalGroup hn g.2)⟩) (fun x hx => ?_)
    (fun x hx hcx => ?_)
  · rw [mem_normalizer_iff]
    intro g
    refine ⟨fun hg => OutcomeLocal.conj_mem_radicalGroup hn hx hg, fun hg => ?_⟩
    have h := OutcomeLocal.conj_mem_radicalGroup hn (inv_mem hx) hg
    rwa [show x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g by group] at h
  · have hx' := NonalternatingRadical.eq_radical_of_centralizes (K := k) hn hn3 i hx 1
      fun g hg => by
        have hcomm : g * x = x * g := mem_centralizer_iff.mp hcx g hg
        rw [map_one, mul_one, ← map_mul, ← map_inv, ← map_mul, ← hcomm, mul_inv_cancel_right]
    exact ⟨1, by rw [pow_one, sq, NonalternatingRadical.mul_self_of_mem_radicalGroup hn hx'.2]⟩

variable {f n : ℕ} {K : Type} [Field K]

theorem even_unitary_fieldBar_fixed_cases (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ f = 2)) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    IsCharacteristicP 2 (fixedSubgroup (primeFormFieldHom h hC σ)) ∨
      ∃ r, 1 ≤ r ∧ (n = 2 * r ∨ n = 2 * r + 1) ∧
        Nonempty (fixedSubgroup (primeFormFieldHom h hC σ) ≃* StatedSp r h.fixedField) := by
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have := fixedField_charP h
  have := fixedField_finite h
  obtain ⟨Cl, hCl⟩ : ∃ Cl : GL (Fin n) h.fixedField,
      (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C := by
    rcases hcase with h1 | ⟨r, hr, hJ⟩
    · exact ⟨1, by rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), h1]⟩
    · refine ⟨blockSwapGL (K := h.fixedField) (r := r) (by omega), ?_⟩
      rw [coe_blockSwapGL, hJ]
      ext i j
      simp only [Matrix.map_apply, blockSwapJ, Matrix.of_apply]
      split_ifs <;> simp
  obtain ⟨hcent, -, hinjU, hNinn, hNC, -, -⟩ :=
    even_unitary_canonical_field_centralizer_transfer h hn hq hC hcase Cl hCl σ hσ
  have hcj := UnbalancingLocal.EvenUnitaryComponents.conj_injective_primeFormP h hC hn
  have heq : inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ⊓
      centralizer {primeFormFieldHom h hC σ} =
        ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
          (fixedIsometryHom h hCl)).range := by
    refine le_antisymm ?_ (le_inf hNinn hNC)
    rintro x ⟨hxI, hxC⟩
    obtain ⟨g, φ, rfl⟩ := (hcent x).mp hxC
    have h1 := primeFormFieldFactor_psi h hC hn hq ⟨fixedIsometryHom h hCl g, φ⟩
    obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ _).mp hxI
    have h2 := primeFormFieldFactor_apply h hC hn hq ⟨s, s.2.1⟩ 1
    rw [map_one, mul_one, ← hs, h1] at h2
    change φ = 1 at h2
    subst h2
    refine ⟨g, ?_⟩
    rw [primeFormPsi_apply, map_one, mul_one]
    rfl
  let Φ : fixedSubgroup (primeFormFieldHom h hC σ) ≃*
      matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) :=
    (fixedInnerEquiv hcj _).trans ((MulEquiv.subgroupCongr heq).trans
      (MonoidHom.ofInjective hinjU).symm)
  rcases canonical_case_of_map h hCl hcase with h1 | ⟨r, hr, hJ⟩
  · rcases Nat.even_or_odd n with hev | ⟨r, hr⟩
    · left
      have hch := isCharacteristicP_matrixIsometryGroup_one (k := h.fixedField) hev hn
      rw [← h1] at hch
      exact LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv Φ.symm hch
    · have hC1 : (Cl : Matrix (Fin n) (Fin n) h.fixedField) =
          ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) := by
        rw [h1, Units.val_one]
      obtain ⟨e₂⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _
        (OutcomeLocal.dotForm_restrict_isAlt (k := h.fixedField) (n := n))
        (OutcomeLocal.dotForm_restrict_nondegenerate hr) (OutcomeLocal.finrank_dotForm_ker hr)
      exact Or.inr ⟨r, by omega, Or.inr hr, ⟨Φ.trans (((MulEquiv.subgroupCongr
        (congrArg matrixIsometryGroup hC1)).trans (OutcomeLocal.oneRestrictEquiv hr)).trans e₂)⟩⟩
  · exact Or.inr ⟨r, by omega, Or.inl hr, ⟨Φ.trans ((MulEquiv.subgroupCongr
      (congrArg matrixIsometryGroup hJ)).trans
        (OutcomeLocal.blockSwapIsometryEquivStatedSp (by omega)))⟩⟩

theorem even_unitary_fieldBar_evenLieConclusion (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ f = 2)) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    (M : Subgroup (fixedSubgroup (primeFormFieldHom h hC σ))) (hM : IsPComponent 2 M) :
    EvenLieConclusion M := by
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have := fixedField_charP h
  have := fixedField_finite h
  rcases even_unitary_fieldBar_fixed_cases h hn hq hC hcase σ hσ with hch | ⟨r, hr, -, ⟨Φ⟩⟩
  · exact absurd hM (not_isPComponent_of_isCharacteristicP hch M)
  · exact evenLieConclusion_of_mulEquiv Φ (fun M' hM' =>
      evenLieConclusion_statedSp h.one_le (UnitaryFieldData.card_fixedField h) hr M' hM') hM

theorem nonempty_mulEquiv_primeFormP_of_lieModel {J : Type} [Group J]
    (hadm : StatedLieAdmissible .PSU n 2 f) (hm : Blueprint.LieModel J .PSU n 2 f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K),
      Nonempty (J ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have hn : 3 ≤ n := hadm.2.2.1
  rcases hm with ⟨-, h⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hadm.2.1, by rw [hK, ← pow_mul, mul_comm]⟩
    obtain ⟨χ⟩ := nonempty_primeFormP_mulEquiv hU (isPrimeFormGram_one (n := n) (K := K))
    exact ⟨K, inferInstance, hU, ⟨e.trans ((unitaryPSUEquiv hU (by omega)).symm.trans χ.symm)⟩⟩
  all_goals omega

theorem even_unitary_outer_fixed_cases {J : Type} [Group J]
    (hadm : StatedLieAdmissible .PSU n 2 f) (hm : Blueprint.LieModel J .PSU n 2 f)
    (α : MulAut J) (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    IsCharacteristicP 2 (fixedSubgroup α) ∨
      ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ f ∧ ∃ r, 1 ≤ r ∧
        (n = 2 * r ∨ n = 2 * r + 1) ∧ Nonempty (fixedSubgroup α ≃* StatedSp r k) := by
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel hadm hm
  have hn : 3 ≤ n := hadm.2.2.1
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => hadm.2.2.2 (by rw [h3.1, h3.2])
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hβ : orderOf (MulAut.congr ψ α) = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  have hβo : MulAut.congr ψ α ∉
      inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨hcases, -, -, hDinner⟩ := even_unitary_involution_matrix_lifts h hC hn hq _ hβ
  rcases hcases with hid | hbar
  · exfalso
    apply hβo
    refine hDinner _ ?_ hβ
    rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker]
    exact hid
  obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ, -, hθβ⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hn hq _ hβ hbar
  have hc : MulAut.congr θ (primeFormFieldHom h hC₀ (primeFormFieldFactor h hC hn hq
      (MulAut.congr ψ α))) = MulAut.congr ψ α := MulEquiv.ext fun x => (hθβ x).symm
  let eF := (fixedSubgroupCongrEquiv ψ α).trans
    ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (fixedSubgroupCongrEquiv θ _).symm)
  rcases even_unitary_fieldBar_fixed_cases h hn hq hC₀ hcase₀ _ hbar with
    hch | ⟨r, hr, hnr, ⟨Φ⟩⟩
  · exact Or.inl (LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv eF.symm hch)
  · exact Or.inr ⟨h.fixedField, inferInstance, fixedField_finite h,
      UnitaryFieldData.card_fixedField h, r, hr, hnr, ⟨eF.trans Φ⟩⟩

theorem evenOuterFamilyInput_PSU : EvenOuterFamilyInput .PSU := by
  intro J _ n f hadm hm α hα hαo P hP
  change EvenLieConclusion P
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel hadm hm
  have : Finite K := h.finite
  have : Finite J := Finite.of_equiv _ ψ.symm.toEquiv
  rcases even_unitary_outer_fixed_cases hadm hm α hα hαo with
    hch | ⟨k, _, _, hk, r, hr, -, ⟨Φ⟩⟩
  · exact absurd hP (not_isPComponent_of_isCharacteristicP hch P)
  · have : Finite (GL (Fin r ⊕ Fin r) k) := Finite.of_injective Units.val Units.val_injective
    exact evenLieConclusion_of_mulEquiv Φ
      (fun M hM => evenLieConclusion_statedSp hadm.2.1 hk hr M hM) hP
end CFSG.ComponentClassification.CatLeafProof
