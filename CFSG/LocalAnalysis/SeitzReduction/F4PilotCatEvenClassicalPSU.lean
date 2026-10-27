module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSU
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenOuter

public noncomputable section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial FourGroupEvenCanonical UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer

variable {f n : ℕ} {K : Type} [Field K]

theorem psu_fieldBar_cases (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ f = 2)) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    (∃ r : ℕ, 1 ≤ r ∧ (n = 2 * r ∨ n = 2 * r + 1) ∧
        Nonempty (fixedSubgroup (primeFormFieldHom h hC σ) ≃* StatedSp r h.fixedField)) ∨
      IsCharacteristicP 2 (fixedSubgroup (primeFormFieldHom h hC σ)) := by
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
    (CatLeafProof.fixedInnerEquiv hcj _).trans ((MulEquiv.subgroupCongr heq).trans
      (MonoidHom.ofInjective hinjU).symm)
  rcases canonical_case_of_map h hCl hcase with h1 | ⟨r, hr, hJ⟩
  · rcases Nat.even_or_odd n with hev | ⟨r, hr⟩
    · right
      have hch := CatLeafProof.isCharacteristicP_matrixIsometryGroup_one (k := h.fixedField) hev hn
      rw [← h1] at hch
      exact LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv Φ.symm hch
    · left
      have hC1 : (Cl : Matrix (Fin n) (Fin n) h.fixedField) =
          ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) := by
        rw [h1, Units.val_one]
      obtain ⟨e₂⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _
        (OutcomeLocal.dotForm_restrict_isAlt (k := h.fixedField) (n := n))
        (OutcomeLocal.dotForm_restrict_nondegenerate hr) (OutcomeLocal.finrank_dotForm_ker hr)
      exact ⟨r, by omega, Or.inr hr, ⟨Φ.trans (((MulEquiv.subgroupCongr
        (congrArg matrixIsometryGroup hC1)).trans (OutcomeLocal.oneRestrictEquiv hr)).trans e₂)⟩⟩
  · left
    exact ⟨r, by omega, Or.inl hr, ⟨Φ.trans ((MulEquiv.subgroupCongr
      (congrArg matrixIsometryGroup hJ)).trans
        (OutcomeLocal.blockSwapIsometryEquivStatedSp (by omega)))⟩⟩

theorem psu_outer_fixed {J : Type} [Group J] {n e : ℕ} (hadm : StatedLieAdmissible .PSU n 2 e)
    (hm : LieModel J .PSU n 2 e) (α : MulAut J) (hα : orderOf α = 2)
    (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    SpFixedOrNotSp6 (fixedSubgroup α) (fun r g => g = e ∧ (n = 2 * r ∨ n = 2 * r + 1)) := by
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel hadm hm
  have hn : 3 ≤ n := hadm.2.2.1
  have hq : ¬(n = 3 ∧ 2 ^ e = 2) := fun h3 => hadm.2.2.2 (by rw [h3.1, h3.2])
  have : Finite K := h.finite
  have : Finite J := Finite.of_equiv _ ψ.symm.toEquiv
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
  refine spFixedOrNotSp6_of_mulEquiv ((fixedSubgroupCongrEquiv ψ α).trans
    ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (fixedSubgroupCongrEquiv θ _).symm)) ?_
  have := fixedField_finite h
  rcases psu_fieldBar_cases h hn hq hC₀ hcase₀ _ hbar with ⟨r, hr1, hnr, ⟨Φ⟩⟩ | hch
  · exact Or.inl ⟨h.fixedField, inferInstance, inferInstance, r, e, h.card_fixedField, hr1,
      ⟨rfl, hnr⟩, ⟨Φ⟩⟩
  · exact Or.inr (notSp6Components_of_isCharacteristicP hch)

theorem catSp6EvenOuterFamily_PSU (hdet : Sp6EvenTypeDet) : CatSp6EvenOuterFamily .PSU := by
  intro S _ _ _ _ n e hadm hm σ hσ hout f D hD hD6 _
  obtain ⟨⟨rfl, hn⟩, hfix⟩ :=
    sp6_of_spFixedOrNotSp6 hdet (psu_outer_fixed hadm hm σ hσ hout) hD hD6
  refine ⟨?_, hfix⟩
  rcases hn with rfl | rfl
  · exact Or.inr (Or.inr (Or.inl hm))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))

end CFSG.SeitzReduction.F4Pilot
