module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatLeafProof (GLS3OddFamilyInput
  nonempty_mulEquiv_primeFormP_of_lieModel')
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem a6Shape_PSU_iff (n f : ℕ) : A6Shape .PSU n f ↔ (n = 3 ∧ f = 2) ∨ (n = 4 ∧ f = 1) := by
  unfold A6Shape
  simp

theorem oddA6Shape_PSU (hO : LieOrderFormulasInput) (hgls : GLS3OddFamilyInput .PSU) :
    OddA6Shape .PSU := by
  apply oddA6Shape_of_concrete
  intro S _ _ n p f hp hp2 hadm hm
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  have hn : 3 ≤ n := hadm.2.2.1
  haveI : Finite K := h.finite
  refine ⟨primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), inferInstance,
    inferInstance, ψ, ?_⟩
  intro σ D hσ hA
  have hmX : LieModel (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) .PSU n p f :=
    LieModel.of_mulEquiv ψ hm
  have hp3 : p = 3 := hA.char_three hO hgls hp hp2 hadm hmX hσ
  subst hp3
  refine ⟨rfl, ?_, fun h' => absurd h' (by decide)⟩
  rw [a6Shape_PSU_iff]
  by_contra hs
  have hq : ¬(n = 3 ∧ 3 ^ f = 2) := fun h3 => hadm.2.2.2 (by rw [h3.1, h3.2])
  by_cases h31 : n = 3 ∧ f = 1
  · obtain ⟨rfl, rfl⟩ := h31
    have hdvd : 360 ∣ Nat.card (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
      hA.dvd.trans (Subgroup.card_subgroup_dvd_card _)
    exact psu_not_dvd_three_three hO hadm hmX hdvd
  have hnot : ¬ ((n = 3 ∧ f = 1) ∨ (n = 3 ∧ f = 2) ∨ (n = 4 ∧ f = 1)) := by
    rintro (h1 | h2 | h3)
    · exact h31 h1
    · exact hs (Or.inl h2)
    · exact hs (Or.inr h3)
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq σ
  have hff : primeFormFieldFactor h hC hn hq σ = φ := by
    rw [← hAφ, primeFormFieldFactor_psi]
  have hφ2 : φ * φ = 1 := by
    rw [← hff, ← map_mul, ← pow_two]
    have h1 := pow_orderOf_eq_one σ
    rw [hσ] at h1
    rw [h1, map_one]
  rcases ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · have hAσ : σ = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    subst hAσ
    exact psuInner_false hO h hn hnot A hσ hA
  · subst hAφ
    exact psuGraph_false hO h hn hnot A φ hφ hσ hA

end CFSG.ComponentClassification.CatFC
