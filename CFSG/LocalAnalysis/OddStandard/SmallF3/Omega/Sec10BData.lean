module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L44

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Sec10BData (t : G) (L S : Subgroup G) : Prop :=
  secB S L ≤ L ∧ Nat.card (secB S L) = 2 ^ 4 ∧ centralizer (secB S L : Set G) ⊓ L = secB S L ∧
    secA t S L ⊓ L = secB S L ∧ secM t S L ⊓ L = L ⊓ normalizer (secB S L : Set G) ∧
    ∃ φ : (Fin 5 → ZMod 2) → G,
      IsPermModuleVia IsEvenVec φ (secB S L) (L ⊓ normalizer (secB S L : Set G))
        (alternatingGroup (Fin 5)) ∧
      (∀ v, IsEvenVec v → vecWeight v = 4 → IsI4PlusIn L (φ v)) ∧
      (∀ v, IsEvenVec v → vecWeight v = 2 → ¬ IsI4PlusIn L (φ v)) ∧
      ∀ g ∈ normalizer (L : Set G) ⊓ normalizer (secB S L : Set G),
        ∃ σ : Equiv.Perm (Fin 5), ∀ v, IsEvenVec v → g * φ v * g⁻¹ = φ (permVec σ v)

theorem sec10BData_of [Finite G] (hb : Asc82Basic10) (hB5 : Asc82FactB5) {t : G}
    {L S : Subgroup G} {z : G} (h : Sec10Z G t L S z) : Sec10BData t L S := by
  obtain ⟨hpsp, htC, htL, htS, hSN, hsyl⟩ := hb G t L S z h
  obtain ⟨B, hBmax, hB16, hBuniq, hBC, φ, hperm, h4, h2, hσ⟩ :=
    hB5 G L hpsp (S ⊓ L) hsyl
  have hBL : B ≤ L := hBmax.1.trans inf_le_right
  have ht : orderOf t = 2 := h.involution
  have hLt : L ≤ centralizer ({t} : Set G) := h.component.le
  have hJ : secB S L = B := by
    refine le_antisymm ?_ ?_
    · rw [secB, JElem]
      refine (Subgroup.closure_le B).mpr ?_
      rintro x ⟨A, hAmax, hxA⟩
      have hAle : A ≤ S ⊓ L := hAmax.1
      have hAel : CFSG.Open.IsElemAbelian 2 A := hAmax.2.1
      have hcardAB : Nat.card A ≤ Nat.card B := hBmax.2.2 A hAle hAel
      have hcardBA : Nat.card B ≤ Nat.card A := hAmax.2.2 B hBmax.1 hBmax.2.1
      have hcardA : Nat.card A = 2 ^ 4 := (le_antisymm hcardAB hcardBA).trans hB16
      have hAB : A = B := hBuniq A hAle hAel.1 hcardA
      rwa [hAB] at hxA
    · rw [secB, JElem]
      intro b hb
      exact Subgroup.subset_closure ⟨B, hBmax, hb⟩
  have hAL : secA t S L ⊓ L = B := by
    rw [secA, hJ]
    exact sec4_sup_zpowers_inf hBL htC htL ht
  have hML : secM t S L ⊓ L = L ⊓ normalizer (B : Set G) := by
    rw [secM, inf_comm]
    exact sec4_inf_normalizer_eq hLt (by rw [secA, hJ]) hAL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ]; exact hBL
  · rw [hJ]; exact hB16
  · rw [hJ]; exact hBC
  · rw [hJ]; exact hAL
  · rw [hJ]; exact hML
  · refine ⟨φ, ?_, ?_, ?_, ?_⟩
    · simpa [hJ] using hperm
    · exact h4
    · exact h2
    · simpa [hJ] using hσ

end CFSG.OddStandard.SmallF3.Omega
