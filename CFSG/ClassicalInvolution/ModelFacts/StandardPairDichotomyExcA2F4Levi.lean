module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Data

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {F : Type} [Field F]

@[expose] noncomputable def signDiagF4 (F : Type) [Field F] (δ : Fin (Tag.rank .F4) → ℤ) :
    ModGL .F4 F :=
  rootDiagUnit .F4 (corootDiagF4 δ (-1 : Fˣ))

theorem weylElt_conj_signDiagF4 (j : Fin (Tag.rank .F4)) {δ : Fin (Tag.rank .F4) → ℤ}
    (hδ : IsRoot .F4 δ) (hl : iform δ δ = 4) :
    weylElt .F4 F j 1 * signDiagF4 F δ * (weylElt .F4 F j 1)⁻¹ =
      signDiagF4 F (reflect .F4 j δ) := by
  unfold signDiagF4
  rw [weylElt_conj_rootDiagUnit, corootDiagF4_reflect j hδ hl]

@[expose] noncomputable def nWordF4 (F : Type) [Field F] (l : List (Fin (Tag.rank .F4))) :
    ModGL .F4 F :=
  (l.map fun j => weylElt .F4 F j 1).prod

theorem nWordF4_mem_levi {l : List (Fin (Tag.rank .F4))} (hl : ∀ j ∈ l, j ∈ JF4) :
    nWordF4 F l ∈ parabolicLevi .F4 F JF4 := by
  induction l with
  | nil => exact one_mem _
  | cons j l ih =>
    rw [nWordF4, List.map_cons, List.prod_cons]
    exact mul_mem (weylElt_mem_parabolicLevi (hl j List.mem_cons_self))
      (ih fun i hi => hl i (List.mem_cons_of_mem _ hi))

theorem wordActF4_isRoot (l : List (Fin (Tag.rank .F4))) {δ : Fin (Tag.rank .F4) → ℤ}
    (hδ : IsRoot .F4 δ) (hl : iform δ δ = 4) :
    IsRoot .F4 (wordActF4 l δ) ∧ iform (wordActF4 l δ) (wordActF4 l δ) = 4 := by
  induction l with
  | nil => exact ⟨hδ, hl⟩
  | cons j l ih =>
    refine ⟨IsRoot.reflect j ih.1, ?_⟩
    change iform (reflect .F4 j (wordActF4 l δ)) (reflect .F4 j (wordActF4 l δ)) = 4
    rw [iform_reflect]
    exact ih.2

theorem nWordF4_conj (l : List (Fin (Tag.rank .F4))) {δ : Fin (Tag.rank .F4) → ℤ}
    (hδ : IsRoot .F4 δ) (hl : iform δ δ = 4) :
    nWordF4 F l * signDiagF4 F δ * (nWordF4 F l)⁻¹ = signDiagF4 F (wordActF4 l δ) := by
  induction l with
  | nil => simp [nWordF4, wordActF4]
  | cons j l ih =>
    have h1 : nWordF4 F (j :: l) = weylElt .F4 F j 1 * nWordF4 F l := by
      rw [nWordF4, List.map_cons, List.prod_cons]
      rfl
    have h2 : wordActF4 (j :: l) δ = reflect .F4 j (wordActF4 l δ) := rfl
    obtain ⟨hr, hlong⟩ := wordActF4_isRoot l hδ hl
    rw [h1, h2, ← weylElt_conj_signDiagF4 j hr hlong, ← ih]
    group

theorem exists_levi_conj_partnerF4 {δ : Fin (Tag.rank .F4) → ℤ} (hδ : IsPartnerF4 δ) :
    ∃ n ∈ parabolicLevi .F4 F JF4,
      n * signDiagF4 F deltaF4 * n⁻¹ = signDiagF4 F δ := by
  obtain ⟨l, hlJ, rfl⟩ := exists_word_partnerF4 hδ
  have h0 := isPartnerF4_deltaF4
  exact ⟨nWordF4 F l, nWordF4_mem_levi hlJ, nWordF4_conj l h0.1 h0.2.1⟩

end CFSG.ClassicalInvolution.ModelFacts.Levi
