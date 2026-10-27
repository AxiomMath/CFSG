module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Data

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {F : Type} [Field F]

@[expose] noncomputable def signDiagE8 (F : Type) [Field F] (δ : Fin (Tag.rank .E8) → ℤ) :
    ModGL .E8 F :=
  rootDiagUnit .E8 (thetaDiag δ (-1 : Fˣ))

theorem weylElt_conj_signDiagE8 (j : Fin (Tag.rank .E8)) (δ : Fin (Tag.rank .E8) → ℤ) :
    weylElt .E8 F j 1 * signDiagE8 F δ * (weylElt .E8 F j 1)⁻¹ =
      signDiagE8 F (reflect .E8 j δ) := by
  unfold signDiagE8
  rw [weylElt_conj_rootDiagUnit, thetaDiag_reflect j δ]

@[expose] noncomputable def nWordE8 (F : Type) [Field F] (l : List (Fin (Tag.rank .E8))) :
    ModGL .E8 F :=
  (l.map fun j => weylElt .E8 F j 1).prod

theorem nWordE8_mem_levi {l : List (Fin (Tag.rank .E8))} (hl : ∀ j ∈ l, j ∈ JE8) :
    nWordE8 F l ∈ parabolicLevi .E8 F JE8 := by
  induction l with
  | nil => exact one_mem _
  | cons j l ih =>
    rw [nWordE8, List.map_cons, List.prod_cons]
    exact mul_mem (weylElt_mem_parabolicLevi (hl j List.mem_cons_self))
      (ih fun i hi => hl i (List.mem_cons_of_mem _ hi))

theorem nWordE8_conj (l : List (Fin (Tag.rank .E8))) (δ : Fin (Tag.rank .E8) → ℤ) :
    nWordE8 F l * signDiagE8 F δ * (nWordE8 F l)⁻¹ = signDiagE8 F (wordActE8 l δ) := by
  induction l with
  | nil => simp [nWordE8, wordActE8]
  | cons j l ih =>
    have h1 : nWordE8 F (j :: l) = weylElt .E8 F j 1 * nWordE8 F l := by
      rw [nWordE8, List.map_cons, List.prod_cons]
      rfl
    have h2 : wordActE8 (j :: l) δ = reflect .E8 j (wordActE8 l δ) := rfl
    rw [h1, h2, ← weylElt_conj_signDiagE8 j, ← ih]
    group

theorem exists_levi_conj_partnerE8 {δ : Fin (Tag.rank .E8) → ℤ} (hδ : IsPartnerE8 δ) :
    ∃ n ∈ parabolicLevi .E8 F JE8,
      n * signDiagE8 F deltaE8 * n⁻¹ = signDiagE8 F δ := by
  obtain ⟨l, hlJ, rfl⟩ := exists_word_partnerE8 hδ
  exact ⟨nWordE8 F l, nWordE8_mem_levi hlJ, nWordE8_conj l deltaE8⟩

end CFSG.ClassicalInvolution.ModelFacts.Levi
