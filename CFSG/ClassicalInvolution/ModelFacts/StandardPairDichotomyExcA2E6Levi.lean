module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Data

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {F : Type} [Field F]

@[expose] noncomputable def signDiagE6 (F : Type) [Field F] (δ : Fin (Tag.rank .E6) → ℤ) :
    ModGL .E6 F :=
  rootDiagUnit .E6 (thetaDiag δ (-1 : Fˣ))

theorem weylElt_conj_signDiagE6 (j : Fin (Tag.rank .E6)) (δ : Fin (Tag.rank .E6) → ℤ) :
    weylElt .E6 F j 1 * signDiagE6 F δ * (weylElt .E6 F j 1)⁻¹ =
      signDiagE6 F (reflect .E6 j δ) := by
  unfold signDiagE6
  rw [weylElt_conj_rootDiagUnit, thetaDiag_reflect_E6 j δ]

@[expose] noncomputable def nWordE6 (F : Type) [Field F] (l : List (Fin (Tag.rank .E6))) :
    ModGL .E6 F :=
  (l.map fun j => weylElt .E6 F j 1).prod

theorem nWordE6_mem_levi {l : List (Fin (Tag.rank .E6))} (hl : ∀ j ∈ l, j ∈ JE6) :
    nWordE6 F l ∈ parabolicLevi .E6 F JE6 := by
  induction l with
  | nil => exact one_mem _
  | cons j l ih =>
    rw [nWordE6, List.map_cons, List.prod_cons]
    exact mul_mem (weylElt_mem_parabolicLevi (hl j List.mem_cons_self))
      (ih fun i hi => hl i (List.mem_cons_of_mem _ hi))

theorem nWordE6_conj (l : List (Fin (Tag.rank .E6))) (δ : Fin (Tag.rank .E6) → ℤ) :
    nWordE6 F l * signDiagE6 F δ * (nWordE6 F l)⁻¹ = signDiagE6 F (wordActE6 l δ) := by
  induction l with
  | nil => simp [nWordE6, wordActE6]
  | cons j l ih =>
    have h1 : nWordE6 F (j :: l) = weylElt .E6 F j 1 * nWordE6 F l := by
      rw [nWordE6, List.map_cons, List.prod_cons]
      rfl
    have h2 : wordActE6 (j :: l) δ = reflect .E6 j (wordActE6 l δ) := rfl
    rw [h1, h2, ← weylElt_conj_signDiagE6 j, ← ih]
    group

theorem exists_levi_conj_partnerE6 {δ : Fin (Tag.rank .E6) → ℤ} (hδ : IsPartnerE6 δ) :
    ∃ n ∈ parabolicLevi .E6 F JE6,
      n * signDiagE6 F deltaE6 * n⁻¹ = signDiagE6 F δ := by
  obtain ⟨l, hlJ, rfl⟩ := exists_word_partnerE6 hδ
  exact ⟨nWordE6 F l, nWordE6_mem_levi hlJ, nWordE6_conj l deltaE6⟩

end CFSG.ClassicalInvolution.ModelFacts.Levi
