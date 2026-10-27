module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Data

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {F : Type} [Field F]

@[expose] noncomputable def signDiagE7 (F : Type) [Field F] (δ : Fin (Tag.rank .E7) → ℤ) :
    ModGL .E7 F :=
  rootDiagUnit .E7 (thetaDiag δ (-1 : Fˣ))

theorem weylElt_conj_signDiagE7 (j : Fin (Tag.rank .E7)) (δ : Fin (Tag.rank .E7) → ℤ) :
    weylElt .E7 F j 1 * signDiagE7 F δ * (weylElt .E7 F j 1)⁻¹ =
      signDiagE7 F (reflect .E7 j δ) := by
  unfold signDiagE7
  rw [weylElt_conj_rootDiagUnit, thetaDiag_reflect_E7 j δ]

@[expose] noncomputable def nWordE7 (F : Type) [Field F] (l : List (Fin (Tag.rank .E7))) :
    ModGL .E7 F :=
  (l.map fun j => weylElt .E7 F j 1).prod

theorem nWordE7_mem_levi {l : List (Fin (Tag.rank .E7))} (hl : ∀ j ∈ l, j ∈ JE7) :
    nWordE7 F l ∈ parabolicLevi .E7 F JE7 := by
  induction l with
  | nil => exact one_mem _
  | cons j l ih =>
    rw [nWordE7, List.map_cons, List.prod_cons]
    exact mul_mem (weylElt_mem_parabolicLevi (hl j List.mem_cons_self))
      (ih fun i hi => hl i (List.mem_cons_of_mem _ hi))

theorem nWordE7_conj (l : List (Fin (Tag.rank .E7))) (δ : Fin (Tag.rank .E7) → ℤ) :
    nWordE7 F l * signDiagE7 F δ * (nWordE7 F l)⁻¹ = signDiagE7 F (wordActE7 l δ) := by
  induction l with
  | nil => simp [nWordE7, wordActE7]
  | cons j l ih =>
    have h1 : nWordE7 F (j :: l) = weylElt .E7 F j 1 * nWordE7 F l := by
      rw [nWordE7, List.map_cons, List.prod_cons]
      rfl
    have h2 : wordActE7 (j :: l) δ = reflect .E7 j (wordActE7 l δ) := rfl
    rw [h1, h2, ← weylElt_conj_signDiagE7 j, ← ih]
    group

theorem exists_levi_conj_partnerE7 {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsPartnerE7 δ) :
    ∃ n ∈ parabolicLevi .E7 F JE7,
      n * signDiagE7 F deltaE7 * n⁻¹ = signDiagE7 F δ := by
  obtain ⟨l, hlJ, rfl⟩ := exists_word_partnerE7 hδ
  exact ⟨nWordE7 F l, nWordE7_mem_levi hlJ, nWordE7_conj l deltaE7⟩

end CFSG.ClassicalInvolution.ModelFacts.Levi
