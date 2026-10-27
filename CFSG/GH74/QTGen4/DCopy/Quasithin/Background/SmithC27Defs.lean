module

public import CFSG.Quasithin.Background.SmithC27Defs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C2Seven

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable (G) in

@[expose] def ASC27Residue_F4 : Prop :=
  ∀ H R M K V : Subgroup G, HypC23 H R M → K ∈ cComp H →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → CharTwo K → ¬ K ≤ M →
    R ≤ Subgroup.normalizer (K : Set G) → V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) →
    ¬ IsChiBlock2 H K → ¬ IsExcA7Block K → ¬ IsSylowTwoOf R (K ⊔ R) →
    C27Concl H R M K V

theorem asc27Statement_of_parts_F4
    (h : ∀ H R M K : Subgroup G, Hyp27 H R M K →
      C27Concl H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) :
    ASC27Statement_F4 G := by
  intro H R M K V hyp hK hq hc hn hR hV
  subst hV
  exact h H R M K ⟨hyp, hK, hq, hc, hn, hR⟩

theorem asc27Statement_of_residue_of_cases_F4 (hres : ASC27Residue_F4 G)
    (hcases : ∀ H R M K : Subgroup G, Hyp27 H R M K →
      (IsChiBlock2 H K ∨ IsExcA7Block K ∨ IsSylowTwoOf R (K ⊔ R)) →
      C27Concl H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) :
    ASC27Statement_F4 G := by
  refine asc27Statement_of_parts_F4 fun H R M K h => ?_
  by_cases hc : IsChiBlock2 H K ∨ IsExcA7Block K ∨ IsSylowTwoOf R (K ⊔ R)
  · exact hcases H R M K h hc
  · simp only [not_or] at hc
    exact hres H R M K _ h.hyp h.comp h.quasi h.charTwo h.not_le h.norm rfl hc.1 hc.2.1 hc.2.2

end CFSG.Quasithin.SmithC27
