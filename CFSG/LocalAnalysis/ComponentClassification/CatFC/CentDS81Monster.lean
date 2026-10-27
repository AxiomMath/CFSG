module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Basic
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.Existence

set_option linter.unusedSectionVars false


theorem monster_centralizer_thirteen {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (e : Y ≃* Carrier .M) {u : Y} (hu : orderOf u = 2) :
    13 ∣ Nat.card (centralizer ({u} : Set Y)) := by
  obtain ⟨ε⟩ : Nonempty (Y ≃* CFSG.Monster.Generated.Gmat) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.nonempty_mulEquiv_gmat_of_isSimpleGroup e
  have hGA : CFSG.Monster.Generated.Gmat = CFSG.Monster.Griess.AutO :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.gmat_eq_griess
  let φ : Y ≃* MGriess := ε.trans (CFSG.YGroups.Y443.griessEquivGmat hGA).symm
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  obtain ⟨-, a, z, -, -, -, hcl, hA, hB, -⟩ := hE
  have hφu : orderOf (φ u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  rw [card_centralizer_eq φ u]
  rcases hcl (φ u) hφu with h | h
  · obtain ⟨-, hcenter, ⟨f⟩⟩ := hA (φ u) h
    have hZ : Nat.card (center ↥(cent (φ u))) = 2 := by
      have h1 := Subgroup.card_map_of_injective (K := center ↥(cent (φ u)))
        (Subgroup.subtype_injective (cent (φ u)))
      rw [hcenter, Nat.card_zpowers, hφu] at h1
      exact h1.symm
    have hcard : Nat.card ↥(cent (φ u)) =
        Nat.card (↥(cent (φ u)) ⧸ center ↥(cent (φ u))) * 2 := by
      rw [← hZ]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(cent (φ u)))
    rw [show Subgroup.centralizer ({φ u} : Set MGriess) = cent (φ u) from rfl, hcard,
      Nat.card_congr f.toEquiv]
    exact Dvd.dvd.mul_right ((by norm_num : 13 ∣ 7 * 13 * 17 * 19 * 31 * 47).trans
      CFSG.Sporadic.Bridge.B.six_primes_dvd) 2
  · obtain ⟨-, -, -, -, hcardB, -⟩ := hB (φ u) h
    rw [show Subgroup.centralizer ({φ u} : Set MGriess) = cent (φ u) from rfl, hcardB]
    norm_num [twoBCentralizerOrder]

end CFSG.ComponentClassification.CatFC.DS81
