module

public import Certificates.Certificate320004
public import CFSG.Certificates.Kernel.Misc.Coset.PGChain

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.CosetTable

theorem g23_check_H :
    (genSub {r : FreeGroup (Fin 6) | r ∈ g23Words.map FreeGroup.mk}
        (subsetOf 6 [0, 1, 2, 3, 4])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 6) | r ∈ g23Words.map FreeGroup.mk}
        (subsetOf 6 [0, 1, 2, 3, 4])).index ≤ 7371 :=
  Certificates.certificate320004.1

theorem g23_check_triv :
    Finite (PG (subsetOf 6 [0, 1, 2, 3, 4]).length
        (restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) g23Words)) ∧
      Nat.card (PG (subsetOf 6 [0, 1, 2, 3, 4]).length
        (restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) g23Words)) ≤ 576 :=
  Certificates.certificate320004.2.1

theorem card_PG_le :
    Finite (PG 6 g23Words) ∧ Nat.card (PG 6 g23Words) ≤ 7371 * 576 :=
  CFSG.KC.MiscCoset.card_le_of_index_restrict g23Words (subsetOf 6 [0, 1, 2, 3, 4]) g23_check_H
    g23_check_triv

@[expose] def SatisfiesWords {X : Type*} [Group X] (ws : List (List (Fin 6 × Bool)))
    (ρ : Fin 6 → X) : Prop :=
  ∀ r ∈ ws, FreeGroup.lift ρ (FreeGroup.mk r) = 1

@[expose] def SatisfiesG23Words {X : Type*} [Group X] (ρ : Fin 6 → X) : Prop :=
  ∀ r ∈ g23Words, FreeGroup.lift ρ (FreeGroup.mk r) = 1

theorem card_closure_le {X : Type*} [Group X] (ρ : Fin 6 → X) (h : SatisfiesG23Words ρ) :
    Nat.card (Subgroup.closure (Set.range ρ)) ≤ 7371 * 576 := by
  obtain ⟨hfin, hc⟩ := card_PG_le
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ g23Words.map FreeGroup.mk},
      FreeGroup.lift ρ r = 1 := by
    rintro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact h w hw
  let φ : PG 6 g23Words →* X := PresentedGroup.toGroup hrel
  have hrange : φ.range = Subgroup.closure (Set.range ρ) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
      {r : FreeGroup (Fin 6) | r ∈ g23Words.map FreeGroup.mk}, MonoidHom.map_closure]
    congr 1
    ext x
    simp [φ, PresentedGroup.toGroup.of]
  rw [← hrange]
  exact (Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective).trans hc

end CFSG.GH74.QTGen4.Recog.G23
