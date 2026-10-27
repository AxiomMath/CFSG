module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverBasic
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldFamily

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.Quasithin (perfectCore)

section CT

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}

variable (e : L ≃* adjointGroup .E6 (fixSubfield σ))

structure FieldRowCT : Prop where
  quasisimple : CFSG.IsQuasisimple (pieceSup e)
  odd_card_center : Odd (Nat.card (center (pieceSup e)))
  le_pieceSup : L ≤ pieceSup e
  cover : ∃ ψ : e6Data_valid.minGroup K →* pieceSup e,
    Function.Surjective ψ ∧ ψ.ker ≤ center (e6Data_valid.minGroup K)
  quotient : ∃ Ψ : adjointGroup .E6 K ≃* (pieceSup e ⧸ center (pieceSup e)),
    ∀ (x : adjointGroup .E6 (fixSubfield σ)) (g : pieceSup e), (g : G) = ((e.symm x : L) : G) →
      Ψ (fixedFieldInclusion σ x) = QuotientGroup.mk g

variable {e}

theorem odd_card_center_minGroup_e6 :
    Odd (Nat.card (center (e6Data_valid.minGroup K))) := by
  rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K).1]
  exact Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _)

theorem fieldRowCT_of_isScFieldRowFamily {φ : ∀ J, (e6Datum K).leviAmalgam J →* G}
    (hφ : IsScFieldRowFamily e φ) : FieldRowCT e := by
  obtain ⟨ψ, hsurj, hker, hZ, -⟩ := exists_surjective_pieceSup_of_isScFieldRowFamily hφ
  refine ⟨isQuasisimple_pieceSup_of_isScFieldRowFamily hφ, ?_,
    le_pieceSup_of_isScFieldRowFamily hφ, ⟨ψ, hsurj, hker⟩,
    exists_mulEquiv_center_quotient_of_isScFieldRowFamily hφ⟩
  rw [hZ]
  exact Odd.of_dvd_nat odd_card_center_minGroup_e6 (Subgroup.card_map_dvd _ _)

theorem fieldRowCT_of_isFieldRowFamily {φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G}
    (hφ : IsFieldRowFamily e φ) : FieldRowCT e :=
  fieldRowCT_of_isScFieldRowFamily hφ.isScFieldRowFamily

end CT

section Cover

@[expose] def FieldCoverFamilyInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (G : Type) [Group G] [Finite G]
    (L : Subgroup G) (e : L ≃* adjointGroup .E6 (fixSubfield σ))
    (h : FieldNeighbourCover σ e .high), orderOf σ = 2 → 4 ≤ Nat.card (fixSubfield σ) →
    h.p.ker ≠ ⊥ → ∃ φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G, IsFieldRowFamily e φ

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem exists_isFieldRowFamily_of_cover_of_ker_eq_bot (h : FieldNeighbourCover σ e .high)
    (hker : h.p.ker = ⊥) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G, IsFieldRowFamily e φ := by
  obtain ⟨φ, hφ, -⟩ := exists_isFieldRowFamily (h.toIso hker)
    ((h.toNeighbour .six).toIso (h.ker_toNeighbour_eq_bot hker .six))
    ((h.toNeighbour .three).toIso (h.ker_toNeighbour_eq_bot hker .three)) hq
  exact ⟨φ, hφ⟩

theorem fieldRowCT_of_cover (hin : FieldCoverFamilyInput) (h : FieldNeighbourCover σ e .high)
    (hσ : orderOf σ = 2) (hq : 4 ≤ Nat.card (fixSubfield σ)) : FieldRowCT e := by
  by_cases hker : h.p.ker = ⊥
  · obtain ⟨φ, hφ⟩ := exists_isFieldRowFamily_of_cover_of_ker_eq_bot h hker hq
    exact fieldRowCT_of_isFieldRowFamily hφ
  · obtain ⟨φ, hφ⟩ := hin K σ G L e h hσ hq hker
    exact fieldRowCT_of_isFieldRowFamily hφ

end Cover

end CFSG.SeitzReduction.E6Pilot
