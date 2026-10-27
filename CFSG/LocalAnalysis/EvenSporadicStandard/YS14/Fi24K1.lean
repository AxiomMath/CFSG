module

public import CFSG.Sporadic.Fi24.Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi23Lift

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.Sporadic.Fi24 (R J JR jR tR MR D24 M)
open CFSG.ComponentClassification.M12Cover (FourClassesLarge)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem MR_centralizes_eq_one {x : R} (hx : x ∈ MR) (hc : ∀ m ∈ MR, m * x = x * m) : x = 1 := by
  obtain ⟨g, hg, rfl⟩ := hx
  have hz : (⟨g, hg⟩ : ↥M) ∈ Subgroup.center ↥M := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    apply CFSG.Sporadic.Fi24.jR_injective
    have := hc (jR h.1) ⟨h.1, h.2, rfl⟩
    simpa [map_mul] using this
  rw [CFSG.Sporadic.Fi24.center_M] at hz
  have h1 : g = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hz)
  rw [h1, map_one]

theorem MR_perfect : MR ≤ ⁅MR, MR⁆ := by
  haveI := CFSG.Sporadic.Fi24.isSimpleGroup_M
  have hne : CFSG.Sporadic.Fi24.fi23EquivM.symm CFSG.Sporadic.Fi23.a *
      CFSG.Sporadic.Fi24.fi23EquivM.symm CFSG.Sporadic.Fi23.y ≠
      CFSG.Sporadic.Fi24.fi23EquivM.symm CFSG.Sporadic.Fi23.y *
      CFSG.Sporadic.Fi24.fi23EquivM.symm CFSG.Sporadic.Fi23.a := by
    rw [← map_mul, ← map_mul, Ne, CFSG.Sporadic.Fi24.fi23EquivM.symm.injective.eq_iff]
    exact CFSG.Sporadic.Fi24.fi23_a_mul_y_ne
  have h1 : commutator ↥M = ⊤ := CFSG.Sporadic.Fi24.commutator_eq_top_of_simple hne
  let f : ↥M →* R := (jR.comp M.subtype)
  have hrange : (⊤ : Subgroup ↥M).map f = MR := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, f, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have h2 : ⁅MR, MR⁆ = (commutator ↥M).map f := by
    rw [commutator_def, Subgroup.map_commutator, hrange]
  rw [h2, h1, hrange]

theorem fourClassesLarge_centralizer_tR :
    FourClassesLarge ↥(Subgroup.centralizer ({tR} : Set R)) := by
  haveI : Finite R := inferInstance
  refine CFSG.EvenSporadicStandard.HypOne.Fi23.fourClassesLarge_of_perfect_few
    (K := Subgroup.centralizer ({tR} : Set R)) (P := MR) ?_ MR_perfect ?_
  · intro m hm
    exact Subgroup.mem_centralizer_singleton_iff.2
      (CFSG.Sporadic.Fi24.commute_tR_of_mem_MR hm)
  · intro x hx hxP _ _
    have htt : tR * tR = 1 := CFSG.Sporadic.Fi24.tR_mul_tR
    rcases CFSG.Sporadic.Fi24.mem_MR_or_of_commute hx with h | h
    · have := MR_centralizes_eq_one h (fun m hm => hxP m hm)
      rw [this]; simp
    · have h1 : x * tR = 1 := MR_centralizes_eq_one h (fun m hm => by
        have hm' := hxP m hm
        have hmT := CFSG.Sporadic.Fi24.commute_tR_of_mem_MR hm
        calc m * (x * tR) = (m * x) * tR := by group
          _ = (x * m) * tR := by rw [hm']
          _ = x * (m * tR) := by group
          _ = x * (tR * m) := by rw [hmT]
          _ = (x * tR) * m := by group)
      have hx1 : x = tR := by
        calc x = x * tR * tR := by rw [mul_assoc, htt, mul_one]
          _ = tR := by rw [h1, one_mul]
      rw [hx1, sq, htt]

theorem fourClassesLarge_centralizer_D24 {u : R} (hu : u ∈ D24) :
    FourClassesLarge ↥(Subgroup.centralizer ({u} : Set R)) :=
  CFSG.EvenSporadicStandard.HypOne.Fi23.fourClassesLarge_of_isConj hu
    fourClassesLarge_centralizer_tR

end CFSG.EvenSporadicStandard.YS14
