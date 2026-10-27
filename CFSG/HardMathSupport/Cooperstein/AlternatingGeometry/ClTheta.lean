module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClClassify
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaJJoin
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IsoBlocksFixed
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderOfNatural

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Open

variable {G : Type} [Group G]

theorem pre_of_theta {S M : Subgroup G} (hS2 : IsPGroup 2 S) (hSM : S ≤ M) {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω] (θ : ↥M →* Perm Ω)
    (hsh : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      Offender.OffenderShapeConcl ((A.subgroupOf M).map θ)) :
    Classif.Pre (((thompsonJ S).subgroupOf M).map θ)
      (fun A : {A : Subgroup G // IsMaxElemAbelian S A} => (A.1.subgroupOf M).map θ) := by
  have hJS : thompsonJ S ≤ S := iSup_le fun A => iSup_le fun hA => hA.1
  have hAJ : ∀ A : Subgroup G, IsMaxElemAbelian S A → A ≤ thompsonJ S := fun A hA =>
    le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) A hA
  refine ⟨?_, ?_, ?_, ?_, fun A => hsh A.1 A.2⟩
  · exact ((hS2.comap_subtype (K := M)).map θ).to_le
      (Subgroup.map_mono (Subgroup.comap_mono hJS))
  · intro A
    exact Subgroup.map_mono (Subgroup.comap_mono (hAJ A.1 A.2))
  · rw [map_thompsonJ_eq_iSup hSM θ]
    exact iSup₂_le fun A hA =>
      le_iSup (fun i : {A : Subgroup G // IsMaxElemAbelian S A} => (i.1.subgroupOf M).map θ) ⟨A, hA⟩
  · intro A
    rintro g ⟨a, ha, rfl⟩
    have haA : (a : G) ∈ A.1 := Subgroup.mem_subgroupOf.1 ha
    have : (a * a : ↥M) = 1 := by
      apply Subtype.ext
      exact ((isElemAb2_of_isElemAbelian A.2.2.1) a haA).1
    rw [← map_mul, this, map_one]

namespace Classif.Setup

open MulAction

variable {d : ℕ} {W : Subgroup (Perm (Fin d))} {ι : Type*} {E : ι → Subgroup (Perm (Fin d))}
  (S : Setup W E)

theorem isIsoPair_of_card_orbit_two {z : Fin d} (h : Nat.card (orbit W z) = 2) :
    IsIsoPair W z (S.ω z) := by
  have hsub : ({z, S.ω z} : Set (Fin d)) ⊆ orbit W z := by
    intro y hy
    rcases hy with rfl | rfl
    · exact mem_orbit_self _
    · exact S.partner_mem_orbit _
  have hcard : (orbit W z : Set (Fin d)).ncard ≤ ({z, S.ω z} : Set (Fin d)).ncard := by
    rw [Set.ncard_pair (S.hmatch z).symm, ← Nat.card_coe_set_eq]; exact h.le
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  refine ⟨(S.hmatch z).symm, S.swap_mem z, fun w hw => ?_⟩
  have : w z ∈ (orbit W z : Set (Fin d)) := ⟨⟨w, hw⟩, rfl⟩
  rw [← heq] at this
  exact this

end Classif.Setup

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
