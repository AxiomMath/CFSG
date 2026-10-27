module

public import CFSG.GH74.GLS.C3.Layer2.L5C3a
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C3a
public import CFSG.GH74.GLS.C3.Layer2.L5C3Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C3Inputs
public import Certificates.Certificate5051
public import Certificates.Certificate5058
public import Certificates.Certificate5059

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem limp_eq_true {a b : Bool} : limp a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp [limp]

theorem e16Chk_true : e16Chk Sh1L RhatL1 = true :=
  Certificates.certificate5058

theorem sh1_E16_unique
    (B : Subgroup (Perm (Fin 16))) (hB : B ≤ Sh1) (hcard : Nat.card B = 16)
    (hel : ∀ b ∈ B, b * b = 1) (hab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) : B = RsubP1 := by
  have hchk := e16Chk_true
  unfold e16Chk at hchk
  simp only [List.all_eq_true, map_nrm, limp_eq_true, decide_eq_true_eq] at hchk
  have hle : B ≤ RsubP1 := by
    intro t htB
    by_contra htR
    have ht1 : t ≠ 1 := fun h => htR (by rw [h]; exact RsubP1.one_mem)
    have htR' : t ∉ RhatL1 := htR
    have hlen := hchk t (mem_Sh1.1 (hB htB)) ⟨ht1, hel t htB, htR'⟩
    set Cs : List (Perm (Fin 16)) :=
      Sh1L.filter fun u => decide (u ≠ 1 ∧ u * u = 1 ∧ t * u = u * t) with hCs
    have hT : ((B : Set (Perm (Fin 16))) \ {1}).ncard = 15 := by
      have h1 : (B : Set (Perm (Fin 16))).ncard = 16 := by
        have h0 := Nat.card_coe_set_eq (B : Set (Perm (Fin 16)))
        rw [← h0]
        exact hcard
      rw [Set.ncard_sdiff_singleton_of_mem (by exact B.one_mem), h1]
    have hsub : ((B : Set (Perm (Fin 16))) \ {1}) ⊆ (Cs.toFinset : Set (Perm (Fin 16))) := by
      intro u hu
      obtain ⟨huB, hu1⟩ := hu
      have hu1' : u ≠ 1 := hu1
      simp only [Finset.mem_coe, List.mem_toFinset, hCs, List.mem_filter, decide_eq_true_eq]
      exact ⟨mem_Sh1.1 (hB huB), hu1', hel u huB, hab t htB u huB⟩
    have h15 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [hT, Set.ncard_coe_finset] at h15
    have h16 : Cs.toFinset.card ≤ Cs.length := List.toFinset_card_le Cs
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, RsubP1_card])

end CFSG.GH74.GLS.C3.Layer2.L5
