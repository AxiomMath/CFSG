module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.J2Cover
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.O8Data CFSG.ClassicalInvolution.Q3.TL4.E4O8Data
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C

@[expose] noncomputable def rootP : List (Equiv.Perm (Fin 360)) := (List.range 8).map gen

theorem forall₂_root : List.Forall₂ (Rep 360) (rootA ()) rootP := by
  rw [rootA, rootP, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro h hh
  exact rep_gen (by rw [List.mem_range] at hh; omega)

theorem omegaT_eq_closure_root : omegaT = Subgroup.closure {x | x ∈ rootP} := by
  rw [omegaT_eq]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, rootP, List.mem_map, List.mem_range]

theorem ident_omega {K : Subgroup (Equiv.Perm (Fin 360))} {s : Equiv.Perm (Fin 360)}
    (hd : Vtx.AmbientQuatDatum omegaT K s) : ∃ g ∈ omegaT, conjSub g K = K0 :=
  Certificates.certificate125.2.2.2.1 hd

theorem forall₂_ws : List.Forall₂ (Rep 360) (wsA ()) wsP :=
  forall₂_perms fun a ha => ⟨_, (data_spec (List.mem_append_right _ ha)).1⟩

theorem ws_mem (k : ℕ) : wsP.getD k 1 ∈ omegaT := by
  rw [List.getD_eq_getElem?_getD]
  cases h : wsP[k]? with
  | none => exact omegaT.one_mem
  | some g =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? h)
    exact (data_spec (List.mem_append_right _ ha)).2

theorem exists_member {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT) :
    ∃ k < wsP.length, conjSub g K0 = conjSub (wsP.getD k 1) K0 :=
  Certificates.certificate125.2.2.2.2.1.2 hg

theorem reflTransGen_starRel {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT) :
    Relation.ReflTransGen (Vtx.StarRel omegaT K0) K0 (conjSub g K0) :=
  Certificates.certificate125.2.2.2.2.2.1 hg

theorem mem_twins_of_le_normalizer {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT)
    (hne : conjSub g K0 ≠ K0) (hle : conjSub g K0 ≤ Subgroup.normalizer (K0 : Set _)) :
    ∃ k ∈ [1, 3, 4], conjSub g K0 = conjSub (wsP.getD k 1) K0 :=
  Certificates.certificate125.2.2.2.2.2.2.1 hg hne hle

theorem edge : conjSub (wsP.getD 1 1) K0 ≠ K0 ∧
    conjSub (wsP.getD 1 1) K0 ≤ Subgroup.normalizer (K0 : Set _) :=
  Certificates.certificate125.2.2.2.2.2.2.2

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
