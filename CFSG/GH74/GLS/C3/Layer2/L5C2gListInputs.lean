module

public import CFSG.GH74.GLS.C3.Layer2.L5C2e
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
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2a
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2b
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2c
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2d
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2e
public import CFSG.GH74.GLS.C3.Layer2.L5C2gInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2gInputs
public import Certificates.Certificate5051
public import Certificates.Certificate5057

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

theorem evalWG_mem {G : Type} [Group G] (S : Subgroup G) {gs : List G} (hgs : ∀ g ∈ gs, g ∈ S)
    (w : List Nat) : evalWG gs w ∈ S := by
  have hgen : ∀ i, gs.getD i 1 ∈ S := by
    intro i
    by_cases hi : i < gs.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact hgs _ (List.getElem_mem hi)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : gs.length ≤ i)]
      exact S.one_mem
  have key : ∀ (w : List Nat) (a : G), a ∈ S → w.foldl (fun a i => a * gs.getD i 1) a ∈ S := by
    intro w
    induction w with
    | nil => intro a ha; exact ha
    | cons i w ih => intro a ha; exact ih _ (S.mul_mem ha (hgen i))
  exact key w 1 S.one_mem

theorem sh1WW_chk :
    (sh1WW.all fun pw => decide (evalWG sh1Gens pw.2 = pw.1)) = true ∧
    sh1WW.length = 128 ∧ (sh1WW.map fun pw => codeP16 pw.1).Nodup :=
  Certificates.certificate5057

theorem mem_closureList_gens {G : Type} [Group G] [DecidableEq G] (gens : List G) (k : ℕ) {g : G}
    (hg : g ∈ gens) : g ∈ closureList gens (k + 1) := by
  have h1 := one_mem_closureList gens k
  simp only [closureList, Function.iterate_succ_apply', closureStep, List.mem_dedup,
    List.mem_append, List.mem_flatMap, List.mem_map] at h1 ⊢
  right
  exact ⟨1, h1, g, hg, by simp⟩

theorem sh1Gens_mem : ∀ g ∈ sh1Gens, g ∈ Sh1 := fun _ hg =>
  mem_Sh1.2 (mem_closureList_gens sh1Gens 11 hg)

theorem sh1WW_mem
    (pw : Perm (Fin 16) × List Nat) (h : pw ∈ sh1WW) : pw.1 ∈ Sh1 := by
  have := sh1WW_chk.1
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  rw [← this pw h]
  exact evalWG_mem Sh1 sh1Gens_mem pw.2

@[expose] def sh1M : List ↥Sh1 :=
  sh1WW.pmap (fun pw h => (⟨pw.1, sh1WW_mem pw h⟩ : ↥Sh1)) (fun _ h => h)

@[expose] def sh1Code (m : ↥Sh1) : Nat := codeP16 m.1

end Fus

end CFSG.GH74.GLS.C3.Layer2.L5
