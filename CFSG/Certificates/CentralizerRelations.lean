module

public import CFSG.Certificates.CentralizerPresented
public import CFSG.Certificates.CosetTableRelations

public section

namespace CFSG.CosetTable

open CFSG.Certificates CFSG.Certificates.CosetEnumeration
open scoped commutatorElement

variable {m : ℕ}

@[expose] def wordOfCodes (m : ℕ) (w : List ℕ) : List (Fin m × Bool) :=
  w.flatMap fun c => ((List.finRange m).filter fun i => i.val = c / 2).map fun i => (i, c % 2 == 0)

@[expose] def commWord (a s : List (Fin m × Bool)) : List (Fin m × Bool) :=
  FreeGroup.invRev a ++ FreeGroup.invRev s ++ a ++ s

theorem commute_of_mk_commWord {rels : Set (FreeGroup (Fin m))} {a s : List (Fin m × Bool)}
    (h : PresentedGroup.mk rels (FreeGroup.mk (commWord a s)) = 1) :
    Commute (PresentedGroup.mk rels (FreeGroup.mk a)) (PresentedGroup.mk rels (FreeGroup.mk s)) := by
  apply commute_of_comm_eq_one
  rw [← h, commWord, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
    ← FreeGroup.inv_mk, ← FreeGroup.inv_mk]
  simp only [map_mul, map_inv]

theorem finite_of_relCentCheck (ws : List (List (Fin m × Bool))) (a : List (Fin m × Bool))
    (subs : List (List (Fin m × Bool))) {capR capI n cap₂ cap₃ : ℕ}
    (hrel : relCheck ws capR (subs.map (commWord a)) = true)
    (hidx : check (presParams ws subs) capI n = true)
    (h2 : check (presParams (ws ++ [a]) []) cap₂ 1 = true)
    (h3 : check (presParams (ws ++ commWords m) []) cap₃ 1 = true) : Finite (PG m ws) := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set x : PG m ws := PresentedGroup.mk rels (FreeGroup.mk a)
  set H : Subgroup (PG m ws) :=
    Subgroup.closure {g | ∃ s ∈ subs, g = PresentedGroup.mk rels (FreeGroup.mk s)}
  have hrel' := eq_one_of_relCheck ws hrel
  have hH : H ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_mk_commWord (hrel' _ (List.mem_map_of_mem hs))).eq.symm
  obtain ⟨hfi, -⟩ := index_le_presented ws subs H
    (fun w hw => Subgroup.subset_closure ⟨w, hw, rfl⟩) hidx
  obtain ⟨f2, c2⟩ := card_le_of_check_trivial (ws ++ [a]) h2
  have hN : Subgroup.normalClosure {x} = ⊤ := by
    apply eq_top_of_card_le_one (us := [a]) _ _ f2 c2
    intro u hu
    simp only [List.mem_singleton] at hu
    subst hu
    exact Subgroup.subset_normalClosure rfl
  obtain ⟨f3, c3⟩ := card_le_of_check_trivial (ws ++ commWords m) h3
  have hP : commutator (PG m ws) = ⊤ := by
    apply eq_top_of_card_le_one (us := commWords m) _ _ f3 c3
    intro u hu
    simp only [commWords, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and] at hu
    obtain ⟨i, j, rfl⟩ := hu
    have : PresentedGroup.mk rels (FreeGroup.mk [(i, false), (j, false), (i, true), (j, true)]) =
        ⁅(PresentedGroup.of i : PG m ws)⁻¹, (PresentedGroup.of j)⁻¹⁆ := by
      rw [commutatorElement_def, inv_inv, inv_inv]
      rfl
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  exact finite_of_centralizer_finiteIndex x H hH hN hP

end CFSG.CosetTable
