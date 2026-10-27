module

public import CFSG.GH74.QTGen4.Recog.G23.Words
public import Certificates.Data.G23RecogGlueInputs

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.CosetTable

theorem lift_renumber {m : ℕ} {X : Type*} [Group X] (S : List (Fin m)) (e : Fin m → X)
    (w : List (Fin m × Bool)) (w' : List (Fin S.length × Bool)) (h : renumber S w = some w') :
    FreeGroup.lift (fun i => e (S.get i)) (FreeGroup.mk w') = FreeGroup.lift e (FreeGroup.mk w) := by
  rw [FreeGroup.lift_mk, FreeGroup.lift_mk, ← map_renumber S w w' h]
  simp [List.map_map, Function.comp_def]

theorem sat_restrict {X : Type*} [Group X] (e : Fin 6 → X) (he : SatisfiesWords g23WordsH e) :
    ∀ r ∈ restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) g23WordsH,
      FreeGroup.lift (fun i => e ((subsetOf 6 [0, 1, 2, 3, 4]).get i)) (FreeGroup.mk r) = 1 := by
  intro r hr
  obtain ⟨w, hw, hwr⟩ := List.mem_filterMap.mp hr
  rw [lift_renumber _ e w r hwr]
  exact he w hw

theorem subsetOf_get (j : Fin (subsetOf 6 [0, 1, 2, 3, 4]).length) :
    (subsetOf 6 [0, 1, 2, 3, 4]).get j = (Fin.cast len5 j).castSucc := by
  have key : ∀ k : Fin 5, (subsetOf 6 [0, 1, 2, 3, 4]).get (Fin.cast len5.symm k) = k.castSucc := by
    decide
  have := key (Fin.cast len5 j)
  simpa using this

theorem sat_H5 {X : Type*} [Group X] (e : Fin 6 → X) (he : SatisfiesWords g23WordsH e) :
    ∀ r ∈ g23H5, FreeGroup.lift (fun i : Fin (subsetOf 6 [0, 1, 2, 3, 4]).length =>
      e (Fin.cast len5 i).castSucc) (FreeGroup.mk r) = 1 := by
  intro r hr
  have h := sat_restrict e he r hr
  have hfun : (fun i : Fin (subsetOf 6 [0, 1, 2, 3, 4]).length =>
      e (Fin.cast len5 i).castSucc) = (fun i => e ((subsetOf 6 [0, 1, 2, 3, 4]).get i)) := by
    funext i
    rw [subsetOf_get]
  rw [hfun]
  exact h

end CFSG.GH74.QTGen4.Recog.G23
