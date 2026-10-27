module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.Blueprint.NativeSporadic
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23BaseInputs
public import Certificates.Certificate4063

public section

namespace CFSG.QuasithinUnique.A5.G3.M23

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

theorem closure_natGens :
    Subgroup.closure {g | g ∈ natGens} = CFSG.Blueprint.NativeSporadic.M23 := by
  unfold CFSG.Blueprint.NativeSporadic.M23
  congr 1
  ext g
  simp [natGens, natA, natB]

theorem evalW_mem_M23 (w : List ℕ) : evalW natGens w ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  rw [← closure_natGens]
  exact evalW_mem_closure natGens w

theorem gens_words :
    tGens = [evalW natGens [0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0],
   evalW natGens [0,1,1,0,1,0,1,1,0,1,1,0,1,0,1,1,0],
   evalW natGens [0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,0,1,0],
   evalW natGens [1,1,1,0,1,0,1,1,1,0,1,0,1,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,0]] ∧ mGens1 = [evalW natGens [1,1,0,1,0,1,0,1,1,1,0,1],
   evalW natGens [0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,0,1]] ∧ mGens2 = [evalW natGens [1,1,1,0,1,0,1,1,1,0,1],
   evalW natGens [0,1,0,1,0,1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1]] :=
  Certificates.certificate4063

theorem tGens_mem : ∀ g ∈ tGens, g ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  intro g hg
  rw [gens_words.1] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> exact evalW_mem_M23 _

theorem mGens1_mem : ∀ g ∈ mGens1, g ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  intro g hg
  rw [gens_words.2.1] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> exact evalW_mem_M23 _

theorem mGens2_mem : ∀ g ∈ mGens2, g ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  intro g hg
  rw [gens_words.2.2] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> exact evalW_mem_M23 _

end CFSG.QuasithinUnique.A5.G3.M23
