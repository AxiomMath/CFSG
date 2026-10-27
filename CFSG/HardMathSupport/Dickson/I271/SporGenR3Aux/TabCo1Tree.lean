module

public import CFSG.Sporadic.Co1Block.Tools
public import CFSG.Sporadic.Co1Block.Cent

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block

theorem image_getD_lt {G : Type*} [Group G] (gens : List G) :
    (fun l => gens.getD l 1) '' {l | l < gens.length} = {g | g ∈ gens} := by
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  · intro hg
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hg
    exact ⟨l, hl, by rw [List.getD_eq_getElem _ _ hl]⟩

theorem setOf_mem_pair {G : Type*} (a b : G) : {g | g ∈ [a, b]} = ({a, b} : Set G) := by
  ext g
  simp

theorem setOf_mem_four {G : Type*} (a b c d : G) :
    {g | g ∈ [a, b, c, d]} = ({a, b, c, d} : Set G) := by
  ext g
  simp

theorem rowsMatrix_toArray_getElem! {L : List Native.Rows} {l : ℕ} (hl : l < L.length) :
    rowsMatrix 24 L.toArray[l]! = rowsMatrix 24 (L.getD l Native.one) := by
  rw [getElem!_pos L.toArray l (by simpa using hl), List.getElem_toArray,
    List.getD_eq_getElem _ _ hl]

theorem rep_arr {Gs : List Native.Rows} {gens : List GL24} (hG : List.Forall₂ MRep Gs gens) :
    ∀ l < Gs.toArray.size, valHom ((fun l => gens.getD l 1) l) =
      rowsMatrix 24 Gs.toArray[l]! := by
  intro l hl
  have hl' : l < Gs.length := by simpa using hl
  rw [rowsMatrix_toArray_getElem! hl']
  exact (getD_rep hG MRep.one l).symm

theorem size_eq_of_rep {Gs : List Native.Rows} {gens : List GL24}
    (hG : List.Forall₂ MRep Gs gens) : Gs.toArray.size = gens.length := by
  simpa using hG.length_eq

theorem card_closure_list {Gs : List Native.Rows} {gens : List GL24}
    (hG : List.Forall₂ MRep Gs gens) {cap : ℕ}
    (h : gtOK Gs.toArray (gtBFS Gs.toArray cap) = true) :
    Nat.card ↥(Subgroup.closure {g | g ∈ gens}) = (gtBFS Gs.toArray cap).pts.size := by
  have := prodTree_card valHom valHom_injective h (fun l => gens.getD l 1) (rep_arr hG)
  rwa [size_eq_of_rep hG, image_getD_lt] at this

theorem mem_closure_list_of_contains {Gs : List Native.Rows} {gens : List GL24}
    (hG : List.Forall₂ MRep Gs gens) {cap : ℕ}
    (h : gtOK Gs.toArray (gtBFS Gs.toArray cap) = true) {r : Native.Rows}
    (hr : (gtBFS Gs.toArray cap).pts.contains r = true) {y : GL24} (hy : MRep r y) :
    y ∈ Subgroup.closure {g | g ∈ gens} := by
  rw [Array.contains_iff_mem, Array.mem_iff_getElem] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  have := mem_closure_of_prodTree valHom valHom_injective h (fun l => gens.getD l 1)
    (rep_arr hG) hi (by rw [getElem!_pos _ i hi]; exact hy.symm)
  rwa [size_eq_of_rep hG, image_getD_lt] at this

end CFSG.HardMathSupport.Dickson.I271.TabCo1
