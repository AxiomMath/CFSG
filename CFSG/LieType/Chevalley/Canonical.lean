module

public import CFSG.LieType.Chevalley.Braid
public import CFSG.LieType.RootSystem.Basic
public import TauCeti.GroupTheory.Coxeter.Matsumoto
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem CoxeterSystem

variable {τ : Tag}

theorem prod_braidWord_weylElt (hA : TauCeti.IsFiniteType τ.cartan) (R : Type*) [CommRing R]
    (i j : Fin τ.rank) :
    ((braidWord (coxeterMatrix hA) i j).map fun k => weylElt τ R k 1).prod =
      ((braidWord (coxeterMatrix hA) j i).map fun k => weylElt τ R k 1).prod := by
  simp only [braidWord, coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  rw [mul_comm (τ.cartan j i)]
  exact prod_alternatingWord_weylElt τ R i j

variable {hA : TauCeti.IsFiniteType τ.cartan} {W : Type*} [Group W]
  (cs : CoxeterSystem (coxeterMatrix hA) W) (R : Type*) [CommRing R]

noncomputable def canonicalRep (w : W) : (Module.End R (RootModule τ R))ˣ :=
  ((cs.exists_isReduced w).choose.map fun i => weylElt τ R i 1).prod

variable {cs R}

theorem canonicalRep_wordProd {ω : List (Fin τ.rank)} (hω : cs.IsReduced ω) :
    canonicalRep cs R (cs.wordProd ω) = (ω.map fun i => weylElt τ R i 1).prod := by
  have h := cs.exists_isReduced (cs.wordProd ω)
  exact TauCeti.matsumoto cs _ (prod_braidWord_weylElt hA R) h.choose_spec.1 hω
    h.choose_spec.2.symm

variable (cs R) in
theorem canonicalRep_one : canonicalRep cs R 1 = 1 := by
  have h := canonicalRep_wordProd (R := R) (cs := cs) (ω := []) (by simp [CoxeterSystem.IsReduced])
  rwa [wordProd_nil, List.map_nil, List.prod_nil] at h

variable (cs R) in
theorem canonicalRep_simple (i : Fin τ.rank) :
    canonicalRep cs R (cs.simple i) = weylElt τ R i 1 := by
  have h := canonicalRep_wordProd (R := R) (cs := cs) (ω := [i])
    (by rw [CoxeterSystem.IsReduced, wordProd_singleton, length_simple, List.length_singleton])
  rwa [wordProd_singleton, List.map_singleton, List.prod_singleton] at h

theorem weylElt_mul_canonicalRep_of_length_eq {i : Fin τ.rank} {w : W}
    (h : cs.length (cs.simple i * w) = cs.length w + 1) :
    weylElt τ R i 1 * canonicalRep cs R w = canonicalRep cs R (cs.simple i * w) := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hred : cs.IsReduced (i :: ω) := by
    rw [CoxeterSystem.IsReduced, wordProd_cons, h, hω.eq, List.length_cons]
  rw [← wordProd_cons, canonicalRep_wordProd hred, canonicalRep_wordProd hω, List.map_cons,
    List.prod_cons]

theorem weylElt_mul_canonicalRep_of_length_add_one_eq {i : Fin τ.rank} {w : W}
    (h : cs.length (cs.simple i * w) + 1 = cs.length w) :
    weylElt τ R i 1 * canonicalRep cs R w =
      torusElt τ R i (-1) * canonicalRep cs R (cs.simple i * w) := by
  have hw : cs.simple i * (cs.simple i * w) = w := cs.simple_mul_simple_cancel_left i
  have h' := weylElt_mul_canonicalRep_of_length_eq (R := R) (i := i) (w := cs.simple i * w)
    (by rw [hw, h])
  rw [hw] at h'
  rw [← h', ← mul_assoc, weylElt_one_mul_self]

theorem weylElt_mul_canonicalRep (i : Fin τ.rank) (w : W) :
    weylElt τ R i 1 * canonicalRep cs R w =
      if cs.length (cs.simple i * w) = cs.length w + 1 then canonicalRep cs R (cs.simple i * w)
      else torusElt τ R i (-1) * canonicalRep cs R (cs.simple i * w) := by
  split_ifs with h
  · exact weylElt_mul_canonicalRep_of_length_eq h
  · exact weylElt_mul_canonicalRep_of_length_add_one_eq ((cs.length_simple_mul w i).resolve_left h)

variable (cs R) in
theorem canonicalRep_mem_closure (w : W) :
    canonicalRep cs R w ∈ Subgroup.closure (Set.range fun i : Fin τ.rank => weylElt τ R i 1) := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨i, rfl⟩

variable (cs) in
theorem canonicalRep_mem_adjointGroup (K : Type*) [Field K] (w : W) :
    canonicalRep cs K w ∈ adjointGroup τ K := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact weylElt_mem_adjointGroup i 1

end CFSG.LieType.Chevalley
