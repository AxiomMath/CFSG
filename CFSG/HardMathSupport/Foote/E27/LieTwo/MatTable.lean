module

public import CFSG.HardMathSupport.Foote.E27.TableSylow
public import CFSG.HardMathSupport.Foote.E27.TableMat

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix CFSG.Sporadic.He.Native

abbrev M2 (d : ℕ) : Type := Matrix (Fin d) (Fin d) (ZMod 2)

abbrev AM : Type := Array (Array ℕ)

structure RawTab where
  elts : Array AM
  par : Array (ℕ × ℕ)
  L : Array (Array ℕ)

@[expose] def buildTab (d : ℕ) (gens : Array AM) (fuel : ℕ) : RawTab :=
  let m := gens.size
  let init : RawTab := ⟨#[idM d], #[(0, 0)], Array.replicate m #[]⟩
  let step : RawTab → ℕ → RawTab := fun st i =>
    (List.range m).foldl (fun (st : RawTab) j =>
      let p := mulM 2 d gens[j]! st.elts[i]!
      match st.elts.findIdx? (matEqB 2 d p) with
      | some k => { st with L := st.L.modify j (·.push k) }
      | none => ⟨st.elts.push p, st.par.push (i, j), st.L.modify j (·.push st.elts.size)⟩) st
  (List.range fuel).foldl (fun st i => if i < st.elts.size then step st i else st) init

@[expose] def tabOK (d : ℕ) (gens : Array AM) (T : RawTab) : Bool :=
  let n := T.elts.size
  (T.par.size == n) && matEqB 2 d T.elts[0]! (idM d) &&
  (List.range n).all (fun i => (i == 0) ||
    (decide ((T.par[i]!).1 < i) && decide ((T.par[i]!).2 < gens.size) &&
      matEqB 2 d T.elts[i]! (mulM 2 d gens[(T.par[i]!).2]! T.elts[(T.par[i]!).1]!))) &&
  (List.range gens.size).all (fun j => (List.range n).all fun i =>
    decide ((T.L[j]!)[i]! < n) &&
      matEqB 2 d (mulM 2 d gens[j]! T.elts[i]!) T.elts[(T.L[j]!)[i]!]!) &&
  (List.range n).all (fun i => (List.range i).all fun k => !(matEqB 2 d T.elts[i]! T.elts[k]!))

section Spec

variable {d : ℕ} {G : Type*} [Group G]

theorem tabData_of_check (mat : G →* M2 d) (hinj : Function.Injective mat)
    (gens : Array AM) (T : RawTab) (g : ℕ → G)
    (hg : ∀ j < gens.size, mat (g j) = toMat 2 d gens[j]!) (hc : tabOK d gens T = true) :
    TabData g T.par T.L T.elts.size gens.size ∧
      ∀ i < T.elts.size, mat (tabElt g T.par i) = toMat 2 d T.elts[i]! := by
  unfold tabOK at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨hpar, h0⟩, htree⟩, hleft⟩, hdist⟩ := hc
  have heq : ∀ i < T.elts.size, mat (tabElt g T.par i) = toMat 2 d T.elts[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [tabElt_zero, map_one, matEqB_true h0, toMat_idM]
      · rcases htree i hi with h1 | ⟨⟨hp, hj⟩, hel⟩
        · exact absurd h1 hi0
        · rw [tabElt_succ g T.par hp, map_mul, hg _ hj, ih _ hp (by omega), matEqB_true hel,
            toMat_mulM]
  refine ⟨⟨fun i hi hin => ?_, fun j hj i hi => ?_, fun i hi k hk hik => ?_⟩, heq⟩
  · rcases htree i hin with h1 | ⟨⟨hp, hj⟩, -⟩
    · omega
    · exact ⟨hp, hj⟩
  · obtain ⟨hlt, hmat⟩ := hleft j hj i hi
    refine ⟨hlt, hinj ?_⟩
    rw [map_mul, hg j hj, heq i hi, heq _ hlt]
    have := matEqB_true hmat
    rw [toMat_mulM] at this
    exact this
  · have key : ∀ i < T.elts.size, ∀ k < i, tabElt g T.par i ≠ tabElt g T.par k := by
      intro i hi k hk heq'
      have h1 := matEqB_false (hdist i hi k hk)
      apply h1
      rw [← heq i hi, ← heq k (by omega), heq']
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key k hk i hlt hik.symm
    · exact key i hi k hlt hik

noncomputable def genOf (mat : G →* M2 d) (gens : Array AM)
    (hex : ∀ j < gens.size, ∃ x : G, mat x = toMat 2 d gens[j]!) (j : ℕ) : G :=
  if h : j < gens.size then (hex j h).choose else 1

theorem mat_genOf (mat : G →* M2 d) (gens : Array AM)
    (hex : ∀ j < gens.size, ∃ x : G, mat x = toMat 2 d gens[j]!) {j : ℕ} (hj : j < gens.size) :
    mat (genOf mat gens hex j) = toMat 2 d gens[j]! := by
  unfold genOf
  rw [dif_pos hj]
  exact (hex j hj).choose_spec

end Spec

end CFSG.HardMathSupport.Foote.E27
