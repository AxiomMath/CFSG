module

public import Certificates.Data.Kernel.Fi22.MarkedK
public import CFSG.Certificates.Kernel.Fi22LH.Rows
public import CFSG.Sporadic.Fi22.LH.Tables
public import CFSG.OddTranspositions.PartFour.ThirteenListThreeFischerPoints

public section

namespace CFSG.KS.Fi22Marked

open CFSG.OddTranspositions.FischerMarked CFSG.KS.Fi22LH CFSG.Sporadic.Fi22
  CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.F3.Native CFSG.KS.TW
  CFSG.Fischer.Classification

theorem conj_closure {G : Type*} [Group G] {n m : ℕ} (F : Fin n → G) (σ : Fin n → Fin n → Fin n)
    (hσ : ∀ c i b, σ (σ c i) b = σ c (σ i (σ c b))) (r : Fin n → ℕ)
    (hbase : ∀ i, r i < m → ∀ b, F (σ i b) = F i * F b * F i)
    (hstep : ∀ i, m ≤ r i → ∃ c i', r c < r i ∧ r i' < r i ∧ σ c i' = i) :
    ∀ i b, F (σ i b) = F i * F b * F i := by
  suffices H : ∀ k i, r i = k → ∀ b, F (σ i b) = F i * F b * F i from fun i => H _ i rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hk
    rcases lt_or_ge (r i) m with hm | hm
    · exact hbase i hm
    · obtain ⟨c, i', hc, hi', rfl⟩ := hstep i hm
      have Pc := ih (r c) (by omega) c rfl
      have Pi := ih (r i') (by omega) i' rfl
      intro b
      simp only [hσ, Pc, Pi, mul_assoc]

theorem sigma_law {G X : Type*} [Group G] (g : X → G) (hg : Function.Injective g)
    (σ : X → X → X) (h : ∀ x y, g (σ x y) = g x * g y * g x) (c i b : X) :
    σ (σ c i) b = σ c (σ i (σ c b)) := by
  apply hg
  simp only [h, mul_assoc]

@[expose] def sigF (a b : Fin 351) : Fin 351 := pointIndex (reflectPoint (point a) (point b))

theorem sigF_law (c i b : Fin 351) : sigF (sigF c i) b = sigF c (sigF i (sigF c b)) :=
  sigma_law (fun a => (reflPoint a : R3 (diagF3 7 1)))
    (Subtype.val_injective.comp reflPoint_bijective.1) sigF (fun x y => reflPoint_reflect x y)
    c i b

theorem refl_coord (c d : ℕ) (k : Fin 7) :
    reflectPoint (vectorOfCode c) (vectorOfCode d) k = ((rN c d k.val : ℕ) : ZMod 3) := by
  simp only [rN, tN, reflectPoint, dot, vectorOfCode, dg, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  simp

theorem rN_mod (c d k : ℕ) : rN c d k % 3 = rN c d k := Nat.mod_mod _ _

theorem vectorCode_refl (c d : ℕ) :
    vectorCode (reflectPoint (vectorOfCode c) (vectorOfCode d)) = reflN c d := by
  simp [vectorCode, reflN, refl_coord, ZMod.val_natCast, rN_mod]

theorem reflN_lt (c d : ℕ) : reflN c d < 2187 := by
  have h : ∀ k, rN c d k < 3 := fun k => Nat.mod_lt _ (by decide)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  unfold reflN
  omega

theorem getElem!_of_map_range {f : ℕ → ℕ} {A : Array ℕ} {n : ℕ}
    (h : (List.range n).map f = A.toList) {i : ℕ} (hi : i < n) : A[i]! = f i := by
  have hl : i < ((List.range n).map f).length := by simpa using hi
  have e := List.getElem_of_eq h hl
  rw [List.getElem_map, List.getElem_range, Array.getElem_toList] at e
  rw [getElem!_pos A i (by rw [← Array.length_toList, ← h]; exact hl), ← e]

theorem sigN_eq {P : ℕ} (hP : pointsOK P) (a b : Fin 351) :
    sigN P a.val b.val = (sigF a b).val := by
  change _ = pointIndices[vectorCode (reflectPoint (vectorOfCode pointCodes[a.val]!)
    (vectorOfCode pointCodes[b.val]!))]! % 351
  rw [vectorCode_refl, getElem!_of_map_range hP.1 a.2, getElem!_of_map_range hP.1 b.2,
    getElem!_of_map_range hP.2 (reflN_lt _ _)]
  rfl


theorem marked_conj (D : LHData) (hO : OrbOK) (h : LHChecks D) (horb : orbitData () = orbL)
    {T P : Nat} (hP : pointsOK P) (hr : rowsOK D.R D.lb0 T P) (ht : treeOK T P) (i j : Fin 351) :
    ap (cTab (orbitData ()) (genTables (orbitData ()) (-2)) (((lhData ())[0]!)[i.val]!))
      (((lhData ())[0]!)[j.val]!) =
      ((lhData ())[0]!)[(pointIndex (reflectPoint (point i) (point j))).val]! := by
  have hS := h.2.2.2.2.1
  have hlt : ∀ a : Fin 351, ((lhData ())[0]!)[a.val]! < 3510 := fun a => by
    rw [← hS a.val a.2]
    exact hr.1 a.val a.2
  have hap : ∀ c x, c < 3510 → x < 3510 →
      ap (cTab (orbitData ()) (genTables (orbitData ()) (-2)) c) x = ent (D.R c) x ∧
        ent (D.R c) x < 3510 := fun c x hc hx => by
    rw [horb]
    exact (cTab_TR hO h c hc).2 x hx
  have hgrp : ∀ c x, c < 3510 → x < 3510 → conjPt c * conjPt x * conjPt c =
      conjPt (ap (cTab (orbitData ()) (genTables (orbitData ()) (-2)) c) x) := fun c x hc hx => by
    rw [conjPt_mul_conjPt hc hx, tT_get hc]
    rfl
  let F : Fin 351 → J := fun a => conjPt (((lhData ())[0]!)[a.val]!)
  have key : ∀ a b, F (sigF a b) = F a * F b * F a := by
    refine conj_closure F sigF sigF_law (fun a => tf T a.val 18) (m := 7) ?_ ?_
    · intro a ha b
      have e := hr.2 a.val a.2 ha b.val b.2
      rw [hS a.val a.2, hS b.val b.2, sigN_eq hP, hS _ (sigF a b).2] at e
      change conjPt _ = conjPt _ * conjPt _ * conjPt _
      rw [hgrp _ _ (hlt a) (hlt b), (hap _ _ (hlt a) (hlt b)).1, e]
    · intro a ha
      obtain ⟨h1, h2, h3, h4, h5⟩ := ht a.val a.2 ha
      refine ⟨⟨_, h1⟩, ⟨_, h2⟩, h3, h4, Fin.ext ?_⟩
      rw [← sigN_eq hP]
      exact h5
  have e := key i j
  change conjPt _ = conjPt _ * conjPt _ * conjPt _ at e
  rw [hgrp _ _ (hlt i) (hlt j)] at e
  obtain ⟨hb1, hb2⟩ := hap _ _ (hlt i) (hlt j)
  rw [← hb1] at hb2
  exact conjPt_inj (by rw [orb_size]; exact hb2) (by rw [orb_size]; exact hlt _) e.symm

end CFSG.KS.Fi22Marked
