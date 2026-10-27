module

public import CFSG.Certificates.Kernel.Co1PSound

public section

namespace CFSG.KC.Co1P

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.Native

variable {rs : List (Nat × Nat)} {ng : Nat}

theorem orbChk_eq (GK GiK : List Nat) (ng R np : Nat) (rs : List (Nat × Nat)) :
    orbChk GK GiK ng R np rs = CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (treePts (hsAct GK) ng oneK rs).2
      (treePts (hisAct GiK) ng oneK rs).2) (CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (lenL GK) ng) (invsOK GK GiK))
      (distinctK np (modL (conjL R (treePts (hsAct GK) ng oneK rs).1
        (treePts (hisAct GiK) ng oneK rs).1)))) := by
  unfold orbChk
  rcases treePts (hsAct GK) ng oneK rs with ⟨a, b⟩
  rfl

theorem orbChk_walks {GK GiK : List Nat} {R np : Nat} (h : orbChk GK GiK ng R np rs = true) :
    (treePts (hsAct GK) ng oneK rs).2 = true ∧ (treePts (hisAct GiK) ng oneK rs).2 = true := by
  rw [orbChk_eq] at h
  exact CFSG.KC.TreeK.andB_true (CFSG.KC.TreeK.andB_true h).1

section

variable {G Gi : Array Rows} {GK GiK : List Nat} {R : Nat}
  (hG : ∀ l < ng, G[l]! = unpackR 24 (getL 0 GK l))
  (hGi : ∀ l < ng, Gi[l]! = unpackR 24 (getL 0 GiK l))
  (hh : (treePts (hsAct GK) ng oneK rs).2 = true) (hhi : (treePts (hisAct GiK) ng oneK rs).2 = true)

include hh hhi in
theorem ptsL_length : (ptsL GK GiK ng R rs).length = rs.length + 1 := by
  have l1 := walk_length hh
  have l2 := walk_length hhi
  rw [ptsL, (conjL_get R _ _ (l1.trans l2.symm)).1, l1]

include hG hGi hh hhi in
theorem mkOrbT_get {k : Nat} (hk : k < rs.length + 1) :
    (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).c.pts[k]! =
      unpackR 24 ((ptsL GK GiK ng R rs)[k]?.getD 0) := by
  have l1 := walk_length hh
  have l2 := walk_length hhi
  rw [mkOrbT_pts hG hGi hh hhi hk, ptsL, (conjL_get R _ _ (l1.trans l2.symm)).2 k (by rw [l1]; exact hk)]
  rfl

include hG hGi hh hhi in
theorem mkOrbT_toList :
    (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).c.pts.toList = (ptsL GK GiK ng R rs).map (unpackR 24) := by
  refine toList_eq_map (by rw [mkOrbT_size, ptsL_length hh hhi]) fun j hj => ?_
  rw [ptsL_length hh hhi] at hj
  exact mkOrbT_get hG hGi hh hhi hj

include hG hGi hh hhi in
theorem contains_mkOrbT (X : Nat) :
    (ptSet (mkOrbT G Gi (unpackR 24 R) (treeArr rs))).contains (unpackR 24 X) =
      (ptsL GK GiK ng R rs).any fun y => eqK X y := by
  rw [ptSet, Std.HashSet.contains_ofList, mkOrbT_toList hG hGi hh hhi, contains_map_unpack]

end

theorem foldPush_succ {α : Type} (n : Nat) (step : Nat → Array α → α) :
    foldPush (n + 1) step = (foldPush n step).push (step n (foldPush n step)) := by
  unfold foldPush
  rw [List.range_succ, List.foldl_append]
  rfl

theorem foldPush_size {α : Type} (step : Nat → Array α → α) : ∀ n, (foldPush n step).size = n
  | 0 => rfl
  | n + 1 => by rw [foldPush_succ, Array.size_push, foldPush_size step n]

theorem foldPush_prefix {α : Type} [Inhabited α] (step : Nat → Array α → α) {j : Nat} :
    ∀ n, j < n → (foldPush n step)[j]! = (foldPush (j + 1) step)[j]!
  | 0, h => absurd h (Nat.not_lt_zero j)
  | n + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [foldPush_succ, getElem!_pos _ j (by rw [Array.size_push, foldPush_size]; omega),
        Array.getElem_push_lt (by rw [foldPush_size]; exact h), ← getElem!_pos,
        foldPush_prefix step n h]
    · rfl

theorem foldPush_get {α : Type} [Inhabited α] (step : Nat → Array α → α) {j n : Nat} (h : j < n) :
    (foldPush n step)[j]! = step j (foldPush j step) := by
  have hs : j < ((foldPush j step).push (step j (foldPush j step))).size := by
    rw [Array.size_push, foldPush_size]
    omega
  rw [foldPush_prefix step n h, foldPush_succ, getElem!_pos _ j hs]
  have hj : (foldPush j step).size = j := foldPush_size step j
  simp only [Array.getElem_push, hj, Nat.lt_irrefl, ↓reduceDIte]

theorem foldPush_tree {α : Type} [Inhabited α] (a0 : α) (F : Nat → α → α) (par lab : Array Nat)
    {n i : Nat} (hi : i < n) (hp : 0 < i → par[i]! < i) :
    (foldPush n fun i acc => if i == 0 then a0 else F lab[i]! acc[par[i]!]!)[i]! =
      if i = 0 then a0 else F lab[i]!
        (foldPush n fun i acc => if i == 0 then a0 else F lab[i]! acc[par[i]!]!)[par[i]!]! := by
  rw [foldPush_get _ hi]
  rcases i with _ | i
  · rfl
  · simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte]
    have hpi := hp (by omega)
    rw [foldPush_prefix _ n (by omega), foldPush_prefix _ (i + 1) hpi]

theorem contains_map_memKT {L : List Nat} {d np : Nat} (hs : sincK (sortP np (modL L)) = true)
    (ha : treeAll d (sortP np (modL L)) = true) (X : Nat) :
    (L.map (unpackR 24)).contains (unpackR 24 X) =
      memKT (Nat.mod X (Nat.shiftLeft 1 576)) (treeOf d (sortP np (modL L))) := by
  rw [contains_map_unpack, any_eqK_memKT hs ha]

end CFSG.KC.Co1P

end
