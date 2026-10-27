module

public import CFSG.Certificates.Kernel.Fi22LH.Defs
import CFSG.Certificates.Kernel.Fi22LH.Orbit
import CFSG.Certificates.Kernel.Fi22LH.Trees
import CFSG.Certificates.Kernel.Fi22LH.RowPhi
import CFSG.Certificates.Kernel.Fi22LH.Far
import CFSG.Certificates.Kernel.Fi22LH.MuEd
import CFSG.Certificates.Kernel.Fi22LH.RootSets

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

theorem lhData_size : (lhData ()).size = 2 := rfl

theorem pair_get0 {α : Type} [Inhabited α] (a b : α) : #[a, b][0]! = a := by
  rw [getElem!_pos _ 0 (by simp)]
  rfl

theorem pair_get1 {α : Type} [Inhabited α] (a b : α) : #[a, b][1]! = b := by
  rw [getElem!_pos _ 1 (by simp)]
  rfl

theorem map_two {α β : Type} [Inhabited α] (a : Array α) (f : α → β) (ha : a.size = 2) :
    a.map f = #[f a[0]!, f a[1]!] := by
  apply Array.ext (by simp [ha])
  intro i h1 h2
  have : i < 2 := by simpa using h2
  rw [Array.getElem_map]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simp [getElem!_pos a 0 (by omega)]
  · simp [getElem!_pos a 1 (by omega)]

theorem map_pair {α β : Type} (a b : α) (f : α → β) : #[a, b].map f = #[f a, f b] := by
  simp

theorem map_range_two {β : Type} (f : Nat → β) : (Array.range 2).map f = #[f 0, f 1] := by
  apply Array.ext (by simp)
  intro i h1 h2
  have : i < 2 := by simpa using h2
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

theorem allIn_two (p : Nat → Bool) : allIn 0 2 p = (p 0 && p 1) := by
  unfold allIn
  simp [Nat.all_succ]

theorem lhCompute_eq (D : LHData) (hO : OrbOK) (h : LHChecks D) :
    lhCompute orbL (tauAll orbL) = lhDec D := by
  have hB : (lhData ()).map bitsOf = #[bitsOf (lhData ())[0]!, bitsOf (lhData ())[1]!] :=
    map_two _ _ lhData_size
  have hOrb : ((lhData ()).map bitsOf).map (fun S => lhOrbitBFS orbL.alpha orbL.beta S 20000) =
      #[orbDec D.QA, orbDec D.QB] := by
    rw [hB, ← orbit_eq0 hO h, ← orbit_eq1 hO h, map_pair]
  have hL : ((lhData ()).map fun S => S.map fun s => (tauAll orbL)[s]!) =
      #[(lhData ())[0]!.map fun s => (tauAll orbL)[s]!,
        (lhData ())[1]!.map fun s => (tauAll orbL)[s]!] := map_two _ _ lhData_size
  have hT : ((Array.range 2).map fun i => treeBFS 3510 0
      ((lhData ()).map fun S => S.map fun s => (tauAll orbL)[s]!)[i]! (Array.range 351)) =
      #[rootDec D.X D.rq0, rootDec D.Y D.rq1] := by
    rw [hL, ← rootTree_eq0 hO h, ← rootTree_eq1 hO h, map_range_two]
    simp
  have hC : (lhData ()).map (fun S => commTree (tauAll orbL) S) =
      #[commTree (tauAll orbL) (lhData ())[0]!, commTree (tauAll orbL) (lhData ())[1]!] :=
    map_two _ _ lhData_size
  unfold lhCompute lhDec
  simp only [hOrb, hT, hC, commTree_eq0 hO h, commTree_eq1 hO h]
  simp only [hB, pair_get0, pair_get1, map_pair, orbit_eq0 hO h, orbit_eq1 hO h, uIdx_eq hO h,
    rowR_eq hO h, rowInv_eq hO h, phi_eq hO h, v0_eq hO h, farTree_eq hO h,
    muW_eq hO h, muTree_eq hO h, edW_eq hO h, ed_eq hO h]

theorem lhChecks_lhDec (D : LHData) (hO : OrbOK) (h : LHChecks D) :
    lhChecks orbL (tauAll orbL) (lhDec D) = true := by
  have hB : (lhData ()).map bitsOf = #[bitsOf (lhData ())[0]!, bitsOf (lhData ())[1]!] :=
    map_two _ _ lhData_size
  have hL : ((lhData ()).map fun S => S.map fun s => (tauAll orbL)[s]!) =
      #[(lhData ())[0]!.map fun s => (tauAll orbL)[s]!,
        (lhData ())[1]!.map fun s => (tauAll orbL)[s]!] := map_two _ _ lhData_size
  unfold lhChecks lhDec
  simp only [hB, hL, pair_get0, pair_get1, map_pair, allIn_two, tauAll_size, c_dataOK h,
    c_mem0 h, c_mem1 h, c_closed0 hO h, c_closed1 hO h, c_rootTree0 hO h, c_rootTree1 hO h,
    c_commTree0 hO h, c_commTree1 hO h, c_dom0 hO h, c_dom1 hO h, c_orbit0 hO h, c_orbit1 hO h,
    c_count63 hO h, c_fail hO h, c_keyFind h, c_swap hO h, c_phi hO h, c_row hO h, c_far hO h,
    c_mu hO h, c_ed hO h]
  simp [c_star0 hO h, c_star1 hO h]

end CFSG.KS.Fi22LH
