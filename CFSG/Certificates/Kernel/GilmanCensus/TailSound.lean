module

public import CFSG.Certificates.Kernel.GilmanCensus.LoopsSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

theorem adjK_congr (g g' : Nat → Nat → Int) (N : Nat)
    (h : ∀ i j, i < N → j < N → g i j = g' i j) : adjK g N = adjK g' N := by
  unfold adjK
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  apply foldl_congr_mem
  intro j hj m
  rw [List.mem_range] at hj
  rw [h i j hi hj]

theorem fhOkK_congr (F H : List (List Nat)) (g g' : Nat → Nat → Int) (N : Nat) (ok : Bool)
    (h : ∀ i j, i < N → j < N → g i j = g' i j) : fhOkK F H g N ok = fhOkK F H g' N ok := by
  unfold fhOkK
  apply foldl_congr_mem
  intro i hi ok
  rw [List.mem_range'] at hi
  apply foldl_congr_mem
  intro j hj ok
  rw [List.mem_range'] at hj
  rw [h i j (by omega) (by omega), h j j (by omega) (by omega)]

theorem reflK_congr (R : List (List Int)) (g g' : Nat → Nat → Int) (n N : Nat) (ok : Bool)
    (h : ∀ i j, i < N → j < N → g i j = g' i j) : reflK R g n N ok = reflK R g' n N ok := by
  unfold reflK reflRowK
  apply foldl_congr_mem
  intro i hi st
  rw [List.mem_range'] at hi
  have e : (List.range' 0 N).foldl (reflStepK R g n i) (st.1, []) =
      (List.range' 0 N).foldl (reflStepK R g' n i) (st.1, []) := by
    apply foldl_congr_mem
    intro j hj st
    rw [List.mem_range'] at hj
    unfold reflStepK
    rw [h j i (by omega) (by omega), h i i (by omega) (by omega)]
  rw [e]

theorem toI_length (R : List (List Nat)) : (toI R).length = R.length := by
  simp [toI]

theorem size_of_LLI {R : Array IVec} {l : List (List Nat)} (h : LLI R = toI l) : R.size = l.length := by
  rw [← length_LLI, h, toI_length]

theorem size_of_LL {F : Array (Array Nat)} {l : List (List Nat)} (h : LL F = l) : F.size = l.length := by
  rw [← length_LL, h]

theorem rows_size {F : Array (Array Nat)} {l : List (List Nat)} {d : Nat} (h : LL F = l)
    (hl : ∀ r ∈ l, r.length = d) : ∀ r ∈ F.toList, r.size = d := by
  intro r hr
  rw [← Array.length_toList]
  apply hl
  rw [← h, LL]
  exact List.mem_map_of_mem hr

theorem map_getElem! {α β : Type} [Inhabited α] [Inhabited β] (R : Array α) (f : α → β) (i : Nat)
    (hi : i < R.size) : (R.map f)[i]! = f R[i]! := by
  rw [getElem!_pos (R.map f) i (by simpa using hi), getElem!_pos R i hi, Array.getElem_map]

theorem all_any_LL (F : Array (Array Nat)) :
    (F.all fun f => f.any (· != 0)) = (LL F).all fun f => f.any (· != 0) := by
  rw [← Array.all_toList, LL, List.all_map]
  congr 1
  funext f
  simp [Function.comp_def, ← Array.any_toList]

theorem tailS_eq (mode n : Nat) (AR : Array IVec) (rho : Array Nat) (B : Array (Array Int))
    (R : Array IVec) (absidx F H : Array (Array Nat)) (d : Nat) (dk : DK)
    (hmode : mode = dk.mode) (hd : d = dk.d)
    (hR : LLI R = toI dk.R) (hRnd : (toI dk.R).Nodup) (hRlen : ∀ r ∈ dk.R, r.length = n)
    (hRN : dk.R.length = dk.N) (hNlt : dk.N < 128)
    (hAR : LLI AR = toI dk.AR) (hARnd : (toI dk.AR).Nodup) (hARlen : ∀ r ∈ dk.AR, r.length = n)
    (hARlt : dk.AR.length < 128)
    (habs : LL absidx = dk.absidx) (hrho : rho.toList = dk.rho)
    (hF : LL F = dk.F) (hFlen : ∀ r ∈ dk.F, r.length = dk.d) (hFN : dk.F.length = dk.N)
    (hH : LL H = dk.H) (hHlen : ∀ r ∈ dk.H, r.length = dk.d) (hHN : dk.H.length = dk.N)
    (hFnz : (dk.F.all fun f => f.any (· != 0)) = true)
    (hhs : (dedupK (scaledK dk.H)).length = 2 * dk.N)
    (hG : ∀ i j, i < dk.N → j < dk.N →
      gramK (LLI B) ((toI dk.R).getD i []) ((toI dk.R).getD j []) = gI dk i j)
    (hfh : fhOkK dk.F dk.H (gI dk) dk.N true = true)
    (hadj : adjK (gI dk) dk.N = dk.adj)
    (haadj : adjK (fun i j => gramK (LLI B) ((toI dk.AR).getD i []) ((toI dk.AR).getD j []))
      dk.AR.length = dk.aadj)
    (hrefl : (reflK (toI dk.R) (gI dk) n dk.N true).1 = true)
    (hlanes : ∀ i < dk.N, ∀ j < 128, (dk.reflP.getD i 0 >>> (7 * j)) % 128 =
      (((reflK (toI dk.R) (gI dk) n dk.N true).2.getD i []).getD j 0))
    (hlines : linesK dk.d = dk.lines) :
    ∃ dt, tailS mode n AR rho B true R absidx F H d = some dt ∧ Rel dt dk := by
  have hRs : R.size = dk.N := by rw [size_of_LLI hR, hRN]
  have hARs : AR.size = dk.AR.length := size_of_LLI hAR
  have hGe : ∀ i j, i < dk.N → j < dk.N →
      (R.map fun r => R.map fun s => gramB B r s)[i]![j]! = gI dk i j := by
    intro i j hi hj
    rw [map_getElem! _ _ i (by omega), map_getElem! _ _ j (by omega), gramB_eq, getRowI, getRowI,
      hR, hG i j hi hj]
  unfold tailS
  dsimp only
  generalize hGd : (R.map fun r => R.map fun s => gramB B r s) = G at hGe ⊢
  have c1 : (F.all fun f => f.any (· != 0)) = true := by rw [all_any_LL, hF, hFnz]
  have c2 : (hsLoop H).size = 2 * R.size := by
    rw [hsLoop_eq, (hset_size _).2, scaled_map, hH, hhs, hRs]
  have c3 : fhOkLoop F H G R.size true = true := by
    rw [fhOkLoop_eq F H G (fun i j => G[i]![j]!) (fun _ _ => rfl), hF, hH, hRs,
      fhOkK_congr _ _ _ (gI dk) _ _ hGe, hfh]
  have hix : ∀ v : IVec, (ixLoop R R.size)[v]? = idxI v.toList (LLI R) 0 :=
    ixLoop_eq R (by rw [hR]; exact hRnd)
  have haix : ∀ v : IVec, (ixLoop AR AR.size)[v]? = idxI v.toList (LLI AR) 0 :=
    ixLoop_eq AR (by rw [hAR]; exact hARnd)
  obtain ⟨r1, r2⟩ := refl_eq n R G (ixLoop R R.size) (fun i j => G[i]![j]!) hix (fun _ _ => rfl)
    R.size true
  have e1 : reflK (LLI R) (fun i j => G[i]![j]!) n R.size true =
      reflK (toI dk.R) (gI dk) n dk.N true := by
    rw [hR, hRs]
    exact reflK_congr _ _ _ _ _ _ hGe
  rw [e1] at r1 r2
  rw [← reflLoop_eq] at r1 r2
  have c4 : (reflLoop n R.size R G (ixLoop R R.size) true).1 = true := by rw [r1, hrefl]
  simp only [c1, c2, c3, c4, Bool.not_true, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    Id.run]
  refine ⟨_, rfl, ?_⟩
  exact
    { mode := hmode
      N := hRs
      Nlt := hNlt
      d := hd
      R := hR
      Rlen := hRlen
      RN := hRN
      ix := hix
      AR := hAR
      ARlen := hARlen
      ARlt := hARlt
      aix := haix
      absidx := habs
      rho := hrho
      F := hF
      Fsz := rows_size hF (fun r hr => by rw [hd]; exact hFlen r hr)
      FN := hFN
      H := hH
      Hsz := rows_size hH (fun r hr => by rw [hd]; exact hHlen r hr)
      HN := hHN
      G := hGe
      adj := (adj_eq (fun i j => G[i]![j]!) R.size).trans (by
        rw [hRs]
        exact (adjK_congr _ _ _ hGe).trans hadj)
      aadj := (adj_eq (fun i j => gramB B AR[i]! AR[j]!) AR.size).trans (by
        rw [hARs]
        refine (adjK_congr _ _ _ (fun i j _ _ => ?_)).trans haadj
        rw [gramB_eq, getRowI, getRowI, hAR])
      refl := fun i hi j hj => by
        rw [getElem!_eq_getD_toList, getRow, r2]
        exact hlanes i hi j hj
      lines := (lines_eq d).trans (by rw [hd]; exact hlines)
      full := by rw [hRs]; rfl }

end Certificates.GilmanCensusK

end
