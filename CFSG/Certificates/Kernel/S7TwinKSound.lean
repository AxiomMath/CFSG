module

public import Certificates.Data.Kernel.S7TwinK
public import Certificates.Data.S7TwinCore
public import CFSG.Certificates.Kernel.KGC31PSound

public section

namespace CFSG.KC.S7TwinK

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P CFSG.KC.BfsPin CFSG.KC.Child3
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native Certificates.S7Twin

variable {n w : Nat}

theorem spanT_tabP {R Ri Y Yi : Nat} (hR : PP n w R) (hY : PP n w Y) :
    spanT n (tabP n w R) (tabP n w Ri) (tabP n w Y) (tabP n w Yi) =
      (pspan n w R Ri Y Yi).map (tabP n w) := by
  unfold spanT pspan
  rw [compT_tabP' hR hR, compT_tabP' hR hY, compT_tabP' hY hR, idT_tabP hR.sz]
  rfl

theorem memT_tabP {L : List Nat} {X : Nat} (hL : ∀ a ∈ L, PP n w a) (hX : PP n w X) :
    memT n (L.map (tabP n w)) (tabP n w X) = pmem L X := by
  unfold memT pmem
  exact any_map_congr fun a ha => tblEq_tabP hX (hL a ha)

theorem sqOneT_tabP {A : Nat} (hA : PP n w A) : sqOneT n (tabP n w A) = psqOne n w A := by
  unfold sqOneT psqOne
  rw [compT_tabP' hA hA, idT_tabP hA.sz, tblEq_tabP (hA.pc hA) (PP.id hA.sz)]

theorem q8PairT_tabP {R Ri Y : Nat} (hR : PP n w R) (hRi : PP n w Ri) (hY : PP n w Y) :
    q8PairT n (tabP n w R) (tabP n w Ri) (tabP n w Y) = pq8Pair n w R Ri Y := by
  unfold q8PairT pq8Pair
  rw [compT_tabP' hR hR, compT_tabP' hY hY, compT_tabP' hR hY, compT_tabP' hY hRi,
    tblEq_tabP (hR.pc hR) (hY.pc hY), tblEq_tabP (hR.pc hY) (hY.pc hRi)]

theorem q8RelT_tabP {X Xi Y Yi : Nat} (hX : PP n w X) (hXi : PP n w Xi) (hY : PP n w Y)
    (hYi : PP n w Yi) :
    q8RelT n (tabP n w X) (tabP n w Xi) (tabP n w Y) (tabP n w Yi) = pq8Rel n w X Xi Y Yi := by
  simp only [q8RelT, pq8Rel]
  rw [compT_tabP' hX hX, compT_tabP' (hX.pc hX) (hX.pc hX), compT_tabP' hY hY,
    compT_tabP' hYi hX, compT_tabP' (hYi.pc hX) hY, idT_tabP hX.sz,
    tblEq_tabP ((hX.pc hX).pc (hX.pc hX)) (PP.id hX.sz), tblEq_tabP (hX.pc hX) (PP.id hX.sz),
    tblEq_tabP (hX.pc hX) (hY.pc hY), tblEq_tabP ((hYi.pc hX).pc hY) hXi]

theorem conjT_tabP' {C Ci a : Nat} (hC : PP n w C) (hCi : PP n w Ci) (ha : PP n w a) :
    conjT n (tabP n w C) (tabP n w Ci) (tabP n w a) = tabP n w (pcj n w C Ci a) := by
  unfold conjT pcj
  rw [compT_tabP' hC ha, compT_tabP' (hC.pc ha) hCi]

theorem pairWitT_tabP {sp0 sp : List Nat} {R C Ci : Nat} (hsp0 : ∀ a ∈ sp0, PP n w a)
    (hsp : ∀ a ∈ sp, PP n w a) (hR : PP n w R) (hC : PP n w C) (hCi : PP n w Ci) :
    pairWitT n (sp0.map (tabP n w)) (sp.map (tabP n w)) (tabP n w R) (tabP n w C) (tabP n w Ci) =
      ppairWit n w sp0 sp R C Ci := by
  have hJ : (sp.map (tabP n w)).map (conjT n (tabP n w C) (tabP n w Ci)) =
      (sp.map (pcj n w C Ci)).map (tabP n w) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun a ha => conjT_tabP' hC hCi (hsp a ha)
  have hJP : ∀ a ∈ sp.map (pcj n w C Ci), PP n w a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    exact PP_pcj hC hCi (hsp b hb)
  set J := sp.map (pcj n w C Ci)
  set S := sp.map (tabP n w)
  set S0 := sp0.map (tabP n w)
  have e1 : (J.map (tabP n w)).all (memT n S0) = J.all (pmem sp0) :=
    all_map_congr fun a ha => memT_tabP hsp0 (hJP a ha)
  have e2 : (J.map (tabP n w)).any (fun x => !memT n S x) = J.any (fun x => !pmem sp x) :=
    any_map_congr fun a ha => by rw [memT_tabP hsp (hJP a ha)]
  have e3 : S.any (fun a => !sqOneT n a && memT n (J.map (tabP n w)) a) =
      sp.any (fun a => !psqOne n w a && pmem J a) :=
    any_map_congr fun a ha => by rw [sqOneT_tabP (hsp a ha), memT_tabP hJP (hsp a ha)]
  have e4 : S.all (fun a => sqOneT n a || !memT n (J.map (tabP n w)) a) =
      sp.all (fun a => psqOne n w a || !pmem J a) :=
    all_map_congr fun a ha => by rw [sqOneT_tabP (hsp a ha), memT_tabP hJP (hsp a ha)]
  have e5 : S.any (fun k => (J.map (tabP n w)).any fun v => !commT n k v) =
      sp.any (fun k => J.any fun v => !Nat.beq (pc n w k v) (pc n w v k)) :=
    any_map_congr fun k hk => any_map_congr fun v hv => by rw [commT_tabP (hsp k hk) (hJP v hv)]
  simp only [pairWitT, ppairWit]
  rw [hJ, compT_tabP' hR hR, e1, e2, e3, e4, e5, memT_tabP hJP (hR.pc hR)]

theorem repPairsT_of {sp0 : List Nat} {L4 : List Table} {R : Nat} {cands : List (Nat × Nat)}
    (hsp0 : ∀ a ∈ sp0, PP n w a) (hR : PP n w R) (hc : ∀ c ∈ cands, PP n w c.1 ∧ PP n w c.2)
    (hL : ∀ T ∈ L4, ∃ Y, PP n w Y ∧ T = tabP n w Y ∧ prepY n w sp0 R cands Y = true) :
    repPairsT n (sp0.map (tabP n w)) L4 (tabP n w R)
      (cands.map fun c => (tabP n w c.1, tabP n w c.2)) = true := by
  simp only [repPairsT]
  rw [invOK_tabP hR, Bool.true_and, List.all_eq_true]
  intro T hT
  obtain ⟨Y, hY, rfl, hp⟩ := hL T hT
  rw [invOK_tabP hY, Bool.true_and, invT_tabP hR, invT_tabP hY, q8PairT_tabP hR hR.pinv hY,
    spanT_tabP hR hY]
  simp only [List.any_map, Function.comp_def]
  have hsp : ∀ a ∈ pspan n w R (pinv n w R) Y (pinv n w Y), PP n w a := by
    intro a ha
    simp only [pspan, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [PP.id hR.sz, hR.pc hR, hR, hR.pinv, hY, hY.pinv, hR.pc hY, hY.pc hR]
  have e : cands.any (fun c => pairWitT n (sp0.map (tabP n w))
      ((pspan n w R (pinv n w R) Y (pinv n w Y)).map (tabP n w)) (tabP n w R) (tabP n w c.1)
      (tabP n w c.2)) =
      cands.any (fun c => ppairWit n w sp0 (pspan n w R (pinv n w R) Y (pinv n w Y)) R c.1 c.2) :=
    any_congr' fun c hc' => pairWitT_tabP hsp0 hsp hR (hc c hc').1 (hc c hc').2
  rw [e]
  exact hp

theorem pairsOK_of {sp0 : List Nat} {L4 : List Table} {reps : List Nat}
    {cands : List (List (Nat × Nat))} (hlen : reps.length = cands.length)
    (hsp0 : ∀ a ∈ sp0, PP n w a) (hreps : ∀ r ∈ reps, PP n w r)
    (hc : ∀ l ∈ cands, ∀ c ∈ l, PP n w c.1 ∧ PP n w c.2)
    (hL : ∀ T ∈ L4, ∃ Y, PP n w Y ∧ T = tabP n w Y ∧ pairsY n w sp0 reps cands Y = true) :
    pairsOK n (sp0.map (tabP n w)) L4 (reps.map (tabP n w))
      (cands.map (List.map fun c => (tabP n w c.1, tabP n w c.2))) = true := by
  unfold pairsOK
  rw [List.length_map, List.length_map, hlen, beq_self_eq_true, Bool.true_and, List.zip_map,
    List.all_map, List.all_eq_true]
  intro p hp
  have hm := List.of_mem_zip hp
  exact repPairsT_of hsp0 (hreps _ hm.1) (hc _ hm.2) fun T hT => by
    obtain ⟨Y, hY, rfl, h⟩ := hL T hT
    exact ⟨Y, hY, rfl, List.all_eq_true.1 h p hp⟩

end CFSG.KC.S7TwinK

end
