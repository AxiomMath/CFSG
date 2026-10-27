module

public import Certificates.Data.Kernel.OpsF2KCo1Gen
public import Certificates.Data.CFSGNative.SectionRank.F2
import all CFSG.Certificates.Kernel.OpsF2KSound
import all CFSG.Certificates.Kernel.OpsF2KSqSound
import all CFSG.Certificates.Kernel.LocalCompCubSound
import all CFSG.Certificates.Kernel.Co1F2Sound

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.SectionRank.Native
open CFSG.KC.Co1F2 (unpackR)

private theorem anyK_congr {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.any p = l.any q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.any_cons, List.any_cons, h a (by simp),
      anyK_congr fun b hb => h b (List.mem_cons_of_mem a hb)]

private theorem canon_beq_eq {d X Y : Nat} (hX : CFSG.KC.Co1F2.Canon d X)
    (hY : CFSG.KC.Co1F2.Canon d Y) :
    Nat.beq X Y = (ops2 d).eq (unpackR d X) (unpackR d Y) := by
  change Nat.beq X Y = (unpackR d X == unpackR d Y)
  by_cases h : X = Y
  · rw [h, Nat.beq_refl, beq_self_eq_true]
  · have hne : unpackR d X ≠ unpackR d Y := fun e => h (CFSG.KC.Co1F2.canon_inj hX hY (by
      rw [← CFSG.KC.Co1F2.unpackR_eq, ← CFSG.KC.Co1F2.unpackR_eq, e]))
    rw [CFSG.KC.LocalComp.Cub.nat_beq_false.mpr h, beq_eq_false_iff_ne.mpr hne]

private theorem dedupK_map {d : Nat} : ∀ (L acc : List Nat),
    (∀ x ∈ L, CFSG.KC.Co1F2.Canon d x) → (∀ x ∈ acc, CFSG.KC.Co1F2.Canon d x) →
    (L.map (unpackR d)).foldl (fun acc y => if acc.any ((ops2 d).eq y) then acc else acc ++ [y])
        (acc.map (unpackR d)) =
      (L.foldl (fun acc y => if acc.any (Nat.beq y) then acc else acc ++ [y]) acc).map
        (unpackR d) ∧
    ∀ x ∈ L.foldl (fun acc y => if acc.any (Nat.beq y) then acc else acc ++ [y]) acc,
      CFSG.KC.Co1F2.Canon d x
  | [], _, _, hacc => ⟨rfl, hacc⟩
  | y :: L, acc, hL, hacc => by
    have hy : CFSG.KC.Co1F2.Canon d y := hL y (by simp)
    have hL' : ∀ x ∈ L, CFSG.KC.Co1F2.Canon d x := fun x hx => hL x (List.mem_cons_of_mem y hx)
    have hany : (acc.map (unpackR d)).any ((ops2 d).eq (unpackR d y)) = acc.any (Nat.beq y) := by
      rw [List.any_map]
      exact anyK_congr fun a ha => (canon_beq_eq hy (hacc a ha)).symm
    simp only [List.map_cons, List.foldl_cons]
    rw [hany]
    by_cases hb : acc.any (Nat.beq y) = true
    · rw [if_pos hb, if_pos hb]
      exact dedupK_map L acc hL' hacc
    · rw [if_neg hb, if_neg hb]
      have hacc' : ∀ x ∈ acc ++ [y], CFSG.KC.Co1F2.Canon d x := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hacc x hx
        · rw [List.mem_singleton.1 hx]
          exact hy
      have e : acc.map (unpackR d) ++ [unpackR d y] = (acc ++ [y]).map (unpackR d) := by
        rw [List.map_append, List.map_singleton]
      rw [e]
      exact dedupK_map L (acc ++ [y]) hL' hacc'

private theorem flatMapK_map {d : Nat} (gs : List Nat) : ∀ xs : List Nat,
    ((xs.map (unpackR d)).flatMap fun x => (gs.map (unpackR d)).map ((ops2 d).mul x)) =
      (xs.flatMap fun x => gs.map (mulF d x)).map (unpackR d)
  | [] => rfl
  | x :: xs => by
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append, flatMapK_map gs xs,
      List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun g _ => ?_
    simp only [Function.comp_apply]
    exact (unpackR_mulF d x g).symm

private theorem closStepK_map {d : Nat} {gs xs : List Nat}
    (hxs : ∀ x ∈ xs, CFSG.KC.Co1F2.Canon d x) :
    (ops2 d).co1GenStep (gs.map (unpackR d)) (xs.map (unpackR d)) =
        (closStepK d gs xs).map (unpackR d) ∧
      ∀ x ∈ closStepK d gs xs, CFSG.KC.Co1F2.Canon d x := by
  have hcan : ∀ y ∈ xs.flatMap (fun x => gs.map (mulF d x)), CFSG.KC.Co1F2.Canon d y := by
    intro y hy
    obtain ⟨x, -, hy⟩ := List.mem_flatMap.1 hy
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hy
    exact CFSG.KC.Co1F2.mulF_canon d x g
  unfold Ops.co1GenStep closStepK
  rw [flatMapK_map]
  exact dedupK_map _ _ hcan hxs

private theorem closAuxK_map {d : Nat} (gs : List Nat) : ∀ (n : Nat) (xs : List Nat),
    (∀ x ∈ xs, CFSG.KC.Co1F2.Canon d x) →
    (ops2 d).co1GenAux (gs.map (unpackR d)) n (xs.map (unpackR d)) =
      (closAuxK d gs n xs).map (unpackR d)
  | 0, _, _ => rfl
  | n + 1, xs, hxs => by
    obtain ⟨hstep, hcan⟩ := closStepK_map (gs := gs) hxs
    simp only [Ops.co1GenAux, closAuxK, hstep, List.length_map]
    by_cases hc : (closStepK d gs xs).length = xs.length
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      exact closAuxK_map gs n _ hcan

private theorem closK_map {d : Nat} (gs : List Nat) (fuel : Nat) :
    (ops2 d).co1GenClosure (gs.map (unpackR d)) fuel =
      (closAuxK d gs fuel [idF d]).map (unpackR d) := by
  unfold Ops.co1GenClosure
  have h1 : [(ops2 d).one] = [idF d].map (unpackR d) := by
    rw [List.map_singleton, unpackR_idF_eq_one]
  rw [h1]
  exact closAuxK_map gs fuel [idF d] fun x hx => by
    rw [List.mem_singleton.1 hx]
    exact CFSG.KC.Co1F2.idF_canon d

private theorem allPowK_sound {d e : Nat} (he : e < 2 ^ 16) {L : List Nat}
    (h : L.all (fun x => Nat.beq (powK d x e) (idF d)) = true) :
    (L.map (unpackR d)).all (fun x => (ops2 d).eq ((ops2 d).pow x e) (ops2 d).one) = true := by
  rw [List.all_map]
  refine List.all_eq_true.2 fun x hx => ?_
  simp only [Function.comp_apply]
  rw [← unpackR_powK he, ← unpackR_idF_eq_one]
  exact eq_of_beq (List.all_eq_true.1 h x hx)

private theorem co1Closed_of_K {d : Nat} {gs xs : List Nat}
    (h : xs.all (fun x => gs.all fun g => xs.any (Nat.beq (mulF d x g))) = true) :
    (ops2 d).co1GenClosed (gs.map (unpackR d)) (xs.map (unpackR d)) = true := by
  unfold Ops.co1GenClosed
  rw [List.all_map]
  refine List.all_eq_true.2 fun x hx => ?_
  simp only [Function.comp_apply]
  rw [List.all_map]
  refine List.all_eq_true.2 fun g hg => ?_
  simp only [Function.comp_apply]
  rw [List.any_map]
  refine any_mono (fun y _ hy => ?_) (List.all_eq_true.1 (List.all_eq_true.1 h x hx) g hg)
  simp only [Function.comp_apply]
  rw [← unpackR_mulF]
  exact eq_of_beq hy

private theorem planeK_regs {d m : Nat} {Rl : List Nat} {Pl : Co1Gen.Plane}
    (h : planeK d m Rl Pl = true) : Pl.u < m ∧ Pl.v < m ∧ ∀ N ∈ Pl.norms, N.reg < m := by
  simp only [planeK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hu, hv, -, -, -, -, -, hn⟩ := h
  refine ⟨hu, hv, fun N hN => ?_⟩
  have hN := List.all_eq_true.1 hn N hN
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hN
  exact hN.1

private theorem planeK_sound {d m : Nat} {Rl : List Nat} {Ra : Array (Array Nat)}
    (hreg : ∀ r < m, Ra[r]! = unpackR d (getR d Rl r)) {Pl : Co1Gen.Plane}
    (h : planeK d m Rl Pl = true) : (ops2 d).co1GenPlane m Ra Pl = true := by
  simp only [planeK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hu, hv, ht, hU5, hV5, hUV, hdist, hnorms⟩ := h
  unfold Ops.co1GenPlane
  rw [hreg _ hu, hreg _ hv]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨hu, hv, ?_, ?_, commOK_of_commK hUV, normalFormOK2_of_K ht hdist, ?_⟩
  · rw [← unpackR_powK (by norm_num), ← unpackR_idF_eq_one]
    exact eq_of_beq hU5
  · rw [← unpackR_powK (by norm_num), ← unpackR_idF_eq_one]
    exact eq_of_beq hV5
  · refine List.all_eq_true.2 fun N hN => ?_
    have hN' := List.all_eq_true.1 hnorms N hN
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hN'
    obtain ⟨hr, ho, ho16, hpow, hconj⟩ := hN'
    rw [hreg _ hr]
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    refine ⟨hr, ho, ?_, ?_⟩
    · rw [← unpackR_powK (lt16 ho16), ← unpackR_idF_eq_one]
      exact eq_of_beq hpow
    · rw [show [unpackR d (getR d Rl Pl.u), unpackR d (getR d Rl Pl.v)] =
          [getR d Rl Pl.u, getR d Rl Pl.v].map (unpackR d) from rfl, List.all_map]
      refine List.all_eq_true.2 fun s hs => ?_
      simp only [Function.comp_apply]
      refine any_mono (fun a ha hp => ?_) (List.all_eq_true.1 hconj s hs)
      refine any_mono (fun b hb hp' => ?_) hp
      have ha' : a < 2 ^ 16 := lt_of_lt_of_le (List.mem_range.1 ha) (by norm_num)
      have hb' : b < 2 ^ 16 := lt_of_lt_of_le (List.mem_range.1 hb) (by norm_num)
      rw [← unpackR_powK ha', ← unpackR_powK hb', ← unpackR_mulF]
      exact conjOK_of_conjK hp'

private theorem run2K_get {d n : Nat} {prog : List Op} {ns : List Nat}
    (hprog : prog.all (Op.lt n) = true) (hexp : prog.all expOK = true) {r : Nat} (hr : r < n) :
    ((ops2 d).run prog (Array.ofFn (n := n) fun i =>
        ((ns.map (unpackR d))[i.val]?).getD (ops2 d).one))[r]! =
      unpackR d (getR d (prog.foldl (stepK d) ((List.range n).map fun i => ns.getD i (idF d))) r) := by
  have hinitlen : ((List.range n).map fun i => ns.getD i (idF d)).length = n := by simp
  have hinitsize : (Array.ofFn (n := n) fun i =>
      ((ns.map (unpackR d))[i.val]?).getD (ops2 d).one).size = n := by simp
  have hmap : ((List.range n).map fun i => ns.getD i (idF d)).map (unpackR d) =
      (Array.ofFn (n := n) fun i => ((ns.map (unpackR d))[i.val]?).getD (ops2 d).one).toList := by
    apply List.ext_getElem
    · simp
    · intro i h1 _
      simp only [List.getElem_map, List.getElem_range, Array.toList_ofFn, List.getElem_ofFn,
        List.getElem?_map]
      by_cases hi : i < ns.length
      · rw [List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]
        rfl
      · rw [List.getElem?_eq_none (by omega), List.getD_eq_default _ _ (by omega)]
        exact unpackR_idF_eq_one d
  have hexp' : prog.all CFSG.KC.LocalComp.Cub.expOK = true := by
    rw [← expOK_eq_cub]
    exact hexp
  have hmap' := CFSG.KC.LocalComp.Cub.run_map hinitlen hinitsize hmap hprog hexp'
  have hlen := CFSG.KC.LocalComp.Cub.length_stepK_foldl d n prog _ hinitlen
  have hsize := CFSG.KC.LocalComp.Cub.size_run d n prog _ hinitsize
  rw [stepK_eq_cub]
  exact (CFSG.KC.LocalComp.Cub.getR_map hlen hsize hmap' hr).symm

theorem co1GenCheck_of_K {d A B : Nat} {csA csB : List Char} {D : Co1Gen.Data}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (h : co1GenK d A B D = true) : (ops2 d).co1GenCheck D = true := by
  simp only [co1GenK, seedsOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, hexp, hexp2, hn, hprog, hA2, hB3, hpg5, hclosed, h625, hP1, hP2, hnsl,
    hprog2, hrA, hrB, hRA, hRB⟩ := h
  have eA : (ops2 d).decode D.seedA = unpackR d A := by
    change CFSG.Sporadic.SmallF2.Native.rowsOfPayload d D.seedA = _
    rw [hsA]
    exact CFSG.KC.Co1F2.bind_sound hA
  have eB : (ops2 d).decode D.seedB = unpackR d B := by
    change CFSG.Sporadic.SmallF2.Native.rowsOfPayload d D.seedB = _
    rw [hsB]
    exact CFSG.KC.Co1F2.bind_sound hB
  have hreg : ∀ r < D.nregs, ((ops2 d).regsOf D.seedA D.seedB D.nregs D.prog)[r]! =
      unpackR d (getR d (runK d A B D.nregs D.prog) r) :=
    fun r hr => regs_get hA hB hsA hsB hprog hexp hr
  obtain ⟨h1u, h1v, h1n⟩ := planeK_regs hP1
  obtain ⟨h2u, h2v, h2n⟩ := planeK_regs hP2
  have hpg : [((ops2 d).regsOf D.seedA D.seedB D.nregs D.prog)[D.plane1.u]!,
      ((ops2 d).regsOf D.seedA D.seedB D.nregs D.prog)[D.plane1.v]!,
      ((ops2 d).regsOf D.seedA D.seedB D.nregs D.prog)[D.plane2.u]!,
      ((ops2 d).regsOf D.seedA D.seedB D.nregs D.prog)[D.plane2.v]!] =
      [getR d (runK d A B D.nregs D.prog) D.plane1.u, getR d (runK d A B D.nregs D.prog) D.plane1.v,
        getR d (runK d A B D.nregs D.prog) D.plane2.u,
        getR d (runK d A B D.nregs D.prog) D.plane2.v].map (unpackR d) := by
    rw [hreg _ h1u, hreg _ h1v, hreg _ h2u, hreg _ h2v]
    rfl
  have hns : ((D.plane1.norms ++ D.plane2.norms).map fun n =>
      ((ops2 d).regsOf D.seedA D.seedB D.nregs D.prog)[n.reg]!) =
      ((D.plane1.norms ++ D.plane2.norms).map fun n =>
        getR d (runK d A B D.nregs D.prog) n.reg).map (unpackR d) := by
    rw [List.map_map]
    refine List.map_congr_left fun N hN => ?_
    rcases List.mem_append.1 hN with hN | hN
    · exact hreg _ (h1n N hN)
    · exact hreg _ (h2n N hN)
  unfold Ops.co1GenCheck
  dsimp only
  rw [hpg, hns, closK_map, eA, eB, run2K_get hprog2 hexp2 hrA, run2K_get hprog2 hexp2 hrB]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨hn, hprog, ?_, ?_, allPowK_sound (by norm_num) hpg5, co1Closed_of_K hclosed,
    allPowK_sound (by norm_num) h625, planeK_sound hreg hP1, planeK_sound hreg hP2,
    by rw [List.length_map]; exact hnsl, hprog2, hrA, hrB, eq_of_beq hRA, eq_of_beq hRB⟩
  · rw [← unpackR_powK (by norm_num), ← unpackR_idF_eq_one]
    exact eq_of_beq hA2
  · rw [← unpackR_powK (by norm_num), ← unpackR_idF_eq_one]
    exact eq_of_beq hB3

end CFSG.KC.OpsF2K

end
