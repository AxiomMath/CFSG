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

private theorem co1SpanK_map {d : Nat} : ∀ gs : List Nat,
    (ops2 d).co1Span (gs.map (unpackR d)) = (co1SpanK d gs).map (unpackR d)
  | [] => by rw [List.map_nil, Ops.co1Span, co1SpanK, List.map_singleton, unpackR_idF_eq_one]
  | g :: gs => by
    rw [List.map_cons, Ops.co1Span, co1SpanK, co1SpanK_map gs, List.flatMap_map, List.map_flatMap]
    congr 1
    funext x
    rw [List.map_map]
    refine List.map_congr_left fun a ha => ?_
    simp only [Function.comp_apply]
    rw [unpackR_mulF, unpackR_powK (lt_of_lt_of_le (List.mem_range.1 ha) (by norm_num))]

private theorem co1PCK_sound {d : Nat} : ∀ gs : List Nat, co1PCK d gs = true →
    (ops2 d).co1PC (gs.map (unpackR d)) = true
  | [], _ => rfl
  | g :: gs, h => by
    rw [co1PCK, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h5, hc⟩, hpc⟩ := h
    rw [List.map_cons, Ops.co1PC, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, co1PCK_sound gs hpc⟩
    · rw [← unpackR_powK (by norm_num), ← unpackR_idF_eq_one]
      exact eq_of_beq h5
    · rw [co1SpanK_map, List.all_map]
      refine List.all_eq_true.2 fun k hk => ?_
      simp only [Function.comp_apply]
      rw [List.any_map]
      refine any_mono (fun w _ hw => ?_) (List.all_eq_true.1 hc k hk)
      exact conjOK_of_conjK hw

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
  obtain ⟨-, -, -, hexp, hexp2, hn, hprog, hA2, hB3, hpc, hv2, hP1, hP2, hnsl,
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
  have hns : ((D.plane1.norms ++ D.plane2.norms).map fun n =>
      ((ops2 d).regsOf D.seedA D.seedB D.nregs D.prog)[n.reg]!) =
      ((D.plane1.norms ++ D.plane2.norms).map fun n =>
        getR d (runK d A B D.nregs D.prog) n.reg).map (unpackR d) := by
    rw [List.map_map]
    refine List.map_congr_left fun N hN => ?_
    rcases List.mem_append.1 hN with hN | hN
    · exact hreg _ (h1n N hN)
    · exact hreg _ (h2n N hN)
  have hpcO := co1PCK_sound _ hpc
  simp only [List.map_cons, List.map_nil, unpackR_mulF] at hpcO
  rw [unpackR_powK (by norm_num), unpackR_powK (by norm_num)] at hpcO
  have hv2O : ((ops2 d).co1Span ([getR d (runK d A B D.nregs D.prog) D.plane1.u,
      getR d (runK d A B D.nregs D.prog) D.plane1.v].map (unpackR d))).any
      ((ops2 d).eq (unpackR d (getR d (runK d A B D.nregs D.prog) D.plane2.v))) = true := by
    rw [co1SpanK_map, List.any_map]
    refine any_mono (fun w _ hw => ?_) hv2
    exact eq_of_beq hw
  simp only [List.map_cons, List.map_nil] at hv2O
  unfold Ops.co1GenCheck
  dsimp only
  rw [hreg _ h1u, hreg _ h1v, hreg _ h2u, hreg _ h2v, hns, eA, eB, run2K_get hprog2 hexp2 hrA,
    run2K_get hprog2 hexp2 hrB]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨hn, hprog, ?_, ?_, hpcO, hv2O, planeK_sound hreg hP1, planeK_sound hreg hP2,
    by rw [List.length_map]; exact hnsl, hprog2, hrA, hrB, eq_of_beq hRA, eq_of_beq hRB⟩
  · rw [← unpackR_powK (by norm_num), ← unpackR_idF_eq_one]
    exact eq_of_beq hA2
  · rw [← unpackR_powK (by norm_num), ← unpackR_idF_eq_one]
    exact eq_of_beq hB3

end CFSG.KC.OpsF2K

end
