module

public import Certificates.Data.Kernel.J4M4F.Defs
public import CFSG.Certificates.Kernel.J4Q.Rep
public import CFSG.Quasithin.Vol2.KGFactC31J4M4Native

public section

namespace CFSG.KS.J4M4F

open CFSG.KC.J4Q CFSG.KD.J4M4F CFSG.Sporadic.J4.Native CFSG.Quasithin.KGC31.J4M4

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem fRows_fold (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {T : Array (Array V2)}
    {FM : List Nat}
    (hT : ∀ j < 10, WfA (T[j]?.getD (idRows ())) ∧ encR (T[j]?.getD (idRows ())) = getN one FM j)
    (x : Nat) : ∀ (L : List Nat), (∀ j ∈ L, j < 10) → ∀ (acc : Array V2) (a : Nat), WfA acc →
      encR acc = a →
      WfA (L.foldl (fun acc j => if x.testBit j then mulRows acc (T[j]?.getD (idRows ())) else acc)
        acc) ∧
      encR (L.foldl (fun acc j => if x.testBit j then mulRows acc (T[j]?.getD (idRows ())) else acc)
        acc) = L.foldl (fun acc j => if x.testBit j then mulJ c rm acc (getN one FM j) else acc) a
  | [], _, _, _, h1, h2 => ⟨h1, h2⟩
  | j :: L, hL, acc, a, h1, h2 => by
    simp only [List.foldl_cons]
    have hj := hL j (List.mem_cons_self ..)
    have hL' : ∀ k ∈ L, k < 10 := fun k hk => hL k (List.mem_cons_of_mem _ hk)
    by_cases hb : x.testBit j = true
    · rw [if_pos hb, if_pos hb]
      refine fRows_fold hK hT x L hL' _ _ (wf_mulRows h1 (hT j hj).1) ?_
      rw [enc_mulRows hK h1 (hT j hj).1, h2, (hT j hj).2]
    · rw [if_neg hb, if_neg hb]
      exact fRows_fold hK hT x L hL' _ _ h1 h2

theorem fRows_enc (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {T : Array (Array V2)}
    {FM : List Nat}
    (hT : ∀ j < 10, WfA (T[j]?.getD (idRows ())) ∧ encR (T[j]?.getD (idRows ())) = getN one FM j)
    (x : Nat) : WfA (fRows T x) ∧ encR (fRows T x) = fRK c rm one FM x := by
  unfold fRows fRK
  exact fRows_fold hK hT x (List.range 10) (fun _ hj => List.mem_range.1 hj) (idRows ()) one
    wf_idRows (enc_idRows hK)

theorem fVec_fold (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {T : Array (Array V2)}
    (hs : T.size = 10) {FM : List Nat}
    (hT : ∀ j < 10, WfA (T[j]?.getD (idRows ())) ∧ encR (T[j]?.getD (idRows ())) = getN one FM j)
    (x : Nat) : ∀ (L : List Nat), (∀ j ∈ L, j < 10) → ∀ (u : V2) (a : Nat), u.wf = true →
      v2N u = a →
      (L.foldl (fun acc j => if x.testBit j then frApply ((T.map frTable)[j]?.getD #[]) acc else acc)
        u).wf = true ∧
      v2N (L.foldl (fun acc j => if x.testBit j then frApply ((T.map frTable)[j]?.getD #[]) acc
        else acc) u) = L.foldl (fun acc j => if x.testBit j then vecJ rm acc (getN one FM j) else acc) a
  | [], _, _, _, h1, h2 => ⟨h1, h2⟩
  | j :: L, hL, u, a, h1, h2 => by
    simp only [List.foldl_cons]
    have hj := hL j (List.mem_cons_self ..)
    have hL' : ∀ k ∈ L, k < 10 := fun k hk => hL k (List.mem_cons_of_mem _ hk)
    by_cases hb : x.testBit j = true
    · rw [if_pos hb, if_pos hb]
      have e : (T.map frTable)[j]?.getD #[] = frTable (T[j]?.getD (idRows ())) := by
        have hjs : j < T.size := by omega
        simp only [Array.getElem?_map, Array.getElem?_eq_getElem hjs, Option.map_some,
          Option.getD_some]
      rw [e]
      refine fVec_fold hK hs hT x L hL' _ _ (wf_frApply (hT j hj).1 u) ?_
      rw [v2N_frApply hK (hT j hj).1 h1, h2, (hT j hj).2]
    · rw [if_neg hb, if_neg hb]
      exact fVec_fold hK hs hT x L hL' _ _ h1 h2

theorem fVec_enc (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {T : Array (Array V2)}
    (hs : T.size = 10) {FM : List Nat}
    (hT : ∀ j < 10, WfA (T[j]?.getD (idRows ())) ∧ encR (T[j]?.getD (idRows ())) = getN one FM j)
    {u : V2} (hu : u.wf = true) (x : Nat) :
    (fVec (T.map frTable) u x).wf = true ∧ v2N (fVec (T.map frTable) u x) = fVK rm one FM (v2N u) x := by
  unfold fVec fVK
  exact fVec_fold hK hs hT x (List.range 10) (fun _ hj => List.mem_range.1 hj) u _ hu rfl

end CFSG.KS.J4M4F

end
