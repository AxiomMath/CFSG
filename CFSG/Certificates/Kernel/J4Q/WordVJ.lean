module

public import CFSG.Certificates.Kernel.J4Q.RepQT2B
public import Certificates.Data.Kernel.J4Q.Words26

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.Native CFSG.KC.Loop

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem frApply_idRows4204 {v : V2} (hv : v.wf = true) : frApply (frTable (idRows ())) v = v := by
  apply V2.eq_of_toVec_eq (wf_frApply wf_idRows v) hv
  rw [CFSG.Sporadic.J4.frApply_toVec_eq_vecMul, CFSG.Sporadic.J4.rowsMatrix_idRows,
    Matrix.vecMul_one]

theorem wordVJ_from4204 (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
    {mats invs : Array (Array V2)} {ms is : List Nat}
    (hm : ∀ k, WfA (mats[k]?.getD (idRows ())) ∧ encR (mats[k]?.getD (idRows ())) = getN one ms k)
    (hi : ∀ k, WfA (invs[k]?.getD (idRows ())) ∧ encR (invs[k]?.getD (idRows ())) = getN one is k) :
    ∀ (w : List Int) (acc : Array V2), WfA acc → ∀ {v : V2}, v.wf = true →
      v2N (frApply (frTable (w.foldl (fun acc l => mulRows acc (if 0 < l then
        mats[l.toNat - 1]?.getD (idRows ()) else invs[(-l).toNat - 1]?.getD (idRows ()))) acc)) v) =
        wordVJ rm one ms is w (v2N (frApply (frTable acc) v))
  | [], _, _, _, _ => rfl
  | l :: w, acc, hacc, v, hv => by
    obtain ⟨hl1, hl2⟩ := letter_enc hm hi l
    rw [List.foldl_cons, wordVJ_from4204 hK hm hi w _ (wf_mulRows hacc hl1) hv,
      vec_mulRows hacc hl1 hv, v2N_frApply hK hl1 (wf_frApply hacc v), hl2]
    exact (strictN_eq _ _).symm

theorem wordVJ_frApply (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
    {mats invs : Array (Array V2)} {ms is : List Nat}
    (hm : ∀ k, WfA (mats[k]?.getD (idRows ())) ∧ encR (mats[k]?.getD (idRows ())) = getN one ms k)
    (hi : ∀ k, WfA (invs[k]?.getD (idRows ())) ∧ encR (invs[k]?.getD (idRows ())) = getN one is k)
    (w : List Int) {v : V2} (hv : v.wf = true) :
    v2N (frApply (frTable (wordRows mats invs w)) v) = wordVJ rm one ms is w (v2N v) := by
  have h := wordVJ_from4204 hK hm hi w (idRows ()) wf_idRows hv
  rw [frApply_idRows4204 hv] at h
  exact h

end CFSG.KC.J4Q

end
