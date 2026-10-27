module

public import Certificates.Data.MaxD2PermTrans
public import Certificates.Data.MaxD2NonComm
public import CFSG.Certificates.Kernel.MaxD2.Sound

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open Certificates.MaxD2Perm

section

variable {D : Data} {K : Pk}

theorem checkNonComm_of (H : Hyps D K) {i j : Nat} (hi : i < K.kN) (hj : j < K.kN)
    (h : notInK K.rcnt K.RT (pcomp K.n K.w (mask K.w) (pcomp K.n K.w (mask K.w)
      (pcomp K.n K.w (mask K.w) (K.NG i) (K.NG j)) (K.NGI i)) (K.NGI j)) = true) :
    checkNonComm D = true := by
  obtain ⟨e, -⟩ := rEnum_eq H
  have hs : (nGens D).size = K.kN := (ngens H.toM).1
  unfold checkNonComm
  simp only []
  rw [e, anyBelow_iff]
  refine ⟨i, by rw [hs]; exact hi, ?_⟩
  rw [anyBelow_iff]
  refine ⟨j, by rw [hs]; exact hj, ?_⟩
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  intro hf
  have pi := ng_perm H.toM hi
  have pj := ng_perm H.toM hj
  rw [ng_get H.toM hi, ng_get H.toM hj, ngi_get H.toM hi, ngi_get H.toM hj, H.hDn] at hf
  unfold commTab at hf
  rw [comp_u pi.1 pj.1, comp_u (cc pi.1 pj.1) pi.2, comp_u (cc (cc pi.1 pj.1) pi.2) pj.2,
    foundR H (cc (cc (cc pi.1 pj.1) pi.2) pj.2)] at hf
  obtain ⟨r, hr, er⟩ := hf
  have hm := (PK.allN_iff.1 h) r hr
  rw [er, Nat.beq_refl] at hm
  exact absurd hm (by decide)

theorem checkTrans_of (H : Hyps D K) {INV CJ : Nat → Nat}
    (hinv : ∀ k < K.cnt, INV k < K.cnt ∧
      permOK K.n K.w (mask K.w) (K.n * K.w) (K.NT k) (K.NT (INV k)) = true)
    (hc : ∀ r < K.rcnt, K.RT r = pidn K.n K.w ∨ (CJ r < K.cnt ∧
      K.RT r = pcomp K.n K.w (mask K.w) (pcomp K.n K.w (mask K.w) (K.NT (CJ r)) (K.RG 0))
        (K.NT (INV (CJ r))))) :
    checkTrans D = true := by
  obtain ⟨eR, -⟩ := rEnum_eq H
  obtain ⟨eN, -⟩ := nEnum_eq H.toM
  have hn := H.hn
  have hu : Cn K.n K.w (K.RG 0) := (H.hRG 0 (by decide)).2
  have hmap : ∀ k < K.cnt, ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (invTab K.n))[k]! =
      unpack K.n K.w (K.NT (INV k)) := fun k hk => by
    rw [getElem!_pos _ k (by simp [rec_size, hk]), Array.getElem_map,
      ← getElem!_pos _ k (by rw [rec_size]; exact hk), rec_get hk, inv_u (hinv k hk).2]
  unfold checkTrans transConj
  simp only []
  rw [eR, eN, H.hDn, Bool.and_eq_true]
  constructor
  · unfold invsOK
    simp only [Bool.and_eq_true, beq_iff_eq, Array.size_map, rec_size, true_and]
    refine allBelow_iff'.2 fun k hk => ?_
    rw [hmap k hk, rec_get hk, inv_comp (hinv k hk).2]
    simp [size_u]
  · refine allBelow_iff'.2 fun r hr => ?_
    rw [rec_size] at hr
    rw [rec_get hr, Bool.or_eq_true]
    rcases hc r hr with e | ⟨hlt, e⟩
    · left
      rw [e, ← id_u hn]
      exact beq_self_eq_true _
    · right
      rw [found_iff]
      refine ⟨CJ r, by simp [rec_size, hlt], ?_⟩
      rw [getElem!_pos _ _ (by simp [rec_size, hlt]), Array.getElem_ofFn]
      simp only []
      rw [rec_get hlt, inv_u (hinv _ hlt).2,
        rg_get H (by decide)]
      have ha := nt_canon H.toM hlt
      have hb := nt_canon H.toM (hinv _ hlt).1
      unfold conjTab
      rw [comp_u ha hu, comp_u (cc ha hu) hb, e]

end

end CFSG.KS.MaxD2

end
