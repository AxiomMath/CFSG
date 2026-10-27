module

public import CFSG.Certificates.Kernel.Census.SoundProof

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert

theorem penumOK_sound {n w : Nat} {gs : Array Nat} {ps : List Nat} {c : ArrCertP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hg : gs.toList.all (canon1 n w) = true)
    (hc : c.pts.toList.all (canon1 n w) = true) (h : penumOK n w gs ps c = true) :
    enumOKK n (gs.map (unpackP n w)) ps (c.toMain n w) = true := by
  have h' := h
  unfold penumOK at h'
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
  obtain ⟨-, ⟨⟨h0, hid⟩, -⟩, -⟩ := h'
  have hv0 := pvalid_pts_of_penumOK h c.pts[0]! (by
    rw [getElem!_pos c.pts 0 h0]
    exact Array.getElem_mem_toList h0)
  rw [hid] at hv0
  obtain ⟨e1, e2⟩ := SP.pid_good hw hv0
  exact SP.enumOKK_of_penumOK ⟨hn, hw, e1, e2⟩ (List.all_eq_true.1 hg) (List.all_eq_true.1 hc) h

end CFSG.KC.Census
