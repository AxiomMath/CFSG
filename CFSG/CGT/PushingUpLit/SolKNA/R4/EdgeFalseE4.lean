module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.EdgeFalseT
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinReduce
public import CFSG.ClassicalInvolution.Q3.TL4E3Defs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3

section Cit3


theorem tightE3E4R_of_four_le {r n : ℕ} (hr : 4 ≤ r) (h4 : NoQ16E4) : TL4.TightE3E4R r n := by
  intro Y _ _ R S t hL _ _ _ J hJ u hu htu ht Sb hex hedge
  obtain ⟨Sq, hdq, ⟨eq⟩⟩ := exists_secDatumR hL.datum hJ.1.2 hu htu ht
  have hdb := hdq.ofSylow Sb
  have hqb : Nonempty (↥(Sb : Subgroup ↥(secR R u)) ≃* QuaternionGroup (2 ^ (r - 2))) :=
    ⟨(Sylow.equiv Sb Sq).trans (eq.trans hL.cls.1.some)⟩
  rcases hex with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨Q, hQ, f, hfs, hf2, -, hm⟩
  · exact h
  · exact absurd h hedge
  · exact absurd h hedge
  · exact tightInO2_of_twinE4' hr h4
      (PhilipHall.QuaternionBridge.TightDatum.toQ8TwinDatum hdb) hqb ⟨Q, hQ, f, hfs, hf2, hm⟩

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4
