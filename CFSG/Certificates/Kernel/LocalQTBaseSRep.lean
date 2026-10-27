module

public import CFSG.Certificates.Kernel.LocalQTBaseSProved

public section

namespace CFSG.KC.LQT.BS

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf CFSG.KC.LQT.BS.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm

theorem baseSK_rep {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat)
    (zn gn gin hn hin k fuel M lg : Nat) (E : Nat → Nat) (K2 L2 : Nat)
    (h : baseSK n w B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true) :
    (slpTabsA ta.toArray tb.toArray prog).size = prog.length + 2 ∧
    ∀ j < (slpTabsA ta.toArray tb.toArray prog).size,
      Rep n w (TF j) (slpTabsA ta.toArray tb.toArray prog)[j]! := by
  rw [baseSK] at h
  dsimp only at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨hta, htb, hso, hTF0, hTF1, hKm, -⟩ := h
  have hnodes : ∀ q < prog.length, TF (2 + q) =
      mulW n w (TF (prog.getD q (0, 0)).1) (TF (prog.getD q (0, 0)).2) := by
    intro q hq
    have hKm' := Nat.le_of_ble_eq_true hKm
    rw [lenA_eq, Nat.add_eq, Nat.mul_eq] at hKm'
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, Nat.mul_zero] at hKm'
        omega
      · exact h0
    have hc : (2 + q) / m < K := by
      rw [Nat.div_lt_iff_lt_mul hm0]
      omega
    have := allR_true (hnd _ hc) ((2 + q) % m) (Nat.mod_lt _ hm0)
    rw [Nat.div_add_mod'] at this
    dsimp only at this
    have h2 : CFSG.KC.Ord.andB (Nat.ble 2 (2 + q)) (Nat.blt (2 + q) (Nat.add (lenA prog) 2)) = true := by
      rw [andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, lenA_eq, Nat.add_eq]
      constructor <;> omega
    have := impB_true this h2
    rw [P.beq_iff, nthP_eq, show Nat.sub (2 + q) 2 = q by rw [Nat.sub_eq]; omega] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [slpTabsA, foldl_slpStepA_size]
    simp only [List.size_toArray, List.length_cons, List.length_nil]
    omega
  · rw [slpTabsA]
    apply slpTF_rep prog #[ta.toArray, tb.toArray]
    · intro j hj
      rcases j with _ | _ | j
      · rw [P.beq_iff.1 hTF0]
        exact rep_codeK hw hta
      · rw [P.beq_iff.1 hTF1]
        exact rep_codeK hw htb
      · simp at hj
    · exact slpOKK_spec' prog 2 hso
    · intro q hq
      exact hnodes q hq

end CFSG.KC.LQT.BS

end
