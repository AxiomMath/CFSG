module

public import CFSG.Certificates.Kernel.AS35QTS.QpowSound

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC.F4M3B CFSG.Fischer
open CFSG.LargeExtraspecial.AS35QTS (Cd mulC e0 tau0 cgens)

theorem eqP_lane {t c : Nat} (ht : t.testBit c = true) (X Y : PL Nat) :
    (eqP (natOps t) X Y).testBit c = eqP bOps (laneOf c X) (laneOf c Y) := by
  simp only [eqP, eqV, isEq, bnot, laneOf, mapP, natOps, bOps, tb_land, tb_xor, ht]

theorem commP_lane {t c : Nat} (ht : t.testBit c = true) (X C : PL Nat) :
    (commP t X C).testBit c =
      eqP bOps (laneOf c (mulD (natOps t) X C)) (laneOf c (mulD (natOps t) C X)) := by
  unfold commP
  rw [mulK_eq (natOps t) frcN_eq, mulK_eq (natOps t) frcN_eq, eqP_lane ht]

theorem fold_tb (t c : Nat) (f : Nat → Nat) : ∀ L : List Nat,
    (List.rec (motive := fun _ => Nat) t (fun g _ ih => Nat.land (f g) ih) L).testBit c =
      (t.testBit c && L.all fun g => (f g).testBit c)
  | [] => by simp
  | g :: L => by
    change (Nat.land (f g) (List.rec (motive := fun _ => Nat) t
      (fun g _ ih => Nat.land (f g) ih) L)).testBit c = _
    rw [tb_land, fold_tb t c f L, List.all_cons, Bool.and_left_comm]

theorem bnot_natOps (t p : Nat) : bnot (natOps t) p = Nat.xor p t := rfl

theorem tb_lor (p q c : Nat) : (Nat.lor p q).testBit c = (p.testBit c || q.testBit c) :=
  Nat.testBit_or p q c

theorem gensIx_eq : gensIx.map decN = cgens := rfl

theorem decN_ixT : decN ixT = tau0 := rfl

theorem centerOK_spec {G : List Nat} (hg : gOK G = true) (hG : G.length = 648)
    (h : centerOK G = true) :
    ∀ q ∈ CFSG.LargeExtraspecial.AS35QTS.codes, (∀ g ∈ cgens, mulC q g = mulC g q) →
      q = e0 ∨ q = tau0 := by
  have hGb : ∀ g ∈ G, g < 2 ^ 18 := fun g hg' => by
    have := incB_lt (gOK_spec hg).1 g hg'
    omega
  intro q hq hcomm
  rw [codes_eq hG (gu3s_eq hg) hGb] at hq
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hq
  have hc' := List.mem_range.1 hc
  have ht : allT.testBit c = true := allT_testBit hc'
  have hX := lane_lanes hG hGb hc'
  unfold centerOK at h
  rw [frc_eqL, lanesK_eq] at h
  have hb := congrArg (fun p => Nat.testBit p c) (Nat.eq_of_beq_eq_true h)
  simp only [Nat.zero_testBit] at hb
  rw [tb_land, fold_tb, ht, Bool.true_and] at hb
  have hall : (gensIx.all fun g => (commP allT (ofIx (lanePl G)) (cst allT g)).testBit c) = true := by
    rw [List.all_eq_true]
    intro g hgm
    rw [commP_lane ht, lane_mulP _ _ hX (lane_cst ht g), lane_mulP _ _ (lane_cst ht g) hX]
    exact (eqP_e _ _).2 (hcomm _ (gensIx_eq ▸ List.mem_map_of_mem hgm))
  rw [hall, Bool.true_and] at hb
  rw [bnot_natOps, tb_xor, ht, tb_lor, eqP_lane ht, eqP_lane ht, hX, lane_cst ht, lane_cst ht,
    decN_ixE, decN_ixT] at hb
  cases h1 : eqP bOps (ofCd _) (ofCd e0)
  · cases h2 : eqP bOps (ofCd _) (ofCd tau0)
    · rw [h1, h2] at hb
      exact absurd hb (by decide)
    · exact Or.inr ((eqP_e _ _).1 h2)
  · exact Or.inl ((eqP_e _ _).1 h1)

end CFSG.KC.AS35QTS

end
