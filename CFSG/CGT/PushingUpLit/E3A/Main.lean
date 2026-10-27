module

public import CFSG.CGT.PushingUpLit.SolK.Inputs
public import CFSG.CGT.PushingUpLit.E3A.Lin
public import CFSG.CGT.PushingUpLit.E3A.Borel
public import CFSG.CGT.PushingUpLit.E3A.Prime
public import CFSG.CGT.Timmesfeld75.ListWCCert

public section

namespace CFSG.CGT.PushingUpLit.E3A

open CFSG CFSG.RankThree.PartOne CFSG.CGT.Timmesfeld75 CFSG.CGT.PushingUpLit.SolK
  CFSG.Assembly.LowTwoRank

theorem wcBlockCentralizer_of_list
    (hSCL : SimpleCaseListStmt) : WCBlockCentralizer := by
  intro G _ _ hsimple _ R X n hn hRab hR4 hTI _ hWC _ hXN _ _ hnat hXC
  have := hsimple
  have hna : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_block hn hnat
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  have hwc : IsWC R := isWC_of_corBHyp
    (corBHyp_of_ti_of_weaklyClosed hRab (fun g => hTI g⁻¹) (fun g => hWC.2 g⁻¹))
  have hlist : ListGroup G := hSCL G hna R hwc hR4
  have hstd : StdPair G R := listWCIdentification_of_cert G hlist R hwc hR4
  have borel : BorelTwoTransitive G R → False := by
    rintro ⟨-, S, hS⟩
    exact false_of_le_normalizer_sylow S hn (hS ▸ hXN) hnat
  rcases hlist with ⟨m, s, hm, hs, hmod⟩ | ⟨s, hs, hmod⟩ | ⟨s, hodd, hs3, hmod⟩ |
    ⟨k, hk6, hk9, he⟩ | hM22 | hM23 | hM24
  · by_cases hm3 : 3 ≤ m
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
      have : CharP K 2 := charP_two_of_card hK
      obtain ⟨-, hR⟩ := hstd.of_psl hm3 K hK e
      exact false_of_lin hn hm3 e hR hnat hXC
    · have hm2 : m = 2 := by omega
      subst hm2
      exact borel (hstd.of_psl2 hmod).2.2
  · exact borel (hstd.of_psu3 hs hmod).2.2
  · exact borel (hstd.of_sz hodd hs3 hmod).2.2
  · exact false_of_alt hn hk6 hk9 he.some (hstd.card_alternating hk6 hk9 he) hnat hXC
  · exact false_of_order_sixteen hn (hstd.card_sporadic (Or.inl hM22)) hstd.transitive
      (by
        obtain ⟨e⟩ := hM22
        rw [Nat.card_congr e.toEquiv]
        have := CFSG.Sporadic.Mathieu.card_M22
        change ¬ 25 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M22
        rw [this]
        norm_num) hnat hXC
  · exact false_of_order_sixteen hn (hstd.card_sporadic (Or.inr (Or.inl hM23))) hstd.transitive
      (by
        obtain ⟨e⟩ := hM23
        rw [Nat.card_congr e.toEquiv]
        have := CFSG.Sporadic.Schreier.m23_card
        change ¬ 25 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M23
        rw [this]
        norm_num) hnat hXC
  · exact false_of_order_sixteen hn (hstd.card_sporadic (Or.inr (Or.inr hM24))) hstd.transitive
      (by
        obtain ⟨e⟩ := hM24
        rw [Nat.card_congr e.toEquiv]
        have := CFSG.Sporadic.Mathieu.card_M24
        change ¬ 25 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M24
        rw [this]
        norm_num) hnat hXC

end CFSG.CGT.PushingUpLit.E3A
