module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Table
public import CFSG.RankThree.PartOne.MultRes.Co2
public import CFSG.RankThree.PartOne.MultRes.Co3
public import CFSG.RankThree.PartOne.MultRes.ON
public import CFSG.RankThree.PartOne.MultRes.McL
public import CFSG.RankThree.PartOne.MultRes.Th
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Fi24Seven

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Blueprint
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd SporadicOrdersTable)
open scoped commutatorElement


theorem twoRankLe_two_of_carrier_cubic {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime)
    (hOrd : SporadicOrdersTable)
    (hbr : Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (h4 : ¬ p ^ 4 ∣ sporOrd s)
    (hW : ∃ x y : NativeSporadic.Carrier s, ⁅x, y⁆ ≠ 1 ∧
      Nat.card (Subgroup.closure ({x, y} : Set (NativeSporadic.Carrier s))) = p ^ 3) :
    TwoRankLe p s 2 := by
  obtain ⟨b⟩ := hbr
  obtain ⟨x, y, hz, hcard⟩ := hW
  have hc : Nat.card (NativeSporadic.Carrier s) = sporOrd s :=
    (Nat.card_congr b.toEquiv).trans (hOrd s)
  haveI : Finite (NativeSporadic.Carrier s) := Nat.finite_of_card_ne_zero (by
    rw [hc]
    intro h0
    apply h4
    rw [h0]
    exact dvd_zero _)
  exact twoRankLe_two_of_cubic hp ⟨b⟩ (by rw [hc]; exact h4) hz hcard

set_option maxRecDepth 10000 in
theorem row_m12 (hOrd : SporadicOrdersTable) : TwoRankLe 3 .M12 2 :=
  twoRankLe_two_of_carrier_cubic (s := .M12) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.M12_sylow3_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_m24 (hOrd : SporadicOrdersTable) : TwoRankLe 3 .M24 2 :=
  twoRankLe_two_of_carrier_cubic (s := .M24) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_j2 (hOrd : SporadicOrdersTable) : TwoRankLe 3 .J2 2 :=
  twoRankLe_two_of_carrier_cubic (s := .J2) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_j4three (hOrd : SporadicOrdersTable) : TwoRankLe 3 .J4 2 :=
  twoRankLe_two_of_carrier_cubic (s := .J4) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_j4eleven (hOrd : SporadicOrdersTable) : TwoRankLe 11 .J4 2 :=
  twoRankLe_two_of_carrier_cubic (s := .J4) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.J4_sylow11_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_hs (hOrd : SporadicOrdersTable) : TwoRankLe 5 .HS 2 :=
  twoRankLe_two_of_carrier_cubic (s := .HS) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.HS_sylow5_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_mclfive (hOrd : SporadicOrdersTable) : TwoRankLe 5 .McL 2 :=
  twoRankLe_two_of_carrier_cubic (s := .McL) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.RankThree.PartOne.MultRes.McL_sylow5_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_hethree (hOrd : SporadicOrdersTable) : TwoRankLe 3 .He 2 :=
  twoRankLe_two_of_carrier_cubic (s := .He) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_heseven (hOrd : SporadicOrdersTable) : TwoRankLe 7 .He 2 :=
  twoRankLe_two_of_carrier_cubic (s := .He) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.He_sylow7_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_ruthree (hOrd : SporadicOrdersTable) : TwoRankLe 3 .Ru 2 :=
  twoRankLe_two_of_carrier_cubic (s := .Ru) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_rufive (hOrd : SporadicOrdersTable) : TwoRankLe 5 .Ru 2 :=
  twoRankLe_two_of_carrier_cubic (s := .Ru) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.Ru_sylow5_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_on (hOrd : SporadicOrdersTable) : TwoRankLe 7 .ONan 2 :=
  twoRankLe_two_of_carrier_cubic (s := .ONan) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.RankThree.PartOne.MultRes.ON_sylow7_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_co2 (hOrd : SporadicOrdersTable) : TwoRankLe 5 .Co2 2 :=
  twoRankLe_two_of_carrier_cubic (s := .Co2) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.RankThree.PartOne.MultRes.Co2_sylow5_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_co3 (hOrd : SporadicOrdersTable) : TwoRankLe 5 .Co3 2 :=
  twoRankLe_two_of_carrier_cubic (s := .Co3) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.RankThree.PartOne.MultRes.Co3_sylow5_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_fi24 (hOrd : SporadicOrdersTable) : TwoRankLe 7 .Fi24Prime 2 :=
  twoRankLe_two_of_carrier_cubic (s := .Fi24Prime) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Fi24prime_sylow7_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

set_option maxRecDepth 10000 in
theorem row_th (hOrd : SporadicOrdersTable) : TwoRankLe 5 .Th 2 :=
  twoRankLe_two_of_carrier_cubic (s := .Th) (by norm_num) hOrd
    CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
    (by norm_num [sporOrd, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON,
      CFSG.Open.orderFi24Prime, CFSG.Open.orderTh])
    (by
      obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.RankThree.PartOne.MultRes.Th_sylow5_cubic_witness
      exact ⟨x, y, hz, hcard⟩)

theorem i1017CubicRows_holds (hOrd : SporadicOrdersTable) : I1017CubicRows where
  m12 := row_m12 hOrd
  m24 := row_m24 hOrd
  j2 := row_j2 hOrd
  j4three := row_j4three hOrd
  j4eleven := row_j4eleven hOrd
  hs := row_hs hOrd
  mclfive := row_mclfive hOrd
  hethree := row_hethree hOrd
  heseven := row_heseven hOrd
  ruthree := row_ruthree hOrd
  rufive := row_rufive hOrd
  on := row_on hOrd
  co2 := row_co2 hOrd
  co3 := row_co3 hOrd
  fi24 := row_fi24 hOrd
  th := row_th hOrd

end CFSG.LocalAnalysis.GLTheoremA.H1017
