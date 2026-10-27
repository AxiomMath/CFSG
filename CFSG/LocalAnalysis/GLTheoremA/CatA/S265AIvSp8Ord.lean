module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8c

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

theorem card_centralizer_ge_of_sp6two {G : Type} [Group G] [Finite G] {d : G} {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({d} : Set G))
    (hKt : catalogIs (PSimple 3 K) S9.isSp6two) :
    1451520 ≤ Nat.card ↥(Subgroup.centralizer ({d} : Set G)) := by
  obtain ⟨e⟩ := CatB.bridge_sp6two hKt
  have h1 : Nat.card (PSimple 3 K) = 1451520 :=
    (Nat.card_congr e.toEquiv).trans CatB.U4Sp8.card_sp_three
  have h2 : Nat.card (PSimple 3 K) ∣ Nat.card K :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)
  have h3 : 1451520 ≤ Nat.card K := h1 ▸ Nat.le_of_dvd Nat.card_pos h2
  exact h3.trans (Subgroup.card_le_of_le hK)

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
