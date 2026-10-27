module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Sylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D1CaseTwoData3.rstruct (hOut : KFactOutCyclic) (hSc : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h28 : KFactL28AutThree) {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} (hd : D1CaseTwoData3 3 P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand 3 M H R z) (hnSP : ¬ D1CzSP 3 (z : G))
    (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    {w : G} (hwR : w ∈ R) (hwC : w ∈ Subgroup.centralizer ({(z : G)} : Set G))
    (hwK : ∀ KC : Subgroup (D1CzQuot 3 (z : G)), IsComponentOf KC ⊤ →
      QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({(z : G)} : Set G)) 3)
        ⟨w, hwC⟩ ∈ KC) (hwo : orderOf w = 3) :
    (∃ y ∈ R, y ^ 3 = (z : G)) ∨ (Nat.card R = 3 ^ 4 ∧ ∃ a ∈ R, a ^ 3 ∈ Subgroup.zpowers w ∧
      a ^ 3 ≠ 1 ∧ ∀ r ∈ R, r ^ 3 = 1 → r ∉ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G) →
        a * r ≠ r * a) :=
  D1CaseTwoDataAt.rstruct (hAut := (kFactCycAut_of_kFactOutCyclic hOut)) (hSc := hSc) (hL2 := hL2)
    (hInv := hInv.toIn) (hSch := hSch) (hSyl := hSyl) (h28 := h28) (hd := hd.toAt) (hz := hz)
    (hnSP := hnSP) (hout := hout) (hB0 := hB0) (hwR := hwR) (hwC := hwC) (hwK := hwK) (hwo := hwo)

end CFSG.LocalAnalysis.RankThreeTheoremC
