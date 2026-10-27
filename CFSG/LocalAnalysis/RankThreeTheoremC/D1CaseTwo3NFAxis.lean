module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFAxis
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.exists_axis_inv (hOut : KFactOutCyclic) (hSc : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hd : D1CaseTwoData3 p P M H R Rbar) {z : H}
    (hz : D1CaseTwoCand p M H R z) (hnSP : ¬ D1CzSP p (z : G)) (hout : D1CzOutside p (z : G))
    (hB0 : D1CzB0 p R (z : G)) :
    ∃ w ∈ R, orderOf w = p ∧ w ∉ Subgroup.zpowers (z : G) ∧ (∀ g ∈ R, Commute w g) ∧
      (∀ g ∈ (P : Subgroup G), Commute w g) ∧
      (∀ g ∈ (P : Subgroup G), (∀ h ∈ (P : Subgroup G), Commute g h) → g ^ p = 1 →
        g ∈ Subgroup.zpowers w) ∧
      (∀ g ∈ R, (∀ h ∈ R, Commute g h) → g ^ p = 1 →
        g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G)) ∧
      ∃ s ∈ Subgroup.normalizer (R : Set G), s * (z : G) * s⁻¹ = z ∧
        s * w * s⁻¹ ∈ Subgroup.zpowers w ∧ s * w * s⁻¹ ≠ w :=
  D1CaseTwoDataAt.exists_axis_inv (hAut := (kFactCycAut_of_kFactOutCyclic hOut)) (hSc := hSc)
    (hL2 := hL2) (hInv := hInv.toIn) (hSch := hSch) (hSyl := hSyl) (hd := hd.toAt) (hz := hz)
    (hnSP := hnSP) (hout := hout) (hB0 := hB0)

end CFSG.LocalAnalysis.RankThreeTheoremC
