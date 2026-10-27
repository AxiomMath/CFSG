module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsU

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def U48Cent3AtK (G : Type) [Group G] [Finite G] : Prop :=
  U48Cent3At G ∧
    ∀ (X L : Subgroup G) (y : G), GLAPComponent 3 X L → catalogIs (PSimple 3 L) S9.isU4eight → y ^ 3 = 1 → y ≠ 1 →
      IsCentralIn 3 y L →
      Subgroup.center (PQuot 3 (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({y} : Set G)))) ≠ ⊥

@[expose] def I141RankAtK (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (Ky Kxy Kay : Subgroup G) (x a y : G), CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({y} : Set G)) →
    GLAPComponent 3 (Subgroup.centralizer ({y} : Set G)) Ky → x ^ 3 = 1 → a ^ 3 = 1 → x * a = a * x →
    x ∉ Subgroup.zpowers a → x ∈ Subgroup.centralizer ({y} : Set G) → a ∈ Subgroup.centralizer ({y} : Set G) →
    GLAPComponent 3 (Ky ⊓ Subgroup.centralizer ({x} : Set G)) Kxy → catalogIs (PSimple 3 Kxy) S9.isU3eight →
    Subgroup.center (PQuot 3 Kxy) ≠ ⊥ →
    GLAPComponent 3 (Ky ⊓ Subgroup.centralizer ({a} : Set G)) Kay → catalogIs (PSimple 3 Kay) S9.isU3eight →
    FieldOn 3 a Kxy → FieldOn 3 x Kay → InnDiagOn 3 (Subgroup.zpowers x) Ky →
    InnDiagOn 3 (Subgroup.zpowers a) Ky → 5 ≤ GLATwoLocalRank 3 ↥(Subgroup.centralizer ({y} : Set G))

end CFSG.LocalAnalysis.GLTheoremA

end
