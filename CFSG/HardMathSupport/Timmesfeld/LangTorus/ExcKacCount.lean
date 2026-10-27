module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice

@[expose] def kacTest {r : ℕ} (θ : Fin r → ℤ) (C : Finset (Option (Fin r))) (γ : Fin r → ℤ) :
    Prop :=
  (∀ j, some j ∉ C → γ j = 0) ∨
    (none ∈ C ∧ ((∀ j, some j ∉ C → γ j = -θ j) ∨ (∀ j, some j ∉ C → γ j = θ j)))

instance {r : ℕ} (θ : Fin r → ℤ) (C : Finset (Option (Fin r))) (γ : Fin r → ℤ) :
    Decidable (kacTest θ C γ) := by
  unfold kacTest
  infer_instance

@[expose] def kacCount (τ : Tag) (θ : Fin τ.rank → ℤ) (C : Finset (Option (Fin τ.rank))) : ℕ :=
  (τ.artifactRoots.filter fun l => decide (kacTest θ C (toVec τ.rank l))).length

set_option maxRecDepth 100000

theorem kacCount_E8_six : ∀ C : Finset (Option (Fin Tag.E8.rank)), C.card = 6 →
    kacCount .E8 ![2, 3, 4, 6, 5, 4, 3, 2] C = 72 →
    C = {some 0, some 1, some 2, some 3, some 4, some 5} := by
  decide +kernel

theorem kacCount_E8_four : ∀ C : Finset (Option (Fin Tag.E8.rank)), C.card = 4 →
    kacCount .E8 ![2, 3, 4, 6, 5, 4, 3, 2] C = 24 → C = {some 1, some 2, some 3, some 4} := by
  decide +kernel

theorem kacCount_E7_six : ∀ C : Finset (Option (Fin Tag.E7.rank)), C.card = 6 →
    kacCount .E7 ![2, 2, 3, 4, 3, 2, 1] C = 72 →
    C = {some 0, some 1, some 2, some 3, some 4, some 5} := by
  decide +kernel

theorem kacCount_E7_four : ∀ C : Finset (Option (Fin Tag.E7.rank)), C.card = 4 →
    kacCount .E7 ![2, 2, 3, 4, 3, 2, 1] C = 24 → C = {some 1, some 2, some 3, some 4} := by
  decide +kernel

theorem kacCount_E6_four : ∀ C : Finset (Option (Fin Tag.E6.rank)), C.card = 4 →
    kacCount .E6 ![1, 2, 2, 3, 2, 1] C = 24 → C = {some 1, some 2, some 3, some 4} := by
  decide +kernel

theorem kacCount_F4_four : ∀ C : Finset (Option (Fin Tag.F4.rank)), C.card = 4 →
    kacCount .F4 ![2, 3, 4, 2] C ≠ 24 := by
  decide +kernel

end CFSG.HardMathSupport.Timmesfeld.LangTorus
