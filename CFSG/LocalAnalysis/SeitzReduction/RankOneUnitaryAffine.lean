module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryAffineModel
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageChainHKS

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis AffineModel

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Certificates


theorem regularNormal_or_projective_of_affineModel {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V} {t : V} {n : ℕ} (hn : 3 ≤ n)
    (hU : Nat.card U = 2 ^ n) (hUt : IsCompl U (zpowers t)) {M H : Subgroup (MulAut V)}
    (hMU : ∀ m ∈ M, ∀ u ∈ U, m u ∈ U) (hHM : H ≤ M) (hHt : ∀ h ∈ H, h t = t)
    (hHn : ∀ m ∈ M, m t = t → ∀ h ∈ H, m * h * m⁻¹ ∈ H) (hHc : IsCyclic H)
    (hHreg : ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃! h : H, (h : MulAut V) u = v)
    (hcat : NonabelianSimpleNormalCatalog (orbitImage M t)) :
    HasRegularNormalSubgroup (orbitImage M t) ∨ (n = 3 ∧ IsProjectiveEight (orbitImage M t)) :=
  regularNormal_or_projective_of_affineModel_of_input smallRootRegularNormalInput hV hn hU hUt
    hMU hHM hHt hHn hHc hHreg hcat

end Certificates

end CFSG.SeitzReduction.RankOne
