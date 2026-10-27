module

public import CFSG.ClassicalInvolution.Asc77.SU4ThreeModel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3TPCtx
public import CFSG.ClassicalInvolution.RouteD.TwinYStatements

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.RouteD.SU4Pattern
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

@[expose] def TauLinear3 {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}
    (c : Q3TP.TCtxS3 .PSU 4 Ω K z) {t : G} (ht : t * z * t⁻¹ = z) : Prop :=
  ∃ φ : (modelUniv .PSU 4 3 1 Nat.prime_three).K ≃* Su (GaloisField 3 (2 * 1)) 3 1 4,
    (∀ R : Subgroup (modelUniv .PSU 4 3 1 Nat.prime_three).K,
      R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D ↔
        R.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
          (by norm_num : 2 ≤ 4)) ∧
      LinearLift (c.d.ψ.comp φ.symm.toMonoidHom) (Gaps.locAut c.hΩ.conjInvariant ht)

@[expose] def TwinSU4Linear3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model .PSU 4) (conjClass3 K) z →
      ∀ c : Q3TP.TCtxS3 .PSU 4 (conjClass3 K) K z,
        ∀ (N K₂ : Subgroup G) (t : G), N ∈ conjClass3 K → IsClassicalMember3 N t →
          K₂ ∈ centralizingMembers (conjClass3 K) {z} → K₂ ≠ K →
          (∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → K₂ ≠ T) →
          Commutes K K₂ → (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K N) →
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W N K₂) →
          ∀ ht : t * z * t⁻¹ = z, TauLinear3 c ht

end CFSG.ClassicalInvolution.Q3.Q3P21
