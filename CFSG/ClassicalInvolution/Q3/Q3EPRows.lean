module

public import CFSG.ClassicalInvolution.Q3.Q3WAE78Row
public import CFSG.ClassicalInvolution.Q3.Q3EPCtx

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false

@[expose] def E7LayerGeom3 : Prop :=
  LayerGeom (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D)
    (GaloisField 3 1)

@[expose] def E7PartnerToral3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .POmegaPlus 6) (conjClass3 K) z →
      ∀ c : ETCtx3 .POmegaPlus 6 (conjClass3 K) K z, ∀ j : Fin 6 → Subgroup G,
        NodeSystem 3 1 (edgeD 6) (conjClass3 K) K z j →
        (∀ a, locImg (conjClass3 K) z (j a) =
          (rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup a).map c.d.ψ) →
        ∀ β ∈ conjClass3 K, ∀ t : G, IsClassicalMember3 β t →
          (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) →
          Commutes β (j 0) → ∀ ht : t * z * t⁻¹ = z, ToralNormalE3 c ht

@[expose] def E8LayerGeom3 : Prop :=
  LayerGeom (fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Nat.prime_three).D)
    (GaloisField 3 1)

@[expose] def E8PartnerToral3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .E7 0) (conjClass3 K) z →
      ∀ c : ETCtx3 .E7 0 (conjClass3 K) K z, ∀ j : Fin 7 → Subgroup G,
        NodeSystem 3 1 (edgeE 7) (conjClass3 K) K z j →
        (∀ a, locImg (conjClass3 K) z (j a) =
          (rankOne (modelUniv .E7 0 3 1 Nat.prime_three).D.rootGroup a).map c.d.ψ) →
        ∀ β ∈ conjClass3 K, ∀ t : G, IsClassicalMember3 β t →
          (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) →
          Commutes β (j 0) → ∀ ht : t * z * t⁻¹ = z, ToralNormalE3 c ht

section Partner

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ETCtx3.partner_involution_commutes {tY : StatedLieTag} {nY : ℕ}
    (c : ETCtx3 tY nY Ω K z) {β : Subgroup G} {t : G} (htβ : IsClassicalMember3 β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) :
    t * z * t⁻¹ = z := by
  obtain ⟨W, hW⟩ := hKβ
  have hzt : z * t = t * z :=
    Gaps.standardPair_involutions_commute two_ne_zero_gf3 hW c.hz.mem htβ.mem
      c.hz.orderOf_eq_two htβ.orderOf_eq_two
  rw [mul_inv_eq_iff_eq_mul]
  exact hzt.symm

end Partner

@[expose] def PartnerExists3E7Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .POmegaPlus 6) (conjClass3 K) z →
        ∃ j : Fin 6 → Subgroup G, NodeSystem 3 1 (edgeD 6) (conjClass3 K) K z j ∧
          (PartnerAt 3 1 (conjClass3 K) j 4 ∨ PartnerAt 3 1 (conjClass3 K) j 5)

@[expose] def PartnerExists3E8Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .E7 0) (conjClass3 K) z →
        ∃ j : Fin 7 → Subgroup G, NodeSystem 3 1 (edgeE 7) (conjClass3 K) K z j ∧
          PartnerAt 3 1 (conjClass3 K) j 6

section Setup

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem nonempty_etctx3_D6 (h3 : OddThreeFreeInput) (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 1 (CompData.model .POmegaPlus 6) (conjClass3 K) z) :
    Nonempty (ETCtx3 .POmegaPlus 6 (conjClass3 K) K z) := by
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hY := yData3_D6
    (⟨Nat.prime_three, le_rfl, by norm_num⟩ : StatedLieAdmissible .POmegaPlus 6 3 1)
  obtain ⟨hex, hP1⟩ := hR.setup
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dictT hY.sc hR.inClass hK hR.cls hshape
  exact ⟨{
    hΩ := hR.inClass
    hex := hex
    hK := hK
    hz := hR.cls
    hP1 := hP1
    hO3 := h3 G K z hR
    d := d
    hY := hY }⟩

theorem nonempty_etctx3_E7 (h3 : OddThreeFreeInput) (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 1 (CompData.model .E7 0) (conjClass3 K) z) :
    Nonempty (ETCtx3 .E7 0 (conjClass3 K) K z) := by
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hY := yData3_E7 (⟨Nat.prime_three, le_rfl, rfl⟩ : StatedLieAdmissible .E7 0 3 1)
  obtain ⟨hex, hP1⟩ := hR.setup
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dictT hY.sc hR.inClass hK hR.cls hshape
  exact ⟨{
    hΩ := hR.inClass
    hex := hex
    hK := hK
    hz := hR.cls
    hP1 := hP1
    hO3 := h3 G K z hR
    d := d
    hY := hY }⟩

end Setup

theorem chainPiece3E7_of_exists (hP : PartnerExists3E7Input) : ChainPiece3E7 := by
  intro G _ _ _ hnab K z hR hshape
  obtain ⟨j, hj, h45⟩ := hP G hnab K z hR hshape
  rcases h45 with h4 | h5
  · exact chainE7_of_partner hj h4
  · have hj' := hj.comp_equiv (Equiv.swap (4 : Fin 6) 5) edgeD6_swap
    have h5' : PartnerAt 3 1 (conjClass3 K) (j ∘ Equiv.swap (4 : Fin 6) 5) 4 :=
      PartnerAt.comp_equiv (Equiv.swap (4 : Fin 6) 5) (by rwa [Equiv.swap_apply_left])
    exact chainE7_of_partner hj' h5'

theorem chainPiece3E8_of_exists (hP : PartnerExists3E8Input) : ChainPiece3E8 := by
  intro G _ _ _ hnab K z hR hshape
  obtain ⟨j, hj, h6⟩ := hP G hnab K z hR hshape
  exact chainE8_of_partner hj h6

theorem piece3E7_of_exists (h3 : OddThreeFreeInput) (hP : PartnerExists3E7Input) : Piece3E7 :=
  piece3E7_of_chain h3 (chainPiece3E7_of_exists hP)

theorem piece3E8_of_exists (h3 : OddThreeFreeInput) (hP : PartnerExists3E8Input) : Piece3E8 :=
  piece3E8_of_chain h3 (chainPiece3E8_of_exists hP)

end CFSG.ClassicalInvolution.Q3.Q3W
