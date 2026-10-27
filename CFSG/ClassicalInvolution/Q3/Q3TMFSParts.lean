module

public import CFSG.ClassicalInvolution.Q3.Q3TMFSCases
public import CFSG.ClassicalInvolution.Q3.Q3TMFSMember
public import CFSG.ClassicalInvolution.Q3.Q3TMFSBalance
public import CFSG.ClassicalInvolution.Q3.Q3TMFSDatum
public import CFSG.ClassicalInvolution.Q3.Q3TMFSSmall
public import CFSG.ClassicalInvolution.Q3.TL3Weak
public import CFSG.ClassicalInvolution.Q3.Q3TKStmt

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T.MFS

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance CFSG.GH74.GLS.Balance
open CFSG.ClassicalInvolution.Q3.Q3T

section Base


@[expose] def TightHasMember3LargeBelow : Prop :=
  ∀ n : ℕ, CIT3Below n → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    Nat.card G < n → (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
    R ≤ Subgroup.centralizer ({t} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal →
    IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) →
    ∃ (z : G) (J : Subgroup G), IsClassicalMember3 J z

theorem _root_.CFSG.ClassicalInvolution.Q3.TightHasMember3Large.below
    (h : TightHasMember3Large) : TightHasMember3LargeBelow :=
  fun _ _ G _ _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2 =>
    h G hnab hlarge R S hS t ht hto hRC hRn h2

@[expose] def ResidualCNormal : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) →
    ∀ (z : Y) (L T : Subgroup Y), Setting z L T →
      (∀ (z' : T) (L' : Subgroup T), ¬ IsClassicalMember3 L' z') → memberIndex L T = 3 →
      ∀ Q : Sylow 2 L, QOddNormalInT z L T Q → False

theorem residualCNormal_of_parts (hlarge : TightHasMember3LargeBelow) (hsmall : SmallRangeOuter) :
    ResidualCNormal := by
  intro Y _ _ hB z L T hS hfree hC Q hQ
  obtain ⟨hsimp, hnab, R, S, t, hD⟩ := typeCNormalDatum_proved Y z L T hS hC Q hQ
  have : T.Normal := hS.normal
  obtain ⟨-, h3⟩ := odd_index_of_memberIndex_eq_three hS.sup hC
  have hlt : Nat.card T < Nat.card Y := by
    have hmul := T.card_mul_index
    have hpos : 0 < Nat.card T := Nat.card_pos
    have hidx : 3 ≤ T.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h3
    nlinarith
  by_cases hF : TwoSubgroupsFourGenerated (genFittingFStar ↥T)
  · exact hsmall Y T hsimp hnab hS.cent hF hfree h3 ⟨R, S, t, hD⟩
  · obtain ⟨hFs, hFnab⟩ := genFittingFStar_simple ↥T hnab
    obtain ⟨z', J, hJ⟩ := hlarge (Nat.card Y) hB ↥T hlt hFnab hF R S hD.quat t hD.mem hD.order
      hD.cent hD.normal hD.twoGroup
    exact hfree z' J hJ

@[expose] def ResidualCFrame : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) →
    ∀ (z : Y) (L T : Subgroup Y), Setting z L T →
      (∀ (z' : T) (L' : Subgroup T), ¬ IsClassicalMember3 L' z') → memberIndex L T = 3 →
      (∀ Q : Sylow 2 L, ¬ QOddNormalInT z L T Q) → False

theorem memberFreeSocleOuter3_of_residualC (hbal : SolvableL2PrimeBalance)
    (hnormal : ResidualCNormal) (hframe : ResidualCFrame) : MemberFreeSocleOuter3 := by
  intro Y _ _ hB hO z L hz T hT hTL hgen hconn hTn hTz hfree
  have hS : Setting z L T := ⟨hO, hz, hT, hTL, hgen, hconn, hTn, hTz⟩
  have : T.Normal := hTn
  rcases memberIndex_cases (T := T) hz with h | h | h | h
  · have hmem := isClassicalMember3_inf_of_memberIndex_eq_one hz hTL h
    exact hfree _ _ (hmem.subgroupOf (inf_le_right : L ⊓ T ≤ T))
  · by_cases hn : ∃ Q : Sylow 2 L, QOddNormalInT z L T Q
    · obtain ⟨Q, hQ⟩ := hn
      exact hnormal Y hB z L T hS hfree h Q hQ
    · push Not at hn
      exact hframe Y hB z L T hS hfree h hn
  · exact typeABExcluded_of_solvBalance hbal Y z L T hS (Or.inl h)
  · exact typeABExcluded_of_solvBalance hbal Y z L T hS (Or.inr h)

theorem memberFreeSocleOuter3_of_parts (hbal : SolvableL2PrimeBalance)
    (hlarge : TightHasMember3LargeBelow) (hsmall : SmallRangeOuter) (hframe : ResidualCFrame) :
    MemberFreeSocleOuter3 :=
  memberFreeSocleOuter3_of_residualC hbal (residualCNormal_of_parts hlarge hsmall) hframe

theorem residualCNormal_of_normalOdd (hN : NormalOddByQuaternion) (hodd : OddLieTightMember) :
    ResidualCNormal := by
  intro Y _ _ _ z L T hS hfree hC Q hQ
  obtain ⟨hsimp, hnab, R, S, t, hD⟩ := typeCNormalDatum_proved Y z L T hS hC Q hQ
  have : T.Normal := hS.normal
  obtain ⟨-, h3⟩ := odd_index_of_memberIndex_eq_three hS.sup hC
  obtain ⟨hFs, hFnab⟩ := genFittingFStar_simple ↥T hnab
  rcases hN ↥T hFnab R S hD.quat t hD.mem hD.order hD.cent hD.normal hD.twoGroup trivial with
    h | h | h
  · obtain ⟨z', J, hJ⟩ := hodd ↥T hFnab h R S hD.quat t hD.mem hD.order hD.cent hD.normal
      hD.twoGroup
    exact hfree z' J hJ
  · exact false_of_sporadic_of_three_dvd_index T hnab hsimp hS.cent h3 (Or.inl h)
  · exact false_of_sporadic_of_three_dvd_index T hnab hsimp hS.cent h3 (Or.inr h)

theorem memberFreeSocleOuter3_of_normalOdd (hbal : SolvableL2PrimeBalance)
    (hN : NormalOddByQuaternion) (hodd : OddLieTightMember) (hframe : ResidualCFrame) :
    MemberFreeSocleOuter3 :=
  memberFreeSocleOuter3_of_residualC hbal (residualCNormal_of_normalOdd hN hodd) hframe

end Base

section Gh74

theorem memberFreeSocleOuter3_of_gh74 (hbal : SolvableL2PrimeBalance) (hGH : GH74SectionalModels)
    (hlarge : TightHasMember3LargeBelow) (hodd : SmallOddLieTightMember)
    (hframe : ResidualCFrame) : MemberFreeSocleOuter3 :=
  memberFreeSocleOuter3_of_parts hbal hlarge (smallRangeOuter_of_parts hGH hodd) hframe

end Gh74

end CFSG.ClassicalInvolution.Q3.Q3T.MFS
