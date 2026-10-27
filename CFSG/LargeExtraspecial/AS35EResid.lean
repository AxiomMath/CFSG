module

public import CFSG.LargeExtraspecial.AS35EDSet
public import CFSG.LargeExtraspecial.AS35DSixOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

structure SixHyp : Prop where
  three_le_width : 3 ≤ S.width
  weak : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z
  zInOTwo : ∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t
  simple : IsSimpleGroup S.zGen
  centralizer_eq : centralizer (S.zGen : Set G) = ⊥
  sup_eq_top : S.zGen ⊔ S.QG = ⊤
  hSet_nonempty : ∃ H : Subgroup G, S.IsHSet H
  sixFour : S.SixFourConcl

@[expose] noncomputable def DbarAsc : Set S.O :=
  {σ | ∃ t ∈ S.DSet, ∃ ht : t ∈ S.M, S.ρ ⟨t, ht⟩ = σ}

@[expose] def FourStruct : Prop :=
  ∃ J : S.Qt ≃ₗ[ZMod 2] S.Qt, (∀ v, J (J v) + J v + v = 0) ∧ (∀ v, S.q (J v) = S.q v) ∧
    (∀ a ∈ S.DbarAsc, ∀ v,
      (a : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((a : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) ∧
    ∀ m ∈ S.Mbar,
      (∀ v, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) ∨
        ∀ v, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J (J ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) v))

structure SixFiveConcl : Prop where
  four_le_width : 4 ≤ S.width
  psu : Nonempty (closure S.DbarAsc ⧸ center (closure S.DbarAsc) ≃* CFSG.Open.timmesfeldPSU S.width)
  pbar_le : ∀ g : G, g * S.z * g⁻¹ ∈ S.DSet →
    ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ ≤ closure S.DbarAsc
  fstar_card : Nat.card (CFSG.generalizedFitting (S.Mbar ⊓ centralizer S.DbarAsc : Subgroup S.O))
    ≤ 3
  three : ∀ a ∈ S.DbarAsc, ∀ b ∈ S.DbarAsc, orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ)
  disjoint : ∀ a ∈ S.DbarAsc, ∀ b ∈ S.DbarAsc, a * b = b * a → a ≠ b →
    commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥
  conj : ∀ a ∈ S.DbarAsc, ∀ b ∈ S.DbarAsc, ∃ g ∈ closure S.DbarAsc, g * a * g⁻¹ = b
  exists_commute : ∀ a ∈ S.DbarAsc, ∃ b ∈ S.DbarAsc, b ≠ a ∧ a * b = b * a
  fourStruct : S.FourStruct

@[expose] def BAt (g : G) : Set G := {b | ∃ k : G, k * S.z * k⁻¹ ∈ S.DAt g ∧ b ∈ S.DAt k}

abbrev BSet : Set G := S.BAt 1

end Setting

namespace S14

@[expose] def AschbacherSixNineStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), AschbacherBelow (Nat.card G) →
    S.SixHyp → S.SixFiveConcl → ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g ⊆ S.BSet

@[expose] def AschbacherSixElevenStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), AschbacherBelow (Nat.card G) →
    S.SixHyp → S.SixFiveConcl →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g = S.BSet) →
    (∀ a ∈ S.BSet, ∀ b ∈ S.BSet, orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ)) →
      ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet

end S14

open CFSG.Blueprint.Fischer (K)
open CFSG.Fischer.Classification.Unitary

theorem kLI : LinearIndependent (ZMod 2) ![1, ω] := by
  rw [linearIndependent_fin2]
  constructor
  · exact omega_ne_zero
  · intro a
    have ha : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases ha a with rfl | rfl
    · rw [Algebra.smul_def, map_zero, zero_mul]; exact zero_ne_one
    · rw [Algebra.smul_def, map_one, one_mul]; exact omega_ne_one

theorem kSpan : Submodule.span (ZMod 2) (Set.range ![1, ω]) = ⊤ := by
  refine Submodule.eq_top_of_finrank_eq ?_
  have h1 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (Set.range ![1, ω])) = 2 := by
    rw [finrank_span_eq_card (b := ![1, ω]) kLI, Fintype.card_fin]
  have h2 : Module.finrank (ZMod 2) K = 2 := by
    have h := GaloisField.finrank (p := 2) (n := 2) (by norm_num)
    exact h
  rw [h1, h2]

noncomputable def kBasis : Module.Basis (Fin 2) (ZMod 2) K :=
  Module.Basis.mk (v := ![1, ω]) kLI (le_of_eq kSpan.symm)

@[simp] theorem kBasis_zero : kBasis 0 = (1 : K) := by
  rw [kBasis, Module.Basis.mk_apply]; rfl

@[simp] theorem kBasis_one : kBasis 1 = ω := by
  rw [kBasis, Module.Basis.mk_apply]; rfl

@[simp] theorem kBasis_repr_one : kBasis.repr (1 : K) = Finsupp.single 0 1 := by
  conv_lhs => rw [← kBasis_zero]
  rw [Module.Basis.repr_self]

@[simp] theorem kBasis_repr_omega : kBasis.repr ω = Finsupp.single 1 1 := by
  conv_lhs => rw [← kBasis_one]
  rw [Module.Basis.repr_self]

end CFSG.LargeExtraspecial
