module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverMult
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt.SLClosed

@[expose] def ClassicalEvenMultiplierRest : Prop :=
  ∀ (A : Type) [Group A] [Finite A], commutator A = ⊤ → Even (Nat.card (center A)) →
    ((∃ n m : ℕ, 4 ≤ n ∧ StatedClassicalModel (A ⧸ center A) .PSU n 2 m) ∨
      (∃ n m : ℕ, 2 ≤ n ∧ StatedClassicalModel (A ⧸ center A) .PSp n 2 m) ∨
      ∃ n m : ℕ, 4 ≤ n ∧ (StatedClassicalModel (A ⧸ center A) .POmegaPlus n 2 m ∨
        StatedClassicalModel (A ⧸ center A) .POmegaMinus n 2 m)) →
    ¬ Nonempty (A ⧸ center A ≃* alternatingGroup (Fin 8)) →
    ¬ Nonempty (A ⧸ center A ≃* alternatingGroup (Fin 6)) →
      StatedClassicalModel (A ⧸ center A) .PSU 4 2 1 ∨
        StatedClassicalModel (A ⧸ center A) .PSU 6 2 1 ∨
        StatedClassicalModel (A ⧸ center A) .PSp 3 2 1 ∨
        StatedClassicalModel (A ⧸ center A) .POmegaPlus 4 2 1

theorem odd_card_center_of_psl {A : Type} [Group A] [Finite A] (hA : commutator A = ⊤)
    {n m : ℕ} (hn : 4 ≤ n) (h41 : ¬(n = 4 ∧ m = 1))
    (hS : StatedClassicalModel (A ⧸ center A) .PSL n 2 m) : Odd (Nat.card (center A)) := by
  have : Group.IsPerfect A := Group.isPerfect_def.2 hA
  obtain ⟨⟨-, hm, -⟩, K, _, _, hK, ⟨e⟩⟩ := hS
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  let φ := specialLinearGroupEquivStatedSL (k + 1) K
  let q : Matrix.SpecialLinearGroup (Fin (k + 1)) K →* StatedProj (StatedSL (k + 1) K) :=
    (QuotientGroup.mk' _).comp φ.toMonoidHom
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp φ.surjective
  have hker : q.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 1)) K) := by
    ext x
    have h1 : x ∈ q.ker ↔
        φ x ∈ (StatedScalars (Fin (k + 1)) K).subgroupOf (StatedSL (k + 1) K) := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      rfl
    rw [h1, ← map_center_eq_statedScalars]
    exact ⟨fun ⟨y, hy, hxy⟩ => (φ.injective hxy) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hK4 : 4 ≤ Nat.card K ∨ 4 ≤ k := by
    rcases (show k = 3 ∨ 4 ≤ k by omega) with rfl | hk
    · left
      have hm2 : 2 ≤ m := by omega
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    · exact Or.inr hk
  have hsplit : ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin (k + 1)) K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ σ : Matrix.SpecialLinearGroup (Fin (k + 1)) K →* E, ∀ g, π (σ g) = g := by
    intro E _ π hπ hcen
    rcases hK4 with hK4 | hk
    · rcases (show k = 3 ∨ 4 ≤ k by omega) with rfl | hk
      · exact sl_exists_section_of_separating (by norm_num)
          (separating_of_card (by norm_num) (by omega) (by omega) (by omega)) hπ hcen
      · exact sl_exists_section_of_four_le hk hπ hcen
    · exact sl_exists_section_of_four_le hk hπ hcen
  obtain ⟨eM⟩ := sl_hopfMultiplier_mulEquiv_ker_of_split (by omega) hsplit q hq hker.le
  have h1 := CFSG.ComponentClassification.CatFactsSp4.card_center_dvd_hopfMultiplier e
  rw [Nat.card_congr eM.toEquiv, hker] at h1
  have h2 := h1.trans ((card_center_specialLinearGroup_dvd (by omega) K).trans
    (Nat.gcd_dvd_right _ _))
  rw [hK] at h2
  have hodd : Odd (2 ^ m - 1) := by
    have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hev : Even (2 ^ m) := (Nat.even_pow' (by omega)).2 even_two
    obtain ⟨r, hr⟩ := hev
    exact ⟨r - 1, by omega⟩
  exact hodd.of_dvd_nat h2

theorem classicalEvenMultiplier_of_rest (h : ClassicalEvenMultiplierRest) :
    ClassicalEvenMultiplier := by
  intro A _ _ hA ⟨hfam, h8, h6⟩ heven
  rcases hfam with ⟨n, m, hn, hL⟩ | hU | hSp | hO
  · exfalso
    by_cases h41 : n = 4 ∧ m = 1
    · obtain ⟨rfl, rfl⟩ := h41
      exact h8 ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).1
        (Or.inl ⟨by decide, hL⟩))
    · exact Nat.not_even_iff_odd.2 (odd_card_center_of_psl hA hn h41 hL) heven
  · exact h A hA heven (Or.inl hU) h8 h6
  · exact h A hA heven (Or.inr (Or.inl hSp)) h8 h6
  · exact h A hA heven (Or.inr (Or.inr hO)) h8 h6

end CFSG.ComponentClassification.RankTwoClassical
