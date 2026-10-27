module

public import Certificates.Certificate6123
public import Certificates.Certificate6124
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Cent
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Outer

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification
open scoped commutatorElement

theorem centralizer_V_le_of_certificate
    {G : Type*} [Group G] [Finite G] {A V : Subgroup G}
    (hA : commutator ↥A = ⊤)
    (e : ↥A ⧸ center ↥A ≃* ↥PSL3Four.S) (hV : IsSylowOf 2 V A) :
    normalizer (A : Set G) ⊓ centralizer (V : Set G) ≤
      (V ⊓ centralizer (V : Set G)) ⊔ centralizer (A : Set G) :=
  centralizer_V_le hA e hV Certificates.certificate6123

theorem outer_involution_cases_of_certificate
    {G : Type*} [Group G] {B : Subgroup G}
    (hB : commutator ↥B = ⊤) (hZ : Odd (Nat.card (center ↥B)))
    (e : ↥B ⧸ center ↥B ≃* ↥PSL3Four.S) {y : G} (hy : y ∈ normalizer (B : Set G))
    (hy2 : y * y = 1) (hout : y ∉ B ⊔ centralizer (B : Set G)) :
    (∀ c ∈ B ⊓ centralizer ({y} : Set G), c * c = 1 → ∃ b ∈ B, b * y * b⁻¹ = y * c) ∧
      (Group.IsSolvable ↥(B ⊓ centralizer ({y} : Set G)) ∨
        (IsSimpleGroup ↥(centralizerBar B y) ∧
          (∃ a b : ↥(centralizerBar B y), a * b ≠ b * a) ∧
          (Nat.card ↥(centralizerBar B y) = 60 ∨ Nat.card ↥(centralizerBar B y) = 168))) :=
  outer_involution_cases hB hZ e Certificates.certificate6124 hy hy2 hout

theorem exists_perfect_involution_of_outer_of_certificate
    {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (hB : commutator ↥B = ⊤) (hZ : Odd (Nat.card (center ↥B)))
    (e : ↥B ⧸ center ↥B ≃* ↥PSL3Four.S) {y : G} (hy : y ∈ normalizer (B : Set G))
    (hy2 : y * y = 1) (hout : y ∉ B ⊔ centralizer (B : Set G))
    (hns : ¬ Group.IsSolvable ↥(B ⊓ centralizer ({y} : Set G))) :
    ∃ D : Subgroup G, D ≤ B ⊓ centralizer ({y} : Set G) ∧ ⁅D, D⁆ = D ∧
      ∃ c ∈ D, c * c = 1 ∧ c ≠ 1 :=
  exists_perfect_involution_of_outer hB hZ e Certificates.certificate6124 hy hy2 hout hns

end CFSG.OddStandard.Seitz77
