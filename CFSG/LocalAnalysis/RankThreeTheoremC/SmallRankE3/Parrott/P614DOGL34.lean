module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.RankThree.PartTwo.KFacts.L34Aut
import CFSG.RankThree.Asc83Table.E27
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.GH74.Constrained
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614DOG

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem card_galoisField_two_two : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

noncomputable def pslEquiv : PSL(3, GaloisField 2 2) ≃* projectiveSL 3 (GaloisField 2 2) :=
  QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 (GaloisField 2 2)).symm

theorem card_psl : Nat.card PSL(3, GaloisField 2 2) = 20160 := by
  rw [Nat.card_congr pslEquiv.toEquiv]
  exact CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL card_galoisField_two_two

variable {X : Type*} [Group X] [Finite X] {N : Subgroup X}

theorem card_mulAut_of_equiv (e : ↥N ≃* PSL(3, GaloisField 2 2)) :
    Nat.card (MulAut ↥N) = 241920 := by
  rw [Nat.card_congr (MulAut.congr (e.trans pslEquiv)).toEquiv]
  exact CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut card_galoisField_two_two

theorem pRank_of_equiv (e : ↥N ≃* PSL(3, GaloisField 2 2)) : CFSG.Open.pRank 3 N = 2 := by
  rw [← CFSG.SectionRank.pRank_coe_eq_openPRank,
    CFSG.RankThree.Asc83Table.pRank_congr (e.trans pslEquiv)]
  exact CFSG.RankThree.PartTwo.KFacts.L34.pRank_three_projectiveSL card_galoisField_two_two

theorem eq_one_of_mem_center_of_equiv (e : ↥N ≃* PSL(3, GaloisField 2 2)) {c : X} (hcN : c ∈ N)
    (hc : ∀ n ∈ N, n * c = c * n) : c = 1 := by
  set e' := e.trans pslEquiv
  have hcen : e' ⟨c, hcN⟩ ∈ center (projectiveSL 3 (GaloisField 2 2)) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨n, rfl⟩ := e'.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e' (Subtype.ext (hc n n.2))
  rw [LinearThreeFourOuter.center_projectiveSL_three_eq_bot card_galoisField_two_two,
    mem_bot] at hcen
  have h1 : (⟨c, hcN⟩ : ↥N) = 1 := e'.injective (hcen.trans (map_one e').symm)
  exact congrArg Subtype.val h1

theorem exists_lift_commute {A B : Type*} [Group A] [Finite A] [Group B] (f : A →* B)
    {W : Subgroup A} (hW : ¬ 3 ∣ Nat.card ↥(W ⊓ f.ker)) {d : A} (hdW : d ∈ W)
    (hd : orderOf d = 3) {w : A} (hwW : w ∈ W) (hc : f w * f d = f d * f w) :
    ∃ c ∈ W, c * d = d * c ∧ f c = f w := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O : Subgroup ↥W := f.ker.subgroupOf W with hO
  haveI : O.Normal := (MonoidHom.normal_ker f).subgroupOf W
  have hcard : Nat.card O = Nat.card ↥(W ⊓ f.ker) := by
    rw [hO, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hOc : Nat.Coprime 3 (Nat.card O) := by
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW
  have ht : ∃ k : ℕ, orderOf (⟨d, hdW⟩ : ↥W) = 3 ^ k :=
    ⟨1, by rw [Subgroup.orderOf_mk, hd, pow_one]⟩
  have hC := CFSG.GH74.centralizer_singleton_quotient_eq_map 3 O hOc ht
  have hmem : QuotientGroup.mk' O ⟨w, hwW⟩ ∈
      centralizer ({QuotientGroup.mk' O ⟨d, hdW⟩} : Set (↥W ⧸ O)) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq, hO, mem_subgroupOf, MonoidHom.mem_ker]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [hc]
    group
  rw [hC] at hmem
  obtain ⟨c', hc', hc'eq⟩ := hmem
  refine ⟨c', c'.2, congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc'), ?_⟩
  have h1 : c'⁻¹ * ⟨w, hwW⟩ ∈ O := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hc'eq
    exact hc'eq
  rw [hO, mem_subgroupOf, MonoidHom.mem_ker] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] at h1
  calc f c' = f c' * ((f c')⁻¹ * f w) := by rw [h1, mul_one]
    _ = f w := by group

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614DOG
