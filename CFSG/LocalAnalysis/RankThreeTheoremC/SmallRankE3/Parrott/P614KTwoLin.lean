module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
import CFSG.RankThree.PartTwo.KFacts.AutPSL2
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614KTwo

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem isCyclic_outer_psl2 (F : Type) [Field F] [Finite F] [CharP F 2] :
    IsCyclic (Outer PSL(2, F)) := by
  haveI := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
  refine isCyclic_of_surjective ((QuotientGroup.mk' (inner PSL(2, F))).comp
    (CFSG.GorensteinWalter.psl2FieldAut F)) fun a => ?_
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner PSL(2, F)) a
  obtain ⟨g, σ, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.exists_pglAction_mul_psl2FieldAut α
  obtain ⟨x, rfl⟩ := CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.toPGL_surjective F g
  have hx : QuotientGroup.mk' (inner PSL(2, F)) (MulAut.conj x) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨x, rfl⟩
  refine ⟨σ, ?_⟩
  rw [MonoidHom.comp_apply,
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL, map_mul, hx,
    one_mul]

theorem mem_zpowers_mul_of_commute {G : Type*} [Group G] {x y : G} (hxy : Commute x y) {m : ℕ}
    (hm : Odd m) (hx : x ^ m = 1) (hy : y ^ 2 = 1) (k : ℤ) (ε : ℕ) :
    x ^ k * y ^ ε ∈ Subgroup.zpowers (x * y) := by
  obtain ⟨j, rfl⟩ := hm
  have hgy : (x * y) ^ (2 * j + 1) = y := by
    rw [hxy.mul_pow, hx, one_mul, pow_succ, pow_mul, hy, one_pow, one_mul]
  have hgx : (x * y) ^ (2 * j + 1 + 1) = x := by
    rw [hxy.mul_pow, pow_succ x, hx, one_mul, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul,
      hy, one_pow, mul_one]
  have hxz := Subgroup.pow_mem (Subgroup.zpowers (x * y)) (Subgroup.mem_zpowers (x * y))
    (2 * j + 1 + 1)
  have hyz := Subgroup.pow_mem (Subgroup.zpowers (x * y)) (Subgroup.mem_zpowers (x * y))
    (2 * j + 1)
  rw [hgx] at hxz
  rw [hgy] at hyz
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hxz k) (Subgroup.pow_mem _ hyz ε)

theorem gcd_three_two_pow_sub_one {m : ℕ} (hm : Odd m) : Nat.gcd 3 (2 ^ m - 1) = 1 := by
  obtain ⟨j, rfl⟩ := hm
  have h2 : 2 ^ (2 * j + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hpos : 1 ≤ 2 ^ (2 * j + 1) := Nat.one_le_two_pow
  generalize 2 ^ (2 * j + 1) = q at h2 hpos ⊢
  exact Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))

theorem conjAut_mem_inner {F : Type} [Field F] [Finite F] (h3 : Nat.gcd 3 (Nat.card F - 1) = 1)
    (A : GL (Fin 3) F) : LinearFlag.conjAut 3 F A ∈ inner (LinearFlag.projectiveSL 3 F) := by
  obtain ⟨-, hcard⟩ := OuterDerived.linear_diagonal_outer (K := F) (n := 3) (by norm_num)
  rw [h3, Nat.dvd_one, Subgroup.card_eq_one] at hcard
  have hA : QuotientGroup.mk' (inner (LinearFlag.projectiveSL 3 F)) (LinearFlag.conjAut 3 F A) ∈
      ((QuotientGroup.mk' (inner (LinearFlag.projectiveSL 3 F))).comp
        (LinearFlag.conjAut 3 F)).range := ⟨A, rfl⟩
  rw [hcard, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hA
  exact hA

theorem isCyclic_outer_projectiveSL_three {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : Odd m) :
    IsCyclic (Outer (LinearFlag.projectiveSL 3 F)) := by
  have h3 : Nat.gcd 3 (Nat.card F - 1) = 1 := by
    rw [hF]
    exact gcd_three_two_pow_sub_one hm
  obtain ⟨hAut, hcyc⟩ := card_ringAut_and_isCyclic Nat.prime_two F hF
  obtain ⟨φ, hφ⟩ := @IsCyclic.exists_generator (RingAut F) _ hcyc
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := F) (n := 3) le_rfl
  have htrans := LinearFlag.standard_automorphism_transport (K := F) (n := 3)
  have hfd : LinearFlag.fieldAut 3 F φ * LinearFlag.dualAut 3 F =
      LinearFlag.dualAut 3 F * LinearFlag.fieldAut 3 F φ := by
    calc LinearFlag.fieldAut 3 F φ * LinearFlag.dualAut 3 F
        = LinearFlag.dualAut 3 F * LinearFlag.fieldAut 3 F φ * LinearFlag.dualAut 3 F *
            LinearFlag.dualAut 3 F := by rw [htrans.2.2.2.2.2.1]
      _ = LinearFlag.dualAut 3 F * LinearFlag.fieldAut 3 F φ := by
            rw [mul_assoc _ (LinearFlag.dualAut 3 F), htrans.2.2.2.1, mul_one]
  refine isCyclic_iff_exists_zpowers_eq_top.2
    ⟨QuotientGroup.mk' (inner _) (LinearFlag.fieldAut 3 F φ) *
      QuotientGroup.mk' (inner _) (LinearFlag.dualAut 3 F), eq_top_iff.2 fun a _ => ?_⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner (LinearFlag.projectiveSL 3 F)) a
  obtain ⟨A, σ, ε, -, rfl⟩ := hgen α
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hφ σ)
  have hc : QuotientGroup.mk' (inner (LinearFlag.projectiveSL 3 F))
      (LinearFlag.conjAut 3 F A) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact conjAut_mem_inner h3 A
  rw [map_mul, map_mul, hc, one_mul, map_zpow, map_zpow, map_pow]
  refine mem_zpowers_mul_of_commute ?_ hm ?_ ?_ k ε
  · show _ * _ = _ * _
    rw [← map_mul, ← map_mul, hfd]
  · rw [← map_pow, ← map_pow, ← hAut, pow_card_eq_one', map_one, map_one]
  · rw [← map_pow, pow_two, htrans.2.2.2.1, map_one]

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614KTwo
