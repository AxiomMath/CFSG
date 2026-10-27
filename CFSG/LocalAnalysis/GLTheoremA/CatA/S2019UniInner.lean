module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalParts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Quadratic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019UniBlocks
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalReduce
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019LinInner
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem s2019UniInner_five : S2019UniInner (5 ≤ ·) := by
  intro p q hp hp2 hq hq2 hqp hq5 f K _ h n A c hA L hL T hT2 hLT
  classical
  haveI := h.finite
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP K q := h.charP
  have hq' : 2 ≤ q ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  have hpq : p ≠ q := Ne.symm hqp
  have hperf : ⁅L, L⁆ = L := glaPComponent_perfect hL
  have hle := perfectInLayer_primeFormConjHom h hp hpq A hA L hL.1 hperf
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hL hle
  have H := primaryData_toLin' h A.2 hp hpq hA
  obtain ⟨⟨a, hgood⟩, hLeq⟩ := exists_good_primaryFactor_of_component hq' A rfl H L hcomp
  set SB := specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
    (a : K[X]) with hSB
  set F : Subgroup ↥(gramSU h (idGram K n)) := SB.comap (toLinSU h n) with hF
  set π := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) with hπ
  have hSBle : SB ≤ (toLinSU h n).range := fun y hy =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq' a hgood hy)
  have hFmap : F.map (toLinSU h n) = SB := Subgroup.map_comap_eq_self hSBle
  have hfacts := specialBlockFacts_of_good H hq' a hgood
  have hFperf : ⁅F, F⁆ = F := by
    apply Subgroup.map_injective (toLinSU_injective (h := h) (n := n))
    rw [Subgroup.map_commutator, hFmap]
    exact Subgroup.isPerfect_iff.mp (hfacts.quasisimple hgood.1).1
  obtain ⟨g, hg, hg2, hns⟩ := exists_quadratic_specialBlock H a hgood.1
  obtain ⟨u, hu⟩ := hSBle hg
  have huF : u ∈ F := by
    rw [hF, Subgroup.mem_comap, hu]
    exact hg
  have huL : π u ∈ L := by
    rw [hLeq]
    exact Subgroup.mem_map_of_mem _ huF
  have huq : u ^ q = 1 := by
    apply toLinSU_injective (h := h) (n := n)
    rw [map_pow, map_one, hu]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact pow_char_eq_one_of_sq_sub_one_eq_zero (F := K) hg2
  have hu2 : (((toLinSU h n u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) - 1) ^ 2 = 0 := by
    rw [hu]
    exact hg2
  have huZ : ∃ j ∈ L, j * π u ≠ π u * j := by
    by_contra hcon
    push Not at hcon
    have hZ : ⁅Subgroup.zpowers u, F⁆ ≤ Subgroup.center ↥(gramSU h (idGram K n)) := by
      have h1 : (⁅Subgroup.zpowers u, F⁆).map π = ⊥ := by
        rw [Subgroup.map_commutator, MonoidHom.map_zpowers, ← hLeq,
          Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le,
          Subgroup.mem_centralizer_iff]
        exact hcon
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at h1
      exact h1.trans (normOneScalars_le_center h _ n)
    have h0 := commutator_eq_bot_of_le_center hFperf hZ
    have hcommF : ∀ s ∈ F, s * u = u * s := by
      intro s hs
      have h2 := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers u) hs
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2.symm
    have hcomm : ∀ y ∈ SB, Commute g y := by
      intro y hy
      obtain ⟨s, hs⟩ := hSBle hy
      have hsF : s ∈ F := by
        rw [hF, Subgroup.mem_comap, hs]
        exact hy
      show g * y = y * g
      rw [← hu, ← hs, ← map_mul, ← map_mul, hcommF s hsF]
    exact hns (hfacts.scalar g (specialBlock_le_unitaryCentralizer hg) fun _ y hy => hcomm y hy)
  have hTq : ∀ t ∈ T, ¬ q ∣ orderOf t := by
    intro t ht hdvd
    obtain ⟨j, hj⟩ := hT2 ⟨t, ht⟩
    have h1 : orderOf t ∣ 2 ^ j := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hj
      simpa using this
    have h2 : q ∣ 2 := hq.dvd_of_dvd_pow (hdvd.trans h1)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h2)
  have hkerq : ∀ s ∈ π.ker, ¬ q ∣ orderOf s := by
    intro s hs hdvd
    rw [hπ, QuotientGroup.ker_mk'] at hs
    obtain ⟨c', -, -, hc'⟩ := hs
    have hs1 : s ^ Nat.card Kˣ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hc', ← map_pow, pow_card_eq_one', map_one, Subgroup.coe_one]
    have h1 : q ∣ Nat.card Kˣ := hdvd.trans (orderOf_dvd_of_pow_eq_one hs1)
    rw [Nat.card_units] at h1
    have h2 : q ∣ Nat.card K := by
      rw [h.card]
      exact dvd_pow_self q (by have := h.one_le; omega)
    have h3 : q ∣ 1 := by
      have := Nat.dvd_sub h2 h1
      rwa [Nat.sub_sub_self (Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne')] at this
    exact hq.one_lt.ne' (Nat.dvd_one.1 h3)
  exact commutator_eq_bot_of_quadratic_lift hq5 hcomp.2.2 hLT hTq π
    (QuotientGroup.mk'_surjective _) hkerq (toLinSU h n) (toLinSU_injective (h := h) (n := n))
    huL huZ huq hu2

end CFSG.LocalAnalysis.GLTheoremA.S2019
