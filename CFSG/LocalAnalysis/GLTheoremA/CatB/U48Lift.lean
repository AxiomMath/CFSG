module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G]

theorem exists_cent_lift_outer {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1) (x : ↥L)
    (hx : (QuotientGroup.mk (conjL L b hb x) : PQuot 3 L) = QuotientGroup.mk x) :
    ∃ x' : ↥L, (x' : G) * b = b * (x' : G) ∧
      (QuotientGroup.mk x' : PQuot 3 L) = QuotientGroup.mk x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := GLAPPrimeCoreOf 3 L with hN
  set H : Subgroup G := L ⊔ Subgroup.zpowers b with hH
  have hLH : L ≤ H := le_sup_left
  have hbH : b ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hNL : N ≤ L := Subgroup.map_subtype_le _
  have hNnorm : H ≤ Subgroup.normalizer (N : Set G) := by
    refine sup_le (le_normalizer_glaPPrimeCoreOf 3 L) ?_
    rw [Subgroup.zpowers_le]
    exact normalizer_le_normalizer_primeCoreOf 3 L hb
  haveI hNormal : (N.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (hNnorm g.2) (n : G)).1 hn
    exact h1
  let π : ↥H →* ↥H ⧸ N.subgroupOf H := QuotientGroup.mk' _
  have hker : ¬ 3 ∣ Nat.card π.ker := by
    rw [QuotientGroup.ker_mk', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNL.trans hLH)).toEquiv]
    exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three L
  let z : ↥H := ⟨b, hbH⟩
  have hz : z ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  let xH : ↥H := ⟨x, hLH x.2⟩
  have hc : π xH * π z = π z * π xH := by
    rw [← map_mul, ← map_mul]
    show (QuotientGroup.mk (xH * z) : ↥H ⧸ N.subgroupOf H) = QuotientGroup.mk (z * xH)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := (QuotientGroup.eq (s := GLAPPrimeCore 3 ↥L)).1 hx
    have h2 := (mem_primeCoreOf_iff _).2 h1
    convert h2 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjL_apply, mul_inv_rev, inv_inv]
    have hzb : (z : G) = b := rfl
    have hxx : (xH : G) = x := rfl
    rw [hzb, hxx]
    group
  obtain ⟨h', hh'z, hh'π⟩ := exists_mem_centralizer_lift Nat.prime_three π hker hz
    (MonoidHom.mem_range.2 ⟨xH, rfl⟩) hc
  have h3 : xH⁻¹ * h' ∈ N.subgroupOf H := (QuotientGroup.eq).1 hh'π.symm
  rw [Subgroup.mem_subgroupOf] at h3
  have h4 : ((x : G))⁻¹ * (h' : G) ∈ N := by simpa using h3
  have h5 : (h' : G) ∈ L := by
    have : (h' : G) = (x : G) * ((x : G)⁻¹ * (h' : G)) := by group
    rw [this]
    exact L.mul_mem x.2 (hNL h4)
  refine ⟨⟨h', h5⟩, ?_, ?_⟩
  · have := congrArg Subtype.val hh'z
    simpa using this
  · rw [QuotientGroup.eq, ← mem_primeCoreOf_iff]
    have : (((⟨h', h5⟩⁻¹ * x : ↥L)) : G) = ((x : G)⁻¹ * h')⁻¹ := by simp
    rw [this]
    exact N.inv_mem h4

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48
