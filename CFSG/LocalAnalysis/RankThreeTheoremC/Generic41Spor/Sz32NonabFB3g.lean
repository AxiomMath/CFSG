module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32SigOne
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB0

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Part

variable {Y : Type} [Group Y] [Finite Y] {F Γ B R₀ : Subgroup Y} {x : Y} {L : Subgroup Y} {z : Y}

private theorem mem_of_conjNormal_eq_conj [L.Normal]
    (hcent : Subgroup.centralizer (L : Set Y) = ⊥)
    {y : Y} {l : L} (h : MulAut.conjNormal y = MulAut.conj l) : y ∈ L := by
  have hg : ((l : Y))⁻¹ * y ∈ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have key := congrArg (fun φ : MulAut L => ((φ ⟨m, hm⟩ : L) : Y)) h
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at key
    have key' : y * m = (l : Y) * m * (l : Y)⁻¹ * y := by
      rw [← key]
      group
    calc m * ((l : Y)⁻¹ * y) = (l : Y)⁻¹ * ((l : Y) * m * (l : Y)⁻¹ * y) := by group
      _ = (l : Y)⁻¹ * (y * m) := by rw [key']
      _ = (l : Y)⁻¹ * y * m := by group
  rw [hcent, Subgroup.mem_bot] at hg
  have hyl : (l : Y) = y := inv_mul_eq_one.1 hg
  rw [← hyl]
  exact l.2

theorem nf5_not_suzuki (hSz : Sz32Facts) (hSig : Sz32SigOne) (hc : NF5Cfg F Γ B R₀ x L z) :
    ¬ IsoLie ↥L (.suzuki 2) := by
  intro h
  haveI : L.Normal := hc.normal
  have hdata := hc.data
  have hT : IsSz32Type 5 ↥L := by
    unfold IsSz32Type
    exact ⟨rfl, h⟩
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) = 5 :=
    hSz.outer ↥L hT
  have hR_le : R₀ ≤ L := by
    intro y hy
    obtain ⟨k, hk⟩ := hdata.R_two ⟨y, hy⟩
    have hk' : y ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    let φ : Y →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L :=
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)).comp
        (MulAut.conjNormal : Y →* MulAut ↥L)
    have h1 : orderOf (φ y) ∣ 2 ^ k :=
      (orderOf_map_dvd φ y).trans (orderOf_dvd_of_pow_eq_one hk')
    have h2 : orderOf (φ y) ∣ 5 := by
      have := orderOf_dvd_natCard (φ y)
      rwa [hOut] at this
    have hcop : Nat.Coprime (2 ^ k) 5 := Nat.Coprime.pow_left k (by norm_num)
    have h3 : orderOf (φ y) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    have h4 : φ y = 1 := orderOf_eq_one_iff.1 h3
    have hmem : MulAut.conjNormal y ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
      (QuotientGroup.eq_one_iff (MulAut.conjNormal y)).1 h4
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.1
      (show MulAut.conjNormal y ∈ (MulAut.conj : ↥L →* MulAut ↥L).range from hmem)
    exact mem_of_conjNormal_eq_conj hc.cent hl.symm
  have hzB : z ∈ B :=
    (hdata.hB z).2 ⟨hc.zgen.mem, by rw [← hc.zgen.order]; exact pow_orderOf_eq_one z⟩
  have hzN : z ∈ Subgroup.normalizer (R₀ : Set Y) := hdata.R_norm hzB
  have hxord : orderOf (⟨z, hc.zL⟩ : ↥L) = 5 := by
    rw [Subgroup.orderOf_mk]
    exact hc.zgen.order
  have hWcard : Nat.card (R₀.subgroupOf L) = Nat.card R₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR_le).toEquiv
  obtain ⟨n, hn⟩ := (isPGroup_iff_card_dvd_pow).1 hdata.R_two
  have hcop : Nat.Coprime 5 (Nat.card (R₀.subgroupOf L)) := by
    rw [hWcard]
    exact Nat.Coprime.coprime_dvd_right hn (Nat.Coprime.pow_right n (by norm_num))
  have hxN : (⟨z, hc.zL⟩ : ↥L) ∈
      Subgroup.normalizer ((R₀.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro m
    have hm := Subgroup.mem_set_normalizer_iff.1 hzN (m : Y)
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_mk]
    exact hm
  have hWbot : R₀.subgroupOf L = ⊥ :=
    hSig ↥L hT ⟨z, hc.zL⟩ hxord (R₀.subgroupOf L) hcop hxN
  apply hdata.R_ne
  rw [eq_bot_iff]
  intro y hy
  have hmem : (⟨y, hR_le hy⟩ : ↥L) ∈ R₀.subgroupOf L := Subgroup.mem_subgroupOf.2 hy
  rw [hWbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hmem

end Part

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
