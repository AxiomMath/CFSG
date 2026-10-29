module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217ALe
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217FrameE

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic

theorem nonCentral_of_card_centralizer {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 50232960) {x : Q} (hx : Nat.card (centralizer ({x} : Set Q)) = 1080) :
    NonCentral 3 x := by
  intro S hxS
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card Q).factorization 3 = 5 := by
    rw [hQ, show (50232960 : ℕ) = 3 ^ 5 * 206720 by norm_num]
    exact CFSG.RankThree.PartOne.factorization_pow_mulG Nat.prime_three (by norm_num)
  have hS : Nat.card S = 243 := by
    rw [Sylow.card_eq_multiplicity, hfac]; norm_num
  have hle : (S : Subgroup Q) ≤ centralizer ({x} : Set Q) := by
    intro s hs
    obtain ⟨z, hz, hzx⟩ := hxS
    rw [mem_centralizer_singleton_iff]
    have := Subgroup.mem_center_iff.1 hz ⟨s, hs⟩
    have h2 := congrArg Subtype.val this
    rw [← hzx]
    exact h2
  have := Subgroup.card_dvd_of_le hle
  rw [hS, hx] at this
  norm_num at this

section Main

variable {G : Type} [Group G] [Finite G]


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem sec217Frame_of (h45 : Sec4.Item4_5) : Sec217Frame (G := G) := by
  intro A E U c L h
  have hAL : A ≤ L := sec217ALe_of h45 A E U c L h
  have hθ := sec217ThetaOne_holds A E U c L h
  obtain ⟨hq, hZ3⟩ := h.quasi_card_center hθ
  obtain ⟨e⟩ := h.quot
  have hpairs := mem_lThreeStarPairs_iff.mp h.pair.mem_pair
  have hEA : E ≤ A := h.pair.mem_E.2
  have hcE : c ∈ E := hpairs.1.1
  have hEL : E ≤ L := hEA.trans hAL
  have hE27 : Nat.card E = 27 := h.pair.mem_E.1.2.1
  obtain ⟨hEN, hUea, hU4⟩ := mem_fourGroups_iff.1 h.pair.mem_U
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := (isElemAbelian_iff.1 hUea).2
  have hUN : U ≤ Subgroup.normalizer (L : Set G) := hpairs.2.2.2.1
  have hLU : ⁅L, U⁆ = L := hpairs.2.2.2.2.2.1
  have hEU : ∀ x ∈ E, ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
    intro x hx u hu
    exact ((Subgroup.mem_normalizer_iff.1 (hEN hx)) u).1 hu
  set F : Subgroup ↥L := A.subgroupOf L with hF
  have hF81 : Nat.card F = 81 := by
    rw [hF, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, h.card]
    norm_num
  have hcen := h.center_eq hθ
  have hZF : Subgroup.center ↥L ≤ F := by
    rw [hcen, Subgroup.zpowers_le]
    exact Subgroup.mem_subgroupOf.2 h.c_mem_A
  have hab := h.isElemAbelian_A
  haveI : IsMulCommutative A := hab.1
  have hFel : CFSG.IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (Subgroup.center ↥L))) := by
    have hFE : CFSG.IsElementaryAbelian 3 F := by
      rw [← isElemAbelian_iff_isElementaryAbelian]
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · apply Subtype.ext
        apply Subtype.ext
        have hc := mul_comm' (⟨((a : ↥L) : G), Subgroup.mem_subgroupOf.1 a.2⟩ : A)
          ⟨((b : ↥L) : G), Subgroup.mem_subgroupOf.1 b.2⟩
        have := congrArg Subtype.val hc
        exact this
      · exact Subtype.ext (hab.2 (x : G) (Subgroup.mem_subgroupOf.1 hx))
    exact CFSG.RankThree.Asc83Table.IsElementaryAbelian.map_hom _ hFE
  obtain ⟨F₁, hZF₁, hF₁F, hF₁27, -, -, h3A, h3B⟩ :=
    exists_F1_of_class hZ3 e hFel hZF hF81
  have hFcube : ∀ x ∈ F, x ^ 3 ∈ Subgroup.center ↥L := by
    intro x hx
    have := (CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.1 hFel).2 _ ⟨x, hx, rfl⟩
    rw [← QuotientGroup.ker_mk' (Subgroup.center ↥L), MonoidHom.mem_ker, map_pow]
    exact this
  have hEF : ∀ a : ↥L, (a : G) ∈ E → a ∈ F := fun a ha => Subgroup.mem_subgroupOf.2 (hEA ha)
  obtain ⟨a, haE, haF₁⟩ : ∃ a : ↥L, (a : G) ∈ E ∧ a ∉ F₁ := by
    by_contra hno
    push Not at hno
    refine false_of_pure3B hq hZ3 (e.trans Item228CensusProof.j3CarrierEquiv) hEL ?_ hE27
      (fun x hx => hFcube x (hEF x hx)) (fun x hx hxc => h3B x (hno x hx) hxc) hUN hU4 hU2 hEU hLU
    intro z hz
    rw [hcen] at hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have : ((⟨c, h.mem⟩ : ↥L) ^ i : ↥L) = ⟨c, h.mem⟩ ^ i := rfl
    rw [Subgroup.coe_zpow]
    exact Subgroup.zpow_mem _ hcE i
  have haF : a ∈ F := hEF a haE
  have hanc : a ∉ Subgroup.center ↥L := fun hc => haF₁ (hZF₁ hc)
  refine ⟨(a : G), ⟨haE, ?_, ⟨a, ⟨1, one_mem _, by simp⟩, ?_⟩⟩⟩
  · intro hmem
    apply hanc
    rw [hcen]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨i, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow]
    exact hi
  · have h5 := h3A a haF haF₁
    have hx3 : (a : ↥L ⧸ Subgroup.center ↥L) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 (hFcube a haF)
    have hx1 : (a : ↥L ⧸ Subgroup.center ↥L) ≠ 1 := fun h1 =>
      hanc ((QuotientGroup.eq_one_iff a).1 h1)
    have hC := card_centralizer_of_equiv_J3 e hx3 hx1 h5
    have hQ : Nat.card (↥L ⧸ Subgroup.center ↥L) = 50232960 := by
      rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.J3.card_J3
    exact nonCentral_of_card_centralizer hQ hC

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
