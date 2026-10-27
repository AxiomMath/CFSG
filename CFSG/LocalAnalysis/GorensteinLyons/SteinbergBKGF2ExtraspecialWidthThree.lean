module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2CoreNoCyclicIndexTwo
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCGWidthOneTwoRank
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCGWidthTwoFourGenerated
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)

namespace SteinbergBK

theorem isElemAbelian_subgroupOf_of_le {G : Type*} [Group G] {p : ℕ} {E K : Subgroup G}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.subgroupOf K) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE K

theorem zpowers_coe_eq_of_generator {X : Type*} [Group X] {H : Subgroup X} {g : H}
    (hg : ∀ h : H, h ∈ zpowers g) : zpowers (g : X) = H := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact zpow_mem g.2 n
  · intro hx
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    refine ⟨n, ?_⟩
    change (g : X) ^ n = x
    rw [← Subgroup.coe_zpow, hn]

theorem card_frattini_quotient_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (X ⧸ frattini X) = Nat.card (Y ⧸ frattini Y) := by
  have hf : (frattini X).map e.toMonoidHom = frattini Y :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  exact Nat.card_congr (QuotientGroup.congr (frattini X) (frattini Y) e hf).toEquiv

theorem exists_conj_le_of_isSylowOf_top {G : Type*} [Group G] [Finite G] {S P : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hP : IsPGroup 2 P) :
    ∃ g : G, P.map (MulAut.conj g).toMonoidHom ≤ S := by
  have := Fact.mk Nat.prime_two
  obtain ⟨-, hS2, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hS
  rw [relIndex_top_right] at hidx
  set R : Sylow 2 G := hS2.toSylow hidx with hR
  obtain ⟨R', hR'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R' R
  refine ⟨g, ?_⟩
  have h1 : ((g • R' : Sylow 2 G) : Subgroup G) = S := by rw [hg, hR, IsPGroup.toSylow_coe]
  rw [Sylow.coe_subgroup_smul] at h1
  rw [← h1]
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.smul_mem_pointwise_smul _ _ _ (hR' hx)

end SteinbergBK

open SteinbergBK

theorem gf2_extraspecial_width_at_least_three
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hQe : IsExtraspecialPGroup 2 Q) {r : ℕ} (hr : r = GLATwoLocalRank 3 G) :
    ∃ w : ℕ, 3 ≤ w ∧ Nat.card Q = 2 ^ (1 + 2 * w) ∧
      (∀ w' : ℕ, Nat.card Q = 2 ^ (1 + 2 * w') → w' = w) ∧ Nat.card B = 3 ^ r ∧ r ≤ w := by
  have := Fact.mk Nat.prime_two
  have hcharM : CFSG.IsCharacteristicP 2 M := hchar M hM.1
  obtain ⟨⟨z, -, -, -, -, -, -, hSyl⟩, -, -, hBcard, -, -, -, -, he3⟩ :=
    gf2_witness_centralizer_and_rank hchar hM hsym hB hBM hQ hr
  obtain ⟨h3, hle⟩ := three_le_pRank_two_of_gf2_witness hchar he hM hsym hB hBM
  set Q₀ := CFSG.pCore 2 M with hQ₀
  have eQ : Q₀ ≃* Q := by
    rw [hQ]
    exact Q₀.equivMapOfInjective M.subtype M.subtype_injective
  have hQ₀e : IsExtraspecialPGroup 2 Q₀ := isExtraspecialPGroup_congr_mulEquiv eQ.symm hQe
  have hZ2 : Nat.card (center Q₀) = 2 := hQ₀e.2.2.2
  have : Fact (Nat.card (center Q₀)).Prime := ⟨hZ2 ▸ Nat.prime_two⟩
  obtain ⟨z₀, hz₀⟩ := (isCyclic_of_prime_card (α := center Q₀) rfl).exists_generator
  have hz : center Q₀ = zpowers (z₀ : Q₀) := (zpowers_coe_eq_of_generator hz₀).symm
  obtain ⟨-, ⟨w, ⟨hw1, hwV⟩, -⟩, hwQ, -, -, -, -, -, -, -, -, -, -, hBw⟩ :=
    extraspecial_centralizer_orthogonal_action hcharM hQ₀e hz
  have hQ₀card : Nat.card Q₀ = 2 ^ (1 + 2 * w) := hwQ w hwV
  have hQcard : Nat.card Q = 2 ^ (1 + 2 * w) := by rw [← Nat.card_congr eQ.toEquiv, hQ₀card]
  have hrw : r ≤ w := by
    have hB' : IsElemAbelian 3 (B.subgroupOf M) := isElemAbelian_subgroupOf_of_le hB.1
    have hB'card : Nat.card (B.subgroupOf M) = 3 ^ r := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv, hBcard]
    exact (hBw _ r hB' hB'card).2 w hwV
  refine ⟨w, ?_, hQcard, fun w' hw' => ?_, hBcard, hrw⟩
  ·
    by_contra hw3
    push Not at hw3
    interval_cases w
    ·
      have h8 : Nat.card Q₀ = 8 := hQ₀card.trans (by norm_num)
      have h2 := (extraspecial_width_one_two_rank_at_most_two hcharM hQ₀e h8).1
      omega
    ·
      have h32 : Nat.card Q₀ = 32 := hQ₀card.trans (by norm_num)
      have hsec := (extraspecial_width_two_subgroups_four_generated hcharM hQ₀e h32).2
      obtain ⟨-, -, hall, ⟨p, hp, hp2, B₀, r₀, hB₀, hB₀card, hr₀, T, hT, hT2, hB₀T⟩, -⟩ :=
        large_local_rank_core_and_component_reduction hchar he
      obtain ⟨⟨d, hd, hdr⟩, h6, -⟩ := hall p hp hp2 B₀ r₀ hB₀ hB₀card hr₀ T hT hT2 hB₀T
      set Q₁ := CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G)) with hQ₁
      have hQ₁2 : IsPGroup 2 Q₁ := CFSG.pCore_isPGroup.map _
      obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 M))
      have hSM : IsSylowOf 2 ((S : Subgroup M).map M.subtype) M := ⟨S, rfl⟩
      obtain ⟨g, hg⟩ := exists_conj_le_of_isSylowOf_top (hSyl _ hSM).1 hQ₁2
      set X₀ := Q₁.map (MulAut.conj g).toMonoidHom with hX₀
      have hX₀M : X₀ ≤ M := hg.trans (map_subtype_le _)
      set X := X₀.subgroupOf M with hX
      have eX : X ≃* Q₁ :=
        (subgroupOfEquivOfLe hX₀M).trans
          (Q₁.equivMapOfInjective _ (MulAut.conj g).injective).symm
      have hX2 : IsPGroup 2 X := hQ₁2.of_equiv eX.symm
      have : Fact (IsPGroup 2 X) := ⟨hX2⟩
      have hEA : CFSG.IsElementaryAbelian 2 (X ⧸ frattini X) :=
        CFSG.isElementaryAbelian_quotient_frattini
      have h16 := hsec X hX2 (frattini X) hEA
      rw [card_frattini_quotient_congr eX, hd] at h16
      have h64 : 2 ^ 6 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (h6.trans hdr)
      omega
  · have h1 : 2 ^ (1 + 2 * w') = 2 ^ (1 + 2 * w) := by rw [← hw', hQcard]
    have h2 := Nat.pow_right_injective (le_refl 2) h1
    omega

end CFSG.LocalAnalysis.GorensteinLyons
