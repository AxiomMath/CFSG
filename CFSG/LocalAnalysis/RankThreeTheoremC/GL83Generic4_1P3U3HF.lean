module

import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedRankForm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u3hf_inf_card_le {T F : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (hxF : x ∈ F)
    (hxT : x ∉ T) (hTx : ∀ t ∈ T, t * x = x * t) (hT3 : ∀ t ∈ T, t ^ 3 = 1)
    (hrk : CFSG.Open.pRank 3 F ≤ 2) (S : Subgroup G) (hS : S ≤ F ⊓ T) :
    Nat.card S ≠ 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hcard
  have hS3 : ∀ s ∈ S, s ^ 3 = 1 := fun s hs => hT3 s (hS hs).2
  have hSp : IsPGroup 3 S := IsPGroup.of_card hcard
  have hSab : IsMulCommutative S := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  have hSel : IsElemAbelian 3 S := ⟨hSab, hS3⟩
  have hxS : x ∉ S := fun h => hxT (hS h).2
  have hcomm : ∀ s ∈ S, s * x = x * s := fun s hs => hTx s (hS hs).2
  have hcard27 : Nat.card (S ⊔ zpowers x : Subgroup G) = 3 ^ 3 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three S hx3 hxS hcomm, hcard]
    ring
  have hSx : S ≤ centralizer ((zpowers x : Subgroup G) : Set G) := fun s hs => by
    rw [zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr (hcomm s hs)
  have hel : IsElemAbelian 3 (S ⊔ zpowers x : Subgroup G) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hSel
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3) hSx
  have hle : S ⊔ zpowers x ≤ F := sup_le (hS.trans inf_le_left) (zpowers_le.mpr hxF)
  have h3 := le_pRank_of_elemAbelian_card (p := 3) hle hel hcard27
  omega

theorem u3hf_inf_central {T F : Subgroup G} (hFp : IsPGroup 3 F)
    (hFT : ∀ f ∈ F, ∀ t ∈ T, f * t * f⁻¹ ∈ T)
    (hS9 : ∀ S : Subgroup G, S ≤ F ⊓ T → Nat.card S ≠ 3 ^ 2) :
    ∀ a ∈ F ⊓ T, ∀ f ∈ F, a * f = f * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := F ⊓ T with hN
  have hNp : IsPGroup 3 N := hFp.to_le inf_le_left
  obtain ⟨k, hk⟩ := hNp.exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have hdvd : 3 ^ 2 ∣ Nat.card N := by rw [hk]; exact pow_dvd_pow 3 (by omega)
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥N) 3 hdvd
    exact hS9 (K.map N.subtype) (Subgroup.map_subtype_le K)
      (by rw [Subgroup.card_map_of_injective N.subtype_injective, hK])
  intro a ha f hf
  have haN : a ∈ N := ha
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with h0 | h1
  ·
    have hN1 : Nat.card N = 1 := by rw [hk, h0, pow_zero]
    have hNbot : N = ⊥ := Subgroup.card_eq_one.mp hN1
    have ha1 : a = 1 := by
      rw [hNbot] at haN
      exact mem_bot.mp haN
    rw [ha1]
    simp
  ·
    have hN3 : Nat.card N = 3 := by rw [hk, h1, pow_one]
    set N' : Subgroup ↥F := N.subgroupOf F with hN'
    have hnorm : N'.Normal := ⟨fun n hn g => by
      refine Subgroup.mem_subgroupOf.mpr ⟨F.mul_mem (F.mul_mem g.2 n.2) (F.inv_mem g.2), ?_⟩
      exact hFT g g.2 n (Subgroup.mem_subgroupOf.mp hn).2⟩
    have hNN' : Nat.card N' = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ≤ F)).toEquiv, hN3]
    have hne : N' ≠ ⊥ := fun h => by
      have : Nat.card N' = 1 := by rw [h]; simp
      omega
    have : Group.IsNilpotent ↥F := hFp.isNilpotent
    have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    have hle : N' ⊓ center ↥F ≤ N' := inf_le_left
    have hdvd : Nat.card ↥(N' ⊓ center ↥F) ∣ 3 := hNN' ▸ Subgroup.card_dvd_of_le hle
    have h3 : Nat.card ↥(N' ⊓ center ↥F) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hc
      · exact h
    have heq : N' ⊓ center ↥F = N' := Subgroup.eq_of_le_of_card_ge hle (by rw [hNN', h3])
    have haN' : (⟨a, ha.1⟩ : ↥F) ∈ N' := Subgroup.mem_subgroupOf.mpr haN
    have hac : (⟨a, ha.1⟩ : ↥F) ∈ center ↥F := by
      have : (⟨a, ha.1⟩ : ↥F) ∈ N' ⊓ center ↥F := by rw [heq]; exact haN'
      exact this.2
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hac ⟨f, hf⟩)).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
