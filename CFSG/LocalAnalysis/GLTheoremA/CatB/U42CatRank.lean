module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42CatDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.LocalAnalysis.GLTheoremA.S12.Common
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem x_not_mem_of_not_dvd {L : Subgroup G} {x : G} (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hxo : orderOf x = 3) (hz : ¬ 3 ∣ Nat.card (Subgroup.center (PQuot 3 L))) : x ∉ L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hx
  set xL : ↥L := ⟨x, hx⟩ with hxL'
  set z : PQuot 3 L := pQuotHom 3 L xL with hzdef
  have hzc : z ∈ Subgroup.center (PQuot 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨l, rfl⟩ := pQuotHom_surjective 3 L y
    have hc : (l : G) * x = x * (l : G) := Subgroup.mem_centralizer_iff.1 hxL l l.2
    have : l * xL = xL * l := Subtype.ext hc
    rw [hzdef, ← map_mul, ← map_mul, this]
  by_cases hz1 : z = 1
  ·
    have hO : x ∈ GLAPPrimeCoreOf 3 L := by
      refine (chev_mem_glaPPrimeCoreOf_iff hx).2 ?_
      have : (pQuotHom 3 L xL) = 1 := hz1
      rwa [pQuotHom, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have h1 : orderOf x ∣ Nat.card (GLAPPrimeCoreOf 3 L) := Subgroup.orderOf_dvd_natCard _ hO
    rw [hxo] at h1
    exact absurd h1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (i183_coprime_card_glaPPrimeCoreOf Nat.prime_three L))
  · have hz3 : z ^ 3 = 1 := by
      rw [hzdef, ← map_pow]
      have : xL ^ 3 = 1 := Subtype.ext (by
        show x ^ 3 = 1
        rw [← hxo]
        exact pow_orderOf_eq_one x)
      rw [this, map_one]
    have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    apply hz
    have h2 := Subgroup.orderOf_dvd_natCard (Subgroup.center (PQuot 3 L)) hzc
    rwa [hzo] at h2

theorem exists_rank_five (h3 : U42RankAt) {X L : Subgroup G} (hL : GLAPComponent 3 X L) {x : G}
    (hxL : x ∈ Subgroup.centralizer (L : Set G)) (hxo : orderOf x = 3)
    (hS : catalogIs (PSimple 3 L) IsU42Host) :
    ∃ W : Subgroup G, W ≤ L ⊔ Subgroup.zpowers x ∧ IsElemAbelian 3 W ∧ Nat.card W = 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect (PQuot 3 L) :=
    ⟨(isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL).1⟩
  obtain ⟨hZ3, hZ4⟩ := h3 (PQuot 3 L) inferInstance hS
  have hker : ¬ 3 ∣ Nat.card (pQuotHom 3 L).ker := by
    rw [ker_pQuotHom]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  have hlift : ∀ {W₀ : Subgroup (PQuot 3 L)}, IsElemAbelian 3 W₀ →
      ∃ W : Subgroup G, W ≤ L ∧ IsElemAbelian 3 W ∧ Nat.card W = Nat.card W₀ := by
    intro W₀ hW₀
    obtain ⟨W, hWp, hWmap, hWinj⟩ := CatB.exists_pSubgroup_lift Nat.prime_three (pQuotHom 3 L) hker
      (isPGroup_of_isElemAbelian hW₀)
      (by rw [MonoidHom.range_eq_top.2 (pQuotHom_surjective 3 L)]; exact le_top)
    have hel : IsElemAbelian 3 W :=
      CatB.isElemAbelian_of_injective_comp_subtype (pQuotHom 3 L) hWinj (hWmap ▸ hW₀)
    refine ⟨W.map L.subtype, Subgroup.map_subtype_le W,
      CFSG.SectionRank.isElemAbelian_map hel L.subtype, ?_⟩
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      CatB.card_eq_of_injective_comp_subtype (pQuotHom 3 L) hWinj, hWmap]
  by_cases hz : 3 ∣ Nat.card (Subgroup.center (PQuot 3 L))
  · obtain ⟨W₀, hW₀e, hW₀c⟩ := hZ3 hz
    obtain ⟨W, hWL, hWe, hWc⟩ := hlift hW₀e
    exact ⟨W, hWL.trans le_sup_left, hWe, hWc.trans hW₀c⟩
  · obtain ⟨W₀, hW₀e, hW₀c⟩ := hZ4 hz
    obtain ⟨W, hWL, hWe, hWc⟩ := hlift hW₀e
    have hxW : x ∉ W := fun h => x_not_mem_of_not_dvd hxL hxo hz (hWL h)
    have hx3 : x ^ 3 = 1 := by
      rw [← hxo]
      exact pow_orderOf_eq_one x
    have hxcW : x ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_iff.1 hxL h (hWL hh)
    have hcomm : ∀ a ∈ W, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
      intro a ha b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact ((Commute.zpow_right (Subgroup.mem_centralizer_iff.1 hxcW a ha) n)).eq
    have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (W : Set G) :=
      Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer (W : Set G) hxcW)
    have hinf : W ⊓ Subgroup.zpowers x = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      by_contra hy1
      exact hxW ((Subgroup.zpowers_le.2 hy.1) (S12.mem_zpowers_of_prime_order hxo hy.2 hy1))
    have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hxo, hWc, hW₀c] at h1
    exact ⟨W ⊔ Subgroup.zpowers x, sup_le_sup_right hWL _,
      CFSG.Open.IsElemAbelian.sup_of_commute hWe (CFSG.Open.isElemAbelian_zpowers hx3) hcomm,
      by rw [h1]; norm_num⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
