module

public import CFSG.GH74.GLS.C3.Layer1.BkS4Prelim
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Th2.L627

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Bk

theorem center_eq_bot_of_simple_card_sixty {K : Type} [Group K] (hs : IsSimpleGroup K)
    (hc : Nat.card K = 60) : Subgroup.center K = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    have hcomm : IsMulCommutative K := Subgroup.center_eq_top_iff.1 h
    have hp := Group.is_simple_iff_prime_card.1 hs
    rw [hc] at hp
    exact absurd hp (by norm_num)

theorem exists_central_ne_of_isSylowOf
    {G : Type} [Group G] [Finite G] {t' : G} {J' S' : Subgroup G}
    (ht'2 : orderOf t' = 2)
    (hJ'C : J' ≤ centralizer ({t'} : Set G))
    (hJ'norm : ∀ c ∈ centralizer ({t'} : Set G), ∀ k ∈ J', c * k * c⁻¹ ∈ J')
    (hJ's : IsSimpleGroup (kBar J')) (hJ'card : Nat.card (kBar J') = 60)
    (hS' : IsSylowOf 2 S' (centralizer ({t'} : Set G))) (_ht'S' : t' ∈ S') :
    ∃ z ∈ S', z ∈ J' ∧ z ≠ 1 ∧ z ≠ t' ∧ ∀ s ∈ S', s * z = z * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : centralizer ({t'} : Set G) ≤ normalizer (J' : Set G) := fun c hc =>
    mem_normalizer_of_two_sided (hJ'norm c hc) (fun k hk => by
      simpa using hJ'norm c⁻¹ (Subgroup.inv_mem _ hc) k hk)
  have hW : IsSylowOf 2 (S' ⊓ J') J' := hS'.inf_of_le_normalizer hJ'C hKN
  have hWcard : Nat.card ↥(S' ⊓ J') = 2 ^ (Nat.card ↥J').factorization 2 := hW.card_eq
  have h60 : 60 ∣ Nat.card ↥J' := by
    rw [← hJ'card, ← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_card _
  have h4 : 2 ^ 2 ∣ Nat.card ↥J' := (by norm_num : 2 ^ 2 ∣ 60).trans h60
  have hf : 2 ≤ (Nat.card ↥J').factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h4
  have hWne : S' ⊓ J' ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(S' ⊓ J') = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hWcard] at h1
    have : 2 ^ 2 ≤ 2 ^ (Nat.card ↥J').factorization 2 := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hWn : ∀ s ∈ S', ∀ w ∈ S' ⊓ J', s * w * s⁻¹ ∈ S' ⊓ J' := fun s hs w hw =>
    ⟨mul_mem (mul_mem hs hw.1) (Subgroup.inv_mem _ hs), hJ'norm s (hS'.le hs) w hw.2⟩
  obtain ⟨z, hzW, hz1, hzc⟩ := exists_central_of_normal hS'.isPGroup hWn inf_le_left hWne
  refine ⟨z, hzW.1, hzW.2, hz1, ?_, hzc⟩
  intro hzt
  have htJ : t' ∈ J' := hzt ▸ hzW.2
  set π : ↥J' →* kBar J' := QuotientGroup.mk' (pPrimeCore 2 ↥J') with hπ
  have hcentral : π ⟨t', htJ⟩ ∈ Subgroup.center (kBar J') := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective g
    show π j * π ⟨t', htJ⟩ = π ⟨t', htJ⟩ * π j
    have hcomm : j * (⟨t', htJ⟩ : ↥J') = ⟨t', htJ⟩ * j :=
      Subtype.ext (mem_centralizer_singleton_iff.1 (hJ'C j.2))
    rw [← map_mul, ← map_mul, hcomm]
  rw [center_eq_bot_of_simple_card_sixty hJ's hJ'card, Subgroup.mem_bot] at hcentral
  have hmem : (⟨t', htJ⟩ : ↥J') ∈ pPrimeCore 2 ↥J' := (QuotientGroup.eq_one_iff _).1 hcentral
  have ht'O : t' ∈ pPrimeCoreOf 2 J' := ⟨⟨t', htJ⟩, hmem, rfl⟩
  have hdvd : orderOf t' ∣ Nat.card ↥(pPrimeCoreOf 2 J') := Subgroup.orderOf_dvd_natCard _ ht'O
  rw [ht'2] at hdvd
  exact (Nat.not_even_iff_odd.2 (TwoThin.card_pPrimeCoreOf_odd J')) (even_iff_two_dvd.2 hdvd)

end CFSG.GH74.GLS.Th2.L627
