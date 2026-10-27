module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.CentralizerFusion
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.FixedPointTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.IndexTI
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.SylowInY

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open MulAction Subgroup

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

theorem coe_mem_normalizer_map {Y : Subgroup G} (H : Subgroup Y) {τ : Y}
    (hτ : τ ∈ normalizer (H : Set Y)) :
    (τ : G) ∈ normalizer ((H.map Y.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hτ ⊢
  intro x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨τ * z * τ⁻¹, (hτ z).mp hz, by simp⟩
  · rintro ⟨z, hz, hzx⟩
    have hz' : ((z : Y) : G) = (τ : G) * x * (τ : G)⁻¹ := hzx
    refine ⟨τ⁻¹ * z * τ, (hτ (τ⁻¹ * z * τ)).mpr ?_, ?_⟩
    · rw [show τ * (τ⁻¹ * z * τ) * τ⁻¹ = z by group]
      exact hz
    · show ((τ⁻¹ * z * τ : Y) : G) = x
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hz']
      group

theorem isPGroup_subgroupOf_sylow (R : Sylow p G) (Y : Subgroup G) :
    IsPGroup p ((R : Subgroup G).subgroupOf Y) :=
  R.isPGroup'.comap_of_injective Y.subtype Subtype.val_injective

theorem not_dvd_index_subgroupOf_sylow [Finite G] (R : Sylow p G) (Y : Subgroup G)
    (hRY : (R : Subgroup G) ≤ Y) :
    ¬ p ∣ ((R : Subgroup G).subgroupOf Y).index := fun h =>
  R.not_dvd_index (dvd_trans h ⟨Y.index, (relIndex_mul_index hRY).symm⟩)

def sylowOfLe [Finite G] (R : Sylow p G) (Y : Subgroup G) (hRY : (R : Subgroup G) ≤ Y) :
    Sylow p Y :=
  (isPGroup_subgroupOf_sylow R Y).toSylow (not_dvd_index_subgroupOf_sylow R Y hRY)

theorem sylowOfLe_coe [Finite G] (R : Sylow p G) (Y : Subgroup G) (hRY : (R : Subgroup G) ≤ Y) :
    (sylowOfLe R Y hRY : Subgroup Y) = (R : Subgroup G).subgroupOf Y :=
  IsPGroup.toSylow_coe _ _

theorem sylowOfLe_map [Finite G] (R : Sylow p G) (Y : Subgroup G) (hRY : (R : Subgroup G) ≤ Y) :
    ((sylowOfLe R Y hRY : Subgroup Y)).map Y.subtype = (R : Subgroup G) := by
  rw [sylowOfLe_coe, subgroupOf_map_subtype, inf_of_le_left hRY]

theorem card_sylow_eq_relIndex [Finite G] (R : Sylow p G) (Y : Subgroup G)
    (hRY : (R : Subgroup G) ≤ Y) :
    Nat.card (Sylow p Y) = (normalizer (R : Set G)).relIndex Y := by
  rw [Sylow.card_eq_index_normalizer (sylowOfLe R Y hRY)]
  show (normalizer (((sylowOfLe R Y hRY : Subgroup Y)) : Set Y)).index = _
  rw [sylowOfLe_coe, ← subgroupOf_normalizer_eq hRY]
  rfl

theorem normMax_of_TI_involution [Finite G] (R : Sylow p G)
    (hTI : ∀ g : G, g ∉ normalizer (R : Set G) →
      (R : Subgroup G) ⊓ (R : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊥)
    (harith : ∀ d : ℕ, d ∣ (normalizer (R : Set G)).index →
      d ≡ 1 [MOD Nat.card (R : Subgroup G)] → d = 1 ∨ 2 ∣ d)
    (t : G) (htN : t ∈ normalizer (R : Set G)) (ht : orderOf t = 2)
    (hfuse : ∀ s ∈ normalizer (R : Set G), IsConj t s →
      ∃ m ∈ normalizer (R : Set G), m * t * m⁻¹ = s)
    (hover : ∀ T : Subgroup G, normalizer (R : Set G) ⊓ Subgroup.centralizer {t} < T →
      T ≤ Subgroup.centralizer {t} → normalizer (R : Set G) ⊔ T = ⊤)
    (Y : Subgroup G) (hY : normalizer (R : Set G) ≤ Y) :
    Y = normalizer (R : Set G) ∨ Y = ⊤ := by
  have hRY : (R : Subgroup G) ≤ Y := le_trans le_normalizer hY
  have hcong := index_modEq_one_of_TI R hTI Y hY
  have hdvd : (normalizer (R : Set G)).relIndex Y ∣ (normalizer (R : Set G)).index :=
    ⟨Y.index, (relIndex_mul_index hY).symm⟩
  rcases harith _ hdvd hcong with h1 | h2
  · left
    exact le_antisymm (relIndex_eq_one.mp h1) hY
  · right
    have hev : Even (Nat.card (Sylow p Y)) := by
      rw [card_sylow_eq_relIndex R Y hRY]
      exact even_iff_two_dvd.mpr h2
    set RY : Sylow p Y := sylowOfLe R Y hRY with hRYdef
    let τ : Y := ⟨t, hY htN⟩
    have hτN : τ ∈ normalizer ((RY : Subgroup Y) : Set Y) := by
      rw [hRYdef, sylowOfLe_coe, ← subgroupOf_normalizer_eq hRY]
      exact Subgroup.mem_subgroupOf.mpr htN
    have hτorder : orderOf τ = 2 := (Subgroup.orderOf_coe τ).symm.trans ht
    have hG2 : IsPGroup 2 (Subgroup.zpowers τ) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτorder]; norm_num)
    have hRYfix : RY ∈ fixedPoints (Subgroup.zpowers τ) (Sylow p Y) := by
      rw [mem_fixedPoints]
      intro g
      change (g : Y) • RY = RY
      rw [Sylow.smul_eq_iff_mem_normalizer]
      exact (Subgroup.zpowers_le.mpr hτN) g.2
    obtain ⟨b, hbfix, hbne⟩ := exists_ne_fixed_of_two_group hG2 hev hRYfix
    have hbτ : τ • b = b := mem_fixedPoints.mp hbfix ⟨τ, Subgroup.mem_zpowers τ⟩
    obtain ⟨y, hy, hyN, hR'⟩ := exists_conj_sylow_in_ne Y RY b hbne
    rw [hRYdef, sylowOfLe_map] at hyN hR'
    have htR' : t ∈ normalizer (((b : Subgroup Y).map Y.subtype : Subgroup G) : Set G) :=
      coe_mem_normalizer_map (b : Subgroup Y) (Sylow.smul_eq_iff_mem_normalizer.mp hbτ)
    obtain ⟨w, hwY, hwC, hwN⟩ :=
      exists_mem_centralizer_not_mem_normalizer (R : Subgroup G) Y hY y hy hyN
        ((b : Subgroup Y).map Y.subtype) hR' t htR' hfuse
    have hstrict : normalizer (R : Set G) ⊓ Subgroup.centralizer {t} <
        Y ⊓ Subgroup.centralizer {t} := by
      refine lt_of_le_of_ne (inf_le_inf hY le_rfl) ?_
      intro heq
      have hw : w ∈ normalizer (R : Set G) ⊓ Subgroup.centralizer {t} := heq ▸ ⟨hwY, hwC⟩
      exact hwN hw.1
    have htop := hover (Y ⊓ Subgroup.centralizer {t}) hstrict inf_le_right
    have hle : normalizer (R : Set G) ⊔ (Y ⊓ Subgroup.centralizer {t}) ≤ Y :=
      sup_le hY inf_le_left
    rw [htop] at hle
    exact top_le_iff.mp hle

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
