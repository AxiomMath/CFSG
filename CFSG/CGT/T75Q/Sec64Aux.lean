module

public import CFSG.CGT.Timmesfeld75.Sec3Fpf
import Mathlib.Tactic.Group

public section

namespace CFSG.CGT.T75Q

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

set_option quotPrecheck false in
local notation "TQ" =>
  (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

theorem mem_normalizer_of_map_mem (hS : Sec3 T T₁) {k : G} (hk : k ∈ T ⊔ T₁)
    (hnorm : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨k, hk⟩ ∈
      Subgroup.normalizer ((TQ : Subgroup XQ) : Set XQ)) :
    k ∈ Subgroup.normalizer (T : Set G) := by
  have hTM : IsPGroup 2 ↥(T ⊔ cfgM T T₁) :=
    (isPGroup_two_of_isElemAbelian hS.cfg.wc.1).to_sup_of_normal_right'
      (isPGroup_two_of_isElemAbelian hS.cfg.isElemAbelian_cfgM)
      (le_sup_left.trans hS.cfg.le_normalizer_cfgM)
  have hconj : conjSubgroup k T ≤ T ⊔ cfgM T T₁ := by
    intro y hy
    have hz : k⁻¹ * y * k ∈ T := mem_conjSubgroup.1 hy
    have hzX : k⁻¹ * y * k ∈ T ⊔ T₁ := Subgroup.mem_sup_left hz
    have hmem : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨k⁻¹ * y * k, hzX⟩ ∈ TQ :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hz)
    have h1 := (Subgroup.mem_normalizer_iff.1 hnorm _).1 hmem
    obtain ⟨t₀, ht₀, hteq⟩ := Subgroup.mem_map.1 h1
    have h2 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))
        (⟨k, hk⟩ * ⟨k⁻¹ * y * k, hzX⟩ * ⟨k, hk⟩⁻¹) =
        QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) t₀ := by
      rw [map_mul, map_mul, map_inv]
      exact hteq.symm
    have h3 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h2)
    have hkz : (((⟨k, hk⟩ * ⟨k⁻¹ * y * k, hzX⟩ * ⟨k, hk⟩⁻¹ : ↥(T ⊔ T₁)) : ↥(T ⊔ T₁)) : G) = y := by
      show k * (k⁻¹ * y * k) * k⁻¹ = y
      group
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hkz] at h3
    have ht₀T : (t₀ : G) ∈ T := Subgroup.mem_subgroupOf.1 ht₀
    have hy' : y = (t₀ : G) * ((y⁻¹ * (t₀ : G))⁻¹) := by group
    rw [hy']
    exact (T ⊔ cfgM T T₁).mul_mem (Subgroup.mem_sup_left ht₀T)
      (Subgroup.mem_sup_right ((cfgM T T₁).inv_mem h3))
  exact mem_normalizer_of_conjSubgroup_eq
    (eq_of_conj_le_pGroup hS.cfg.wc hTM le_sup_left hconj)

theorem exists_odd_normalizer (hS : Sec3 T T₁) {f : ℕ} (hf : 2 ≤ f)
    (hX : IsL2Pair XQ TQ (2 ^ f)) :
    ∃ (k : G) (hk : k ∈ T ⊔ T₁), k ∈ Subgroup.normalizer (T : Set G) ∧
      Odd (orderOf (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨k, hk⟩)) ∧
      QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨k, hk⟩ ≠ 1 := by
  obtain ⟨Hc, hHN, hcyc, hcard, -, -, -⟩ := hX.exists_complement
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card Hc := orderOf_eq_card_of_forall_mem_zpowers hg
  have hpow : 2 ≤ 2 ^ (f - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (f - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow2 : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hcard' : Nat.card Hc = 2 * 2 ^ (f - 1) - 1 := by rw [hcard, hpow2]
  have hodd : Odd (orderOf g) := by
    rw [hord, hcard', Nat.odd_iff]
    omega
  have hne : orderOf g ≠ 1 := by
    rw [hord, hcard']
    omega
  obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk_surjective (g : XQ)
  have hgN : (g : XQ) ∈ Subgroup.normalizer ((TQ : Subgroup XQ) : Set XQ) := hHN g.2
  have hk₀' : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨(k₀ : G), k₀.2⟩ = (g : XQ) := by
    rw [← hk₀]
    rfl
  refine ⟨(k₀ : G), k₀.2, ?_, ?_, ?_⟩
  · exact mem_normalizer_of_map_mem hS k₀.2 (by rw [hk₀']; exact hgN)
  · rw [hk₀', Subgroup.orderOf_coe]
    exact hodd
  · rw [hk₀']
    intro h1
    apply hne
    rw [← Subgroup.orderOf_coe, h1, orderOf_one]

theorem mem_left_of_centralizes (hS : Sec3 T T₁) {q : ℕ} (hX : IsL2Pair XQ TQ q) {u : G}
    (hu : u ∈ T ⊔ T₁) (huC : ∀ t ∈ T, u * t = t * u) : u ∈ T := by
  have hTab := hS.cfg.wc.1
  have hTne : TQ ≠ ⊥ := hS.map_ne_bot
  obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hTne
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hcent := hX.centralizer_eq hs hs1'
  obtain ⟨s₀, hs₀, hss₀⟩ := Subgroup.mem_map.1 hs
  have hs₀T : (s₀ : G) ∈ T := Subgroup.mem_subgroupOf.1 hs₀
  have hū : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨u, hu⟩ ∈
      Subgroup.centralizer ({s} : Set XQ) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hss₀, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact huC _ hs₀T
  rw [hcent] at hū
  obtain ⟨t₀, ht₀, hteq⟩ := Subgroup.mem_map.1 hū
  have h3 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hteq)
  have ht₀T : (t₀ : G) ∈ T := Subgroup.mem_subgroupOf.1 ht₀
  have hn : ((t₀ : G)⁻¹ * u) ∈ cfgM T T₁ := by simpa using h3
  have hnC : ∀ t ∈ T, ((t₀ : G)⁻¹ * u) * t = t * ((t₀ : G)⁻¹ * u) := by
    intro t ht
    have h1 : (t₀ : G)⁻¹ * t = t * (t₀ : G)⁻¹ :=
      (Commute.inv_left (show Commute (t₀ : G) t from elemAbelian_mul_comm hTab ht₀T ht)).eq
    calc ((t₀ : G)⁻¹ * u) * t = (t₀ : G)⁻¹ * (u * t) := by group
      _ = (t₀ : G)⁻¹ * (t * u) := by rw [huC t ht]
      _ = ((t₀ : G)⁻¹ * t) * u := by group
      _ = (t * (t₀ : G)⁻¹) * u := by rw [h1]
      _ = t * ((t₀ : G)⁻¹ * u) := by group
  obtain ⟨a, ha, b, hb, hab⟩ := hS.cfg.mem_cfgM_iff.1 hn
  have haT : a ∈ T := (mem_normIn.1 ha).1
  have hbC : ∀ t ∈ T, b * t = t * b := by
    intro t ht
    have hb' : b = a⁻¹ * ((t₀ : G)⁻¹ * u) := by rw [hab]; group
    have h1 : a⁻¹ * t = t * a⁻¹ :=
      (Commute.inv_left (show Commute a t from elemAbelian_mul_comm hTab haT ht)).eq
    rw [hb']
    calc a⁻¹ * ((t₀ : G)⁻¹ * u) * t = a⁻¹ * (((t₀ : G)⁻¹ * u) * t) := by group
      _ = a⁻¹ * (t * ((t₀ : G)⁻¹ * u)) := by rw [hnC t ht]
      _ = (a⁻¹ * t) * ((t₀ : G)⁻¹ * u) := by group
      _ = (t * a⁻¹) * ((t₀ : G)⁻¹ * u) := by rw [h1]
      _ = t * (a⁻¹ * ((t₀ : G)⁻¹ * u)) := by group
  have hb1 : b = 1 := by
    by_contra hb1
    have hbT₁ : b ∈ T₁ := (mem_normIn.1 hb).1
    have hTle : T ≤ normIn T T₁ := fun t ht =>
      mem_normIn.2 ⟨ht, hS.cfg.wc₁.centralizer_le_normalizer hbT₁ hb1
        (Subgroup.mem_centralizer_singleton_iff.2 (hbC t ht).symm)⟩
    exact hS.not_le_cfgM (hTle.trans (Cfg.normIn_le_cfgM_left T T₁))
  have hu' : u = (t₀ : G) * a := by
    have : (t₀ : G)⁻¹ * u = a := by rw [hab, hb1, mul_one]
    calc u = (t₀ : G) * ((t₀ : G)⁻¹ * u) := by group
      _ = (t₀ : G) * a := by rw [this]
  rw [hu']
  exact T.mul_mem ht₀T haT

end CFSG.CGT.T75Q
