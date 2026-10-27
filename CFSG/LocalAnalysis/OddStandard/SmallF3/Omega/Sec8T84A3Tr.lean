module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Cl2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace A3

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G}
  {B K L1 : Subgroup G}

theorem B_le_K (hK : Sec8T84K G t L S z g B K) : B ≤ K :=
  sec8t84a1_B_le_A.trans hK.A_le

theorem t_mem_K (hK : Sec8T84K G t L S z g B K) : t ∈ K :=
  hK.A_le sec8t84a1_t_mem_A

theorem cl2_of (hK : Sec8T84K G t L S z g B K) : Cl2 K B where
  B_le := B_le_K hK
  central := fun k hk b hb => ((hK.center b (B_le_K hK hb)).mpr hb k hk).symm
  comm_mem := hK.comm_le
  sq_mem := hK.sq_le
  B_sq := fun b hb => by
    rw [← pow_two]
    exact hK.ctx.B_e16.1.2 b hb

theorem t_mul_t (hctx : Sec8Ctx G t L S z g B) : t * t = 1 := by
  have h2 : orderOf t = 2 := hctx.toSec3SettingLB.involution
  have h3 : t ^ 2 = 1 := by
    rw [← h2]
    exact pow_orderOf_eq_one t
  rw [← pow_two]
  exact h3

theorem L1_normal (h : Sec8T84L1 G t L S z g B K L1) :
    ∀ k ∈ K, ∀ l ∈ L1, k * l * k⁻¹ ∈ L1 := by
  have hcard : Nat.card (L1.subgroupOf K) = 2 ^ 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv, h.card]
  have hindex : (L1.subgroupOf K).index = 2 := by
    have hmul := (L1.subgroupOf K).card_mul_index
    rw [hcard, h.K_data.card] at hmul
    have hpow : (2 : ℕ) ^ 9 = 2 ^ 8 * 2 := by norm_num
    rw [hpow] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hmul
  have hnorm : (L1.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two hindex
  intro k hk l hl
  have hmem : (⟨k, hk⟩ : ↥K) * ⟨l, h.le hl⟩ * (⟨k, hk⟩ : ↥K)⁻¹ ∈ L1.subgroupOf K :=
    hnorm.conj_mem ⟨l, h.le hl⟩ (by rw [Subgroup.mem_subgroupOf]; exact hl) ⟨k, hk⟩
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

private theorem zpow_t_eq_one_or_eq_t (hctx : Sec8Ctx G t L S z g B) (n : ℤ) :
    t ^ n = 1 ∨ t ^ n = t := by
  have h2 : orderOf t = 2 := hctx.toSec3SettingLB.involution
  have hmod : t ^ (n % 2) = t ^ n := by
    simpa [h2] using zpow_mod_orderOf t n
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [← hmod, h0, zpow_zero]
  · right
    rw [← hmod, h1, zpow_one]

private theorem zpowers_t_le_normalizer_L1 (h : Sec8T84L1 G t L S z g B K L1) :
    zpowers t ≤ normalizer (L1 : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx l hl
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact L1_normal h (t ^ n) (Subgroup.zpow_mem K (t_mem_K h.K_data) n) l hl

theorem mem_K_iff (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1) {k : G}
    (hk : k ∈ K) : ∃ l ∈ L1, k = l ∨ k = t * l := by
  have hnorm : zpowers t ≤ normalizer (L1 : Set G) := zpowers_t_le_normalizer_L1 h
  have hmem : k ∈ ((zpowers t ⊔ L1 : Subgroup G) : Set G) := by
    rw [← h.sup]
    exact hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (zpowers t) L1 hnorm, Set.mem_mul] at hmem
  obtain ⟨x, hx, l, hl, rfl⟩ := hmem
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases zpow_t_eq_one_or_eq_t hctx n with h1 | ht
  · exact ⟨l, hl, Or.inl (by rw [h1, one_mul])⟩
  · exact ⟨l, hl, Or.inr (by rw [ht])⟩

private theorem zpowers_t_le_normalizer_B (hctx : Sec8Ctx G t L S z g B) :
    zpowers t ≤ normalizer (B : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx b hb
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hc : Commute (t ^ n) b :=
    Commute.zpow_left (show Commute t b from sec8t84a1_t_comm hctx hb) n
  have hconj : t ^ n * b * (t ^ n)⁻¹ = b := by
    rw [hc.eq]
    group
  rwa [hconj]

theorem mem_A_iff (hctx : Sec8Ctx G t L S z g B) {a : G} (ha : a ∈ Asub8 t B) :
    ∃ b ∈ B, a = b ∨ a = t * b := by
  have hnorm : zpowers t ≤ normalizer (B : Set G) := zpowers_t_le_normalizer_B hctx
  rw [Asub8] at ha
  have hmem : a ∈ ((zpowers t ⊔ B : Subgroup G) : Set G) := ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (zpowers t) B hnorm, Set.mem_mul] at hmem
  obtain ⟨x, hx, b, hb, rfl⟩ := hmem
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases zpow_t_eq_one_or_eq_t hctx n with h1 | ht
  · exact ⟨b, hb, Or.inl (by rw [h1, one_mul])⟩
  · exact ⟨b, hb, Or.inr (by rw [ht])⟩

theorem tauFn_t_mul (hctx : Sec8Ctx G t L S z g B) (hK : Sec8T84K G t L S z g B K) {l : G}
    (hl : l ∈ K) : tauFn t (t * l) = tauFn t l := by
  have hb : tauFn t l ∈ B := (cl2_of hK).tau_mem (t_mem_K hK) hl
  have hc : t * tauFn t l = tauFn t l * t := sec8t84a1_t_comm hctx hb
  have htt := t_mul_t hctx
  calc tauFn t (t * l) = t * tauFn t l * t⁻¹ := by unfold tauFn; group
    _ = tauFn t l := by rw [hc]; group

theorem tau_exists (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1) {b : G}
    (hb : b ∈ B) : ∃ l ∈ L1, tauFn t l = b := by
  obtain ⟨k, hk, hkb⟩ := h.K_data.tau b hb
  obtain ⟨l, hl, hkl⟩ := mem_K_iff hctx h hk
  refine ⟨l, hl, ?_⟩
  have hkb' : tauFn t k = b := hkb
  rcases hkl with rfl | rfl
  · exact hkb'
  · rw [← hkb']
    exact (tauFn_t_mul hctx h.K_data (h.le hl)).symm

theorem tau_eq_one_iff (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1) {l : G}
    (hl : l ∈ L1) : tauFn t l = 1 ↔ l ∈ B := by
  constructor
  · intro h1
    have hcomm : l * t = t * l := tauFn_eq_one_iff.mp h1
    have hmemA : l ∈ Asub8 t B := by
      have hmem : l ∈ K ⊓ centralizer ({t} : Set G) :=
        ⟨h.le hl, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
      rwa [h.K_data.cent_t] at hmem
    obtain ⟨b, hb, hlb⟩ := mem_A_iff hctx hmemA
    rcases hlb with hlb | hlb
    · rw [hlb]
      exact hb
    · exfalso
      have hmemL1 : l * b⁻¹ ∈ L1 := L1.mul_mem hl (L1.inv_mem (h.B_le hb))
      have ht : l * b⁻¹ = t := by
        rw [hlb]
        group
      exact h.t_not (ht ▸ hmemL1)
  · intro hb
    exact tauFn_eq_one_iff.mpr (sec8t84a1_t_comm hctx hb).symm

theorem inf_cent_t (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1) :
    L1 ⊓ centralizer ({t} : Set G) = B := by
  apply le_antisymm
  · intro x hx
    exact (tau_eq_one_iff hctx h hx.1).mp
      (tauFn_eq_one_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hx.2))
  · intro b hb
    exact ⟨h.B_le hb, Subgroup.mem_centralizer_singleton_iff.mpr
      (sec8t84a1_t_comm hctx hb).symm⟩

theorem tau_mul_L1 (h : Sec8T84L1 G t L S z g B K L1) {x y : G} (hx : x ∈ L1) (hy : y ∈ L1) :
    tauFn t (x * y) = tauFn t x * tauFn t y :=
  (cl2_of h.K_data).tau_mul (t_mem_K h.K_data) (h.le hx) (h.le hy)

theorem tau_inv_L1 (h : Sec8T84L1 G t L S z g B K L1) {x : G} (hx : x ∈ L1) :
    tauFn t x⁻¹ = (tauFn t x)⁻¹ := by
  have h1 := tau_mul_L1 h hx (L1.inv_mem hx)
  rw [mul_inv_cancel] at h1
  have h2 : tauFn t (1 : G) = 1 := by unfold tauFn; group
  rw [h2] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem sq_eq_of_tau_eq (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1)
    {l l' : G} (hl : l ∈ L1) (hl' : l' ∈ L1) (he : tauFn t l = tauFn t l') :
    l * l = l' * l' := by
  have hxl : l⁻¹ * l' ∈ L1 := L1.mul_mem (L1.inv_mem hl) hl'
  have htau : tauFn t (l⁻¹ * l') = 1 := by
    rw [tau_mul_L1 h (L1.inv_mem hl) hl', tau_inv_L1 h hl, he, inv_mul_cancel]
  have hb : l⁻¹ * l' ∈ B := (tau_eq_one_iff hctx h hxl).mp htau
  have hsq : (l * (l⁻¹ * l')) * (l * (l⁻¹ * l')) = l * l :=
    (cl2_of h.K_data).sq_mul_B (h.le hl) hb
  have hl'eq : l' = l * (l⁻¹ * l') := by group
  rw [hl'eq, hsq]

end A3

end CFSG.OddStandard.SmallF3.Omega
