module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterMuOneDich
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterMuOneInv
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterMuOneItem
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterMuOneMain

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

theorem U3C1OuterLevelData.muOne_false_of_sylow_of_index_two
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ D : Subgroup G}
    {d : G} {V U U₁ : Subgroup G} (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1)
    (hL : U3C1OuterLevelData G L f t T D V U U₁ 1) (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hidx : ∀ s ∈ T, ∀ s' ∈ T, s ∉ szT₁ L T ⊔ zpowers t → s' ∉ szT₁ L T ⊔ zpowers t →
      s * s'⁻¹ ∈ szT₁ L T ⊔ zpowers t)
    (hsyl : ∃ S : Sylow 2 G, (S : Subgroup G) = U ⊔ T) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨htT, -, -, hTN₁, hdisj, -, -⟩ := h.start_of_card_sylow hS2
  have hT₁T : szT₁ L T ≤ T := szT₁_le_left L T
  have hPeq := hL.muOne_sup_eq hS
  have htt : t * t = 1 := by rw [← sq, h.sq_eq_one]
  obtain ⟨w₁, hw₁T, hw₁2, hw₁S, hw₁V⟩ : ∃ w ∈ T, w ^ 2 = 1 ∧ w ∉ szT₁ L T ⊔ zpowers t ∧
      ∀ r ∈ V, w * r * w⁻¹ = r⁻¹ := by
    obtain ⟨v₀, hv₀T, hv₀2, hv₀S⟩ := hS.outer
    rcases hL.muOne_dichotomy hS hc hμV hK hμ hv₀T hv₀2 hv₀S with hcen | hinv
    · have hv₀t : v₀ * t = t * v₀ := mem_centralizer_singleton_iff.mp (h.le hv₀T)
      refine ⟨t * v₀, mul_mem htT hv₀T, ?_, fun hm => hv₀S ?_, fun r hr => ?_⟩
      · rw [Commute.mul_pow hv₀t.symm 2, h.sq_eq_one, hv₀2, one_mul]
      · rw [show v₀ = t⁻¹ * (t * v₀) by group]
        exact mul_mem (inv_mem (mem_sup_right (mem_zpowers t))) hm
      · rw [show t * v₀ * r * (t * v₀)⁻¹ = t * (v₀ * r * v₀⁻¹) * t⁻¹ by group, hcen r hr]
        exact hS.conf.inv r hr
    · exact ⟨v₀, hv₀T, hv₀2, hv₀S, hinv⟩
  have hbgen : ∀ s ∈ T, ∃ k : ℤ, (w₁ ^ k)⁻¹ * s ∈ szT₁ L T ⊔ zpowers t := by
    intro s hs
    by_cases hsH : s ∈ szT₁ L T ⊔ zpowers t
    · exact ⟨0, by simpa using hsH⟩
    · refine ⟨1, ?_⟩
      have hs' : s⁻¹ ∉ szT₁ L T ⊔ zpowers t := fun h' => hsH (by simpa using inv_mem h')
      have hw' : w₁⁻¹ ∉ szT₁ L T ⊔ zpowers t := fun h' => hw₁S (by simpa using inv_mem h')
      have h1 := hidx s⁻¹ (inv_mem hs) w₁⁻¹ (inv_mem hw₁T) hs' hw'
      rw [zpow_one]
      have h2 := inv_mem h1
      rwa [mul_inv_rev, inv_inv, inv_inv] at h2
  have htb : t ∉ szT₁ L T ⊔ zpowers w₁ := by
    intro htb
    rw [sup_comm] at htb
    obtain ⟨a, ha, y, hy, hay⟩ := ncyc_exists_mul_of_mem_sup (zpowers_le.mpr (hTN₁ hw₁T)) htb
    rcases mem_zpowers_involution_eq_one_or_eq hw₁2 ha with rfl | rfl
    · have ht1 : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨by rw [← hay, one_mul]; exact hy,
        mem_zpowers t⟩
      rw [hdisj] at ht1
      have : t = 1 := (mem_bot.mp ht1)
      rw [this] at htt
      have h1 := h.inv
      rw [this, orderOf_one] at h1
      exact absurd h1 (by norm_num)
    · apply hw₁S
      rw [show a = t * y⁻¹ by rw [← hay]; group]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (inv_mem hy))
  have hM₀T : szT₁ L T ⊔ zpowers w₁ ≤ T := sup_le hT₁T (zpowers_le.mpr hw₁T)
  have hM₀N : szT₁ L T ⊔ zpowers w₁ ≤ normalizer (U₁ : Set G) := hM₀T.trans hL.T_le
  have hcommT := h.commutator_le_szT₁_of_card_sylow hS2
  have hM₀n : ∀ s ∈ T, ∀ m ∈ szT₁ L T ⊔ zpowers w₁, s * m * s⁻¹ ∈ szT₁ L T ⊔ zpowers w₁ := by
    intro s hs m hm
    have hcm : s * m * s⁻¹ * m⁻¹ ∈ szT₁ L T := by
      have := hcommT (commutator_mem_commutator hs (hM₀T hm))
      rwa [commutatorElement_def] at this
    rw [show s * m * s⁻¹ = (s * m * s⁻¹ * m⁻¹) * m by group]
    exact mul_mem (mem_sup_left hcm) hm
  set Q := (szT₁ L T ⊔ zpowers w₁) ⊔ U₁ with hQdef
  have hMn : ∀ s ∈ U ⊔ T, ∀ m ∈ Q, s * m * s⁻¹ ∈ Q := by
    intro s hs m hm
    rw [hPeq] at hs
    obtain ⟨s₀, hs₀, u₀, hu₀, rfl⟩ := ncyc_exists_mul_of_mem_sup hL.T_le hs
    obtain ⟨m₀, hm₀, u₁, hu₁, rfl⟩ := ncyc_exists_mul_of_mem_sup hM₀N hm
    have e : s₀ * u₀ * (m₀ * u₁) * (s₀ * u₀)⁻¹ =
        (s₀ * m₀ * s₀⁻¹) * (s₀ * ((m₀⁻¹ * u₀ * m₀) * u₁ * u₀⁻¹) * s₀⁻¹) := by group
    rw [e]
    refine mul_mem (mem_sup_left (hM₀n s₀ hs₀ m₀ hm₀)) (mem_sup_right ?_)
    have h1 : m₀⁻¹ * u₀ * m₀ ∈ U₁ := (mem_normalizer_iff''.mp (hM₀N hm₀) u₀).mp hu₀
    exact (mem_normalizer_iff.mp (hL.T_le hs₀) _).mp (mul_mem (mul_mem h1 hu₁) (inv_mem hu₀))
  have htM : t ∉ Q := by
    intro htM
    obtain ⟨m₀, hm₀, u, hu, hmu⟩ := ncyc_exists_mul_of_mem_sup hM₀N htM
    have huT : u ∈ T := by
      rw [show u = m₀⁻¹ * t by rw [← hmu]; group]
      exact mul_mem (inv_mem (hM₀T hm₀)) htT
    apply htb
    rw [← hmu]
    exact mul_mem hm₀ (mem_sup_left (hL.muOne_mem_T₁_of_mem_T hS hu huT))
  have hcov : ∀ s ∈ U ⊔ T, s ∈ Q ∨ t⁻¹ * s ∈ Q := by
    intro s hs
    rw [hPeq] at hs
    obtain ⟨s₀, hs₀, u, hu, rfl⟩ := ncyc_exists_mul_of_mem_sup hL.T_le hs
    obtain ⟨k, hk⟩ := hbgen s₀ hs₀
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hk
    have hs₀' : s₀ = w₁ ^ k * y * z := by rw [mul_assoc, hyz]; group
    have hby : w₁ ^ k * y * u ∈ Q :=
      mul_mem (mem_sup_left (mul_mem (mem_sup_right (zpow_mem (mem_zpowers w₁) k))
        (mem_sup_left hy))) (mem_sup_right hu)
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    · left
      rw [hs₀', hz1, mul_one]
      exact hby
    · right
      rw [hz1] at hs₀'
      have hbt : w₁ ^ k * t = t * w₁ ^ k :=
        (Commute.zpow_left (mem_centralizer_singleton_iff.mp (h.le hw₁T)) k).eq
      have hyt : y * t = t * y := mem_centralizer_singleton_iff.mp (h.le (hT₁T hy))
      have e : t⁻¹ * (w₁ ^ k * y * t * u) = w₁ ^ k * y * u := by
        calc t⁻¹ * (w₁ ^ k * y * t * u) = t⁻¹ * (w₁ ^ k * (y * t)) * u := by group
          _ = t⁻¹ * (w₁ ^ k * (t * y)) * u := by rw [hyt]
          _ = t⁻¹ * ((w₁ ^ k * t) * y) * u := by group
          _ = t⁻¹ * ((t * w₁ ^ k) * y) * u := by rw [hbt]
          _ = w₁ ^ k * y * u := by group
      rw [hs₀', e]
      exact hby
  obtain ⟨S, hSeq⟩ := hsyl
  have hP2 : IsPGroup 2 (U ⊔ T : Subgroup G) := hSeq ▸ S.isPGroup'
  have hPidx : ¬ 2 ∣ (U ⊔ T).index := hSeq ▸ S.not_dvd_index
  have hG : IsSimpleGroup G := h.setting.1
  obtain ⟨a₀, b₀, hab⟩ : ∃ a b : G, a * b ≠ b * a := h.setting.2.1
  have htP : t ∈ U ⊔ T := mem_sup_right htT
  rcases CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) (P := U ⊔ T) (Q := Q) (u := t)
      hP2 hPidx hMn
      ⟨t, htP, fun s hs => by
        rcases hcov s hs with h1 | h1
        · exact ⟨0, by simpa using h1⟩
        · exact ⟨1, by simpa using h1⟩⟩
      htP htM
      (fun g k _ => by
        rw [pow_mul, h.sq_eq_one, one_pow, mul_one, inv_mul_cancel]
        exact one_mem _)
      (fun g hgP _ => hcov _ hgP)
    with ⟨N, hN, hNcyc, -, htN⟩ | ⟨g, hgM, hgext, -⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := N) with hN1 | hN1
    · apply hab
      have : IsCyclic (G ⧸ N) := hNcyc
      have hcomm := (QuotientGroup.mk' N).isMulCommutative_of_isCyclic_of_ker_le_center (by
        rw [QuotientGroup.ker_mk', hN1]
        exact bot_le)
      exact hcomm.is_comm.comm a₀ b₀
    · exact htN (hN1 ▸ mem_top t)
  · obtain ⟨c, hct, hcT⟩ := h.muOne_exists_conj_of_isExtremalIn hgext
    have hxQ : c * t * c⁻¹ ∈ Q := by rw [hct]; exact hgM
    obtain ⟨m₀, hm₀, u, hu, hmu⟩ := ncyc_exists_mul_of_mem_sup hM₀N hxQ
    rw [sup_comm] at hm₀
    obtain ⟨a, ha, y, hy, hay⟩ := ncyc_exists_mul_of_mem_sup (zpowers_le.mpr (hTN₁ hw₁T)) hm₀
    have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
    rcases mem_zpowers_involution_eq_one_or_eq hw₁2 ha with rfl | rfl
    · refine hL.muOne_false_of_conj_mem_U₁ hS hc hμV hK hμ hcT ?_
      rw [← hmu, ← hay, one_mul]
      exact mul_mem (hT₁U₁ hy) hu
    · refine hL.muOne_false_of_conj_mem_inv hS hc hμV hK hμ hw₁T hw₁2 hw₁S hw₁V hcT ?_
      rw [← hmu, ← hay, show a * y * u * a⁻¹ = a * (y * u) * a⁻¹ by group]
      exact (mem_normalizer_iff.mp (hL.T_le hw₁T) _).mp (mul_mem (hT₁U₁ hy) hu)

end CFSG.SeitzReduction.RankOne
