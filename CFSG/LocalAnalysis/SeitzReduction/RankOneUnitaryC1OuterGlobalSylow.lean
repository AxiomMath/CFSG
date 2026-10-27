module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGlobalSquare
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterMuOneTwo
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGlobalFusion

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

theorem muOneCent_sq_mem_of_zpow_mem {G : Type} [Group G] (H : Subgroup G) {b : G} {n : ℕ}
    (hbn : b ^ (2 ^ n) = 1) {k : ℤ} (hk : Odd k) (hb : b ^ (2 * k) ∈ H) : b ^ 2 ∈ H := by
  obtain ⟨u, v, huv⟩ := (Int.isCoprime_two_right.mpr hk).pow_right (n := n)
  have key : (2 : ℤ) = 2 * k * u + ((2 ^ n : ℕ) : ℤ) * (2 * v) := by
    push_cast
    linear_combination -2 * huv
  have e : b ^ 2 = (b ^ (2 * k)) ^ u * (b ^ (2 ^ n)) ^ (2 * v) := by
    rw [← zpow_natCast b (2 ^ n), ← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm (2 * k) u,
      mul_comm u, ← key]
    norm_cast
  rw [e, hbn, one_zpow, mul_one]
  exact zpow_mem hb u

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem muOneCent_exists_sq_of_mem (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {b : G} (hbT : b ∈ T)
    (hb2 : b ^ 2 ∉ szT₁ L T ⊔ zpowers t) {w : G} (hw : w ∈ szT₁ L T ⊔ zpowers b)
    (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) : ∃ s : G, s ^ 2 = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, hsqT, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hwT : w ∈ T := (sup_le (szT₁_le_left L T) (zpowers_le.mpr hbT)) hw
  have hconjT : ∀ s ∈ T, ∀ z ∈ szT₁ L T, s * z * s⁻¹ ∈ szT₁ L T := fun s hs z hz =>
    (mem_normalizer_iff.mp (hTN₁ hs) z).mp hz
  have hbN : zpowers b ≤ normalizer (szT₁ L T : Set G) := zpowers_le.mpr (hTN₁ hbT)
  rw [sup_comm] at hw
  obtain ⟨a, ha, y, hy, hay⟩ := ncyc_exists_mul_of_mem_sup hbN hw
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
  have hww : w * w = 1 := by rw [← sq, hw2]
  have e2 : b ^ k * y * b ^ k = y⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [mul_assoc (b ^ k * y), hay]
    exact hww
  have hb2k : b ^ (2 * k) ∈ szT₁ L T := by
    have e : b ^ (2 * k) = (b ^ k * y⁻¹ * (b ^ k)⁻¹) * y⁻¹ := by
      calc b ^ (2 * k) = b ^ k * b ^ k := by rw [two_mul, zpow_add]
        _ = (b ^ k * y⁻¹ * (b ^ k)⁻¹) * (b ^ k * y * b ^ k) := by group
        _ = (b ^ k * y⁻¹ * (b ^ k)⁻¹) * y⁻¹ := by rw [e2]
    rw [e]
    exact mul_mem (hconjT _ (zpow_mem hbT k) _ (inv_mem hy)) (inv_mem hy)
  obtain ⟨n, hn⟩ := h.isPGroup ⟨b, hbT⟩
  have hbn : b ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨j, rfl⟩ : Even k := by
    by_contra hodd
    rw [Int.not_even_iff_odd] at hodd
    exact hb2 (mem_sup_left (muOneCent_sq_mem_of_zpow_mem _ hbn hodd hb2k))
  obtain ⟨D, -, hDN, hTD, hcent, hconj⟩ := h.exists_cartan_le_of_card_sylow hS2
  obtain ⟨nn, hnn, hnD⟩ := hconj (b ^ j) (zpow_mem hbT j)
  obtain ⟨c, hcdef⟩ : ∃ c, c = nn⁻¹ * b ^ j := ⟨_, rfl⟩
  rw [← hcdef] at hnD
  have hcT : c ∈ T := by
    rw [hcdef]
    exact mul_mem (inv_mem (szT₁_le_left L T hnn)) (zpow_mem hbT j)
  have hy₂ : c ^ 2 * w⁻¹ ∈ szT₁ L T := by
    rw [← hay, hcdef, zpow_add, show (nn⁻¹ * b ^ j) ^ 2 * (b ^ j * b ^ j * y)⁻¹ =
        nn⁻¹ * (b ^ j * nn⁻¹ * (b ^ j)⁻¹) * ((b ^ j * b ^ j) * y⁻¹ * (b ^ j * b ^ j)⁻¹) by
      rw [sq]; group]
    exact mul_mem (mul_mem (inv_mem hnn) (hconjT _ (zpow_mem hbT j) _ (inv_mem hnn)))
      (hconjT _ (mul_mem (zpow_mem hbT j) (zpow_mem hbT j)) _ (inv_mem hy))
  have hcNorm : c ∈ normalizer (D : Set G) := by
    have hc' : c⁻¹ ∈ normalizer (D : Set G) := mem_normalizer_of_forall_inv_mul_mul_mem
      fun x hx => by rw [inv_inv]; exact hnD x hx
    simpa using inv_mem hc'
  have hc4T₁ : c ^ 4 ∈ szT₁ L T := by
    have e : c ^ 4 = (c ^ 2 * w⁻¹) * (w * (c ^ 2 * w⁻¹) * w⁻¹) := by
      calc c ^ 4 = c ^ 2 * c ^ 2 * (w * w)⁻¹ := by
            rw [hww, inv_one, mul_one, ← pow_add]
        _ = (c ^ 2 * w⁻¹) * (w * (c ^ 2 * w⁻¹) * w⁻¹) := by group
    rw [e]
    exact mul_mem hy₂ (hconjT w hwT _ hy₂)
  have hT₁D : ∀ z ∈ szT₁ L T, z ∈ normalizer (D : Set G) → z = 1 := by
    intro z hz hzN
    refine hcent z hz fun x hx => ?_
    have h1 : z * x * z⁻¹ * x⁻¹ ∈ D := mul_mem ((mem_normalizer_iff.mp hzN x).mp hx) (inv_mem hx)
    have h2 : z * x * z⁻¹ * x⁻¹ ∈ szT₁ L T := by
      rw [show z * x * z⁻¹ * x⁻¹ = z * (x * z⁻¹ * x⁻¹) by group]
      exact mul_mem hz ((mem_normalizer_iff.mp (hDN hx) _).mp (inv_mem hz))
    have h3 : z * x * z⁻¹ * x⁻¹ ∈ szT₁ L T ⊓ D := mem_inf.mpr ⟨h2, h1⟩
    rw [hTD, mem_bot] at h3
    calc z * x = z * x * z⁻¹ * x⁻¹ * (x * z) := by group
      _ = x * z := by rw [h3, one_mul]
  have hc4 : c ^ 4 = 1 := hT₁D _ hc4T₁ (pow_mem hcNorm 4)
  have hc2T : c ^ 2 ∈ T := pow_mem hcT 2
  have hc22 : (c ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hc4
  have hc2S : c ^ 2 ∉ szT₁ L T ⊔ zpowers t := by
    intro hc2
    apply hwS
    rw [show w = (c ^ 2 * w⁻¹)⁻¹ * c ^ 2 by group]
    exact mul_mem (mem_sup_left (inv_mem hy₂)) hc2
  obtain ⟨W, -, -, hWcard, -, -, -, hWiff⟩ := h.exists_W_of_card_sylow hS2 hc2T hc22 hc2S
  obtain ⟨z, hzdef⟩ : ∃ z, z = w * (c ^ 2)⁻¹ := ⟨_, rfl⟩
  have hz : z ∈ szT₁ L T := by
    rw [hzdef, show w * (c ^ 2)⁻¹ = (c ^ 2 * w⁻¹)⁻¹ by group]
    exact inv_mem hy₂
  have hcc : c ^ 2 * c ^ 2 = 1 := by rw [← sq]; exact hc22
  have hzw : z * c ^ 2 = w := by rw [hzdef]; group
  have hzW : z ∈ W := by
    refine (hWiff z hz).mp ?_
    have e1 : c ^ 2 * z * (c ^ 2)⁻¹ = z⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      calc z * (c ^ 2 * z * (c ^ 2)⁻¹) = (z * c ^ 2) * (z * c ^ 2) * (c ^ 2 * c ^ 2)⁻¹ := by
            group
        _ = 1 := by rw [hzw, hww, hcc, inv_one, mul_one]
    rw [e1, show z⁻¹ * z⁻¹ = (z ^ 2)⁻¹ by rw [sq]; group]
    exact inv_mem (hsqT z hz)
  obtain ⟨e₀, -, he₀⟩ := h.muOneCent_exists_conj_of_mem_W hS2 hc2T hc22 hc2S hWcard hWiff hzW
  refine ⟨e₀ * c * e₀⁻¹, ?_⟩
  rw [show (e₀ * c * e₀⁻¹) ^ 2 = e₀ * c ^ 2 * e₀⁻¹ by rw [sq, sq]; group, he₀, hzw]

end U3Start

theorem U3C1OuterLevelData.muOneCent_false_of_sylow {G : Type}
    [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ D : Subgroup G} {d : G}
    {V U U₁ : Subgroup G} (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1)
    (hL : U3C1OuterLevelData G L f t T D V U U₁ 1) (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hsyl : ∃ S : Sylow 2 G, (S : Subgroup G) = U ⊔ T) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨htT, -, -, hTN₁, -, hMn, -⟩ := h.start_of_card_sylow hS2
  have hT₁T : szT₁ L T ≤ T := szT₁_le_left L T
  have hMT : szT₁ L T ⊔ zpowers t ≤ T := sup_le hT₁T (zpowers_le.mpr htT)
  obtain ⟨b, hbT, hbgen, htb⟩ := h.exists_gen_of_outer_involution hS2 hS.outer
  by_cases hb2 : b ^ 2 ∈ szT₁ L T ⊔ zpowers t
  ·
    have hbev : ∀ j : ℤ, b ^ (j + j) ∈ szT₁ L T ⊔ zpowers t := fun j => by
      rw [← two_mul, zpow_mul, zpow_ofNat]
      exact zpow_mem hb2 j
    have hMconj : ∀ x ∈ T, ∀ m ∈ szT₁ L T ⊔ zpowers t, x * m * x⁻¹ ∈ szT₁ L T ⊔ zpowers t := by
      intro x hx m hm
      have := hMn.conj_mem ⟨m, hMT hm⟩ (mem_subgroupOf.mpr hm) ⟨x, hx⟩
      rw [mem_subgroupOf] at this
      simpa using this
    have hodd : ∀ {x : G} {i : ℤ}, x ∉ szT₁ L T ⊔ zpowers t →
        (b ^ i)⁻¹ * x ∈ szT₁ L T ⊔ zpowers t → Odd i := by
      intro x i hxM hi
      by_contra hev
      rw [Int.not_odd_iff_even] at hev
      obtain ⟨j, rfl⟩ := hev
      apply hxM
      rw [show x = b ^ (j + j) * ((b ^ (j + j))⁻¹ * x) by group]
      exact mul_mem (hbev j) hi
    refine hL.muOne_false_of_sylow_of_index_two hS hμV ?_ hsyl
    intro s hs s' hs' hsM hs'M
    obtain ⟨k, hk⟩ := hbgen s hs
    obtain ⟨k', hk'⟩ := hbgen s' hs'
    obtain ⟨i, rfl⟩ := hodd hsM hk
    obtain ⟨i', rfl⟩ := hodd hs'M hk'
    have e : s * s'⁻¹ = (b ^ (2 * i + 1) * ((b ^ (2 * i + 1))⁻¹ * s *
        ((b ^ (2 * i' + 1))⁻¹ * s')⁻¹) * (b ^ (2 * i + 1))⁻¹) * b ^ ((i - i') + (i - i')) := by
      group
    rw [e]
    exact mul_mem (hMconj _ (zpow_mem hbT _) _ (mul_mem hk (inv_mem hk'))) (hbev (i - i'))
  ·
    obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
    have hPeq := hL.muOne_sup_eq hS
    have hM₀T : szT₁ L T ⊔ zpowers b ≤ T := sup_le hT₁T (zpowers_le.mpr hbT)
    have hM₀N : szT₁ L T ⊔ zpowers b ≤ normalizer (U₁ : Set G) := hM₀T.trans hL.T_le
    have hcommT := h.commutator_le_szT₁_of_card_sylow hS2
    have hM₀n : ∀ s ∈ T, ∀ m ∈ szT₁ L T ⊔ zpowers b, s * m * s⁻¹ ∈ szT₁ L T ⊔ zpowers b := by
      intro s hs m hm
      have hcm : s * m * s⁻¹ * m⁻¹ ∈ szT₁ L T := by
        have := hcommT (commutator_mem_commutator hs (hM₀T hm))
        rwa [commutatorElement_def] at this
      rw [show s * m * s⁻¹ = (s * m * s⁻¹ * m⁻¹) * m by group]
      exact mul_mem (mem_sup_left hcm) hm
    set Q := (szT₁ L T ⊔ zpowers b) ⊔ U₁ with hQdef
    have hMn' : ∀ s ∈ U ⊔ T, ∀ m ∈ Q, s * m * s⁻¹ ∈ Q := by
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
    have hQT : ∀ m ∈ Q, m ∈ T → m ∈ szT₁ L T ⊔ zpowers b := by
      intro m hm hmT
      obtain ⟨m₀, hm₀, u, hu, hmu⟩ := ncyc_exists_mul_of_mem_sup hM₀N hm
      have huT : u ∈ T := by
        rw [show u = m₀⁻¹ * m by rw [← hmu]; group]
        exact mul_mem (inv_mem (hM₀T hm₀)) hmT
      rw [← hmu]
      exact mul_mem hm₀ (mem_sup_left (hL.muOne_mem_T₁_of_mem_T hS hu huT))
    have htM : t ∉ Q := fun htM => htb (hQT t htM htT)
    have hcov : ∀ s ∈ U ⊔ T, s ∈ Q ∨ t⁻¹ * s ∈ Q := by
      intro s hs
      rw [hPeq] at hs
      obtain ⟨s₀, hs₀, u, hu, rfl⟩ := ncyc_exists_mul_of_mem_sup hL.T_le hs
      obtain ⟨k, hk⟩ := hbgen s₀ hs₀
      obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hk
      have hs₀' : s₀ = b ^ k * y * z := by rw [mul_assoc, hyz]; group
      have hby : b ^ k * y * u ∈ Q :=
        mul_mem (mem_sup_left (mul_mem (mem_sup_right (zpow_mem (mem_zpowers b) k))
          (mem_sup_left hy))) (mem_sup_right hu)
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
      · left
        rw [hs₀', hz1, mul_one]
        exact hby
      · right
        rw [hz1] at hs₀'
        have hbt : b ^ k * t = t * b ^ k :=
          (Commute.zpow_left (mem_centralizer_singleton_iff.mp (h.le hbT)) k).eq
        have hyt : y * t = t * y := mem_centralizer_singleton_iff.mp (h.le (hT₁T hy))
        have e : t⁻¹ * (b ^ k * y * t * u) = b ^ k * y * u := by
          calc t⁻¹ * (b ^ k * y * t * u) = t⁻¹ * (b ^ k * (y * t)) * u := by group
            _ = t⁻¹ * (b ^ k * (t * y)) * u := by rw [hyt]
            _ = t⁻¹ * ((b ^ k * t) * y) * u := by group
            _ = t⁻¹ * ((t * b ^ k) * y) * u := by rw [hbt]
            _ = b ^ k * y * u := by group
        rw [hs₀', e]
        exact hby
    obtain ⟨S, hSeq⟩ := hsyl
    have hP2 : IsPGroup 2 (U ⊔ T : Subgroup G) := hSeq ▸ S.isPGroup'
    have hPidx : ¬ 2 ∣ (U ⊔ T).index := hSeq ▸ S.not_dvd_index
    have hG : IsSimpleGroup G := h.setting.1
    obtain ⟨a₀, b₀, hab⟩ : ∃ a b : G, a * b ≠ b * a := h.setting.2.1
    have htP : t ∈ U ⊔ T := mem_sup_right htT
    rcases CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) (P := U ⊔ T) (Q := Q)
        (u := t) hP2 hPidx hMn'
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
      have hQP : Q ≤ U ⊔ T := by
        rw [hPeq]
        exact sup_le (hM₀T.trans le_sup_left) le_sup_right
      have hxQ : c * t * c⁻¹ ∈ Q := by rw [hct]; exact hgM
      have htt : t * t = 1 := by rw [← sq, h.sq_eq_one]
      have hx2 : c * t * c⁻¹ * (c * t * c⁻¹) = 1 := by
        rw [show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, htt, mul_one,
          mul_inv_cancel]
      rcases hL.muOne_classify hS (hQP hxQ) hx2 with h1 | h1 | ⟨w, hwT, hw2, hwS, h1⟩
      · exact hL.muOne_false_of_conj_mem_U₁ hS hc hμV hK hμ hcT h1
      · apply htM
        rw [show t = (c * t * c⁻¹ * t⁻¹)⁻¹ * (c * t * c⁻¹) by group]
        exact mul_mem (mem_sup_right (inv_mem h1)) hxQ
      · have hwQ : w ∈ Q := by
          rw [show w = (c * t * c⁻¹ * w⁻¹)⁻¹ * (c * t * c⁻¹) by group]
          exact mul_mem (mem_sup_right (inv_mem h1)) hxQ
        rcases hL.muOne_dichotomy hS hc hμV hK hμ hwT hw2 hwS with hcen | hinv
        · obtain ⟨c', -, hc'⟩ :=
            hL.muOneCent_exists_conj_eq hS hc hμV hK hμ hwT hw2 hwS hcen hcT h1
          obtain ⟨s, hs⟩ := h.muOneCent_exists_sq_of_mem hS2 hbT hb2 (hQT w hwQ hwT) hw2 hwS
          refine hS.muOneCent_conj_ne_sq (c' * c) s ?_
          rw [hs, ← hc']
          group
        · exact hL.muOne_false_of_conj_mem_inv hS hc hμV hK hμ hwT hw2 hwS hinv hcT h1

theorem u3C1OuterMuOneSylowInput_holds :
    U3C1OuterMuOneSylowInput := by
  intro G _ _ L f t T R₂ D d V U U₁ hS hL hsyl
  by_contra hμV
  exact hL.muOneCent_false_of_sylow hS hμV hsyl

@[expose] def U3C1OuterMuOneNormInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G), U3C1OuterStepHyp G L f t T R₂ D d V 1 →
    U3C1OuterLevelData G L f t T D V U U₁ 1 → ¬ U₁ ≤ centralizer (V : Set G) →
    (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U ⊔ T) →
    ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t → (∀ r ∈ V, w * r * w⁻¹ = r) →
      (∀ s : G, s ^ 2 ≠ w) → ∀ g ∈ normalizer ((U ⊔ T : Subgroup G) : Set G),
        (∃ P : Subgroup G, IsPGroup 2 P ∧ U ⊔ T ≤ P ∧ g ∈ P) → g * t * g⁻¹ ≠ w

theorem u3C1OuterMuOneInput_of_norm
    (hN : U3C1OuterMuOneNormInput) : U3C1OuterMuOneInput := by
  intro G _ _ L f t T R₂ D d V U U₁ hS hL hnS
  by_contra hμV
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  obtain ⟨g, hgN, hgS, P, hP2, hSP, hgP⟩ :=
    exists_normalizer_not_mem_of_not_isSylow hL.isSylowOf.isPGroup hnS
  have htT := (hS.start.start_of_card_sylow hS.card_sylow).1
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hgT : ∀ s ∈ T, g * s * g⁻¹ ∈ U ⊔ T := fun s hs =>
    (mem_normalizer_iff.mp hgN s).mp (mem_sup_right hs)
  have htt : t * t = 1 := by rw [← sq, hS.start.sq_eq_one]
  have hx2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, htt, mul_one,
      mul_inv_cancel]
  rcases hL.muOne_classify hS (hgT t htT) hx2 with h1 | h1 | ⟨w, hwT, hw2, hwS, h1⟩
  · exact hL.muOne_false_of_conj_mem_U₁ hS hc hμV hK hμ hgT h1
  · exact hgS (hL.muOne_mem_sup_of_conj hS hc hμV hK hμ hP2 hSP hgP h1)
  · rcases hL.muOne_dichotomy hS hc hμV hK hμ hwT hw2 hwS with hcen | hinv
    · obtain ⟨c, hcT, hcx⟩ :=
        hL.muOneCent_exists_conj_eq hS hc hμV hK hμ hwT hw2 hwS hcen hgT h1
      have hcS : c ∈ U ⊔ T := mem_sup_left (hL.U₁_le (hT₁U₁ hcT))
      have hcgN : c * g ∈ normalizer ((U ⊔ T : Subgroup G) : Set G) :=
        mul_mem (Subgroup.le_normalizer hcS) hgN
      have hcg : c * g * t * (c * g)⁻¹ = w := by
        rw [show c * g * t * (c * g)⁻¹ = c * (g * t * g⁻¹) * c⁻¹ by group]
        exact hcx
      by_cases hsq : ∃ s : G, s ^ 2 = w
      · obtain ⟨s, rfl⟩ := hsq
        exact hS.muOneCent_conj_ne_sq (c * g) s hcg
      · push Not at hsq
        exact hN G L f t T R₂ D d V U U₁ hS hL hμV hnS w hwT hw2 hwS hcen hsq (c * g) hcgN
          ⟨P, hP2, hSP, mul_mem (hSP hcS) hgP⟩ hcg
    · exact hL.muOne_false_of_conj_mem_inv hS hc hμV hK hμ hwT hw2 hwS hinv hgT h1

end CFSG.SeitzReduction.RankOne
