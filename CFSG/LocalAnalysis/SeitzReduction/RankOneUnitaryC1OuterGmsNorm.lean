module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsLocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterLevelData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G}

section Comm

variable (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1)
  (hL : U3C1OuterLevelData G L f t T D V U U₁ 1)
include hS hL

theorem gms_mem_sup_of_comm_mem_szA₁ {w : G} (hwT : w ∈ T) (hwV : ∀ r ∈ V, w * r * w⁻¹ = r⁻¹)
    {W : Subgroup G}
    (hWiff : ∀ y ∈ szT₁ L T, (y⁻¹ * (w * y * w⁻¹) ∈ szA₁ (szT₁ L T) ↔ y ∈ W)) {c : G}
    (hcU : c ∈ U₁) (hcw : c * w * c⁻¹ * w⁻¹ ∈ szA₁ (szT₁ L T)) : c ∈ W ⊔ V := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := hS.start.start_of_card_sylow hS.card_sylow
  have htC := hS.start.mem_centralizer_szT₁
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.mp (hS.start.le hwT)
  have hlam := hL.lambda hS.start hS.card_sylow hS.conf
  have hV₁N : szT₁ L T ≤ normalizer (outerV₁ L T U₁ : Set G) := fun y hy =>
    mem_normalizer_outerV₁ (Subgroup.le_normalizer (hT₁U₁ hy)) (Subgroup.le_normalizer hy)
  have hA₁V₁ : szA₁ (szT₁ L T) ≤ outerV₁ L T U₁ := fun a ha =>
    mem_outerV₁.mpr ⟨hT₁U₁ (szA₁_le _ ha), (mem_szA₁.mp ha).2⟩
  rw [hlam] at hcU
  obtain ⟨y, hy, z, hz, rfl⟩ := ncyc_exists_mul_of_mem_sup hV₁N hcU
  obtain ⟨hzU, hzC⟩ := mem_outerV₁.mp hz
  set a := y * z * w * (y * z)⁻¹ * w⁻¹ with ha
  have haA : a ∈ szA₁ (szT₁ L T) := hcw
  have hwy : w * y * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) y).mp hy
  have hwz : w * z * w⁻¹ ∈ outerV₁ L T U₁ :=
    (mem_normalizer_iff.mp (mem_normalizer_outerV₁ (hL.T_le hwT) (hTN₁ hwT)) z).mp hz
  have hay : y * a = a * y := mem_centralizer_iff.mp (mem_szA₁.mp haA).2 y hy
  have hc1 : y * a⁻¹ = a⁻¹ * y := (Commute.inv_right hay).eq
  have hrel : y⁻¹ * (w * y * w⁻¹) = a⁻¹ * (z * (w * z * w⁻¹)⁻¹) := by
    have e1 : w * y * w⁻¹ * (w * z * w⁻¹) = a⁻¹ * (y * z) := by rw [ha]; group
    calc y⁻¹ * (w * y * w⁻¹) =
          y⁻¹ * (w * y * w⁻¹ * (w * z * w⁻¹)) * (w * z * w⁻¹)⁻¹ := by group
      _ = y⁻¹ * (a⁻¹ * (y * z)) * (w * z * w⁻¹)⁻¹ := by rw [e1]
      _ = y⁻¹ * (a⁻¹ * y) * z * (w * z * w⁻¹)⁻¹ := by group
      _ = y⁻¹ * (y * a⁻¹) * z * (w * z * w⁻¹)⁻¹ := by rw [hc1]
      _ = a⁻¹ * (z * (w * z * w⁻¹)⁻¹) := by group
  have hRV : a⁻¹ * (z * (w * z * w⁻¹)⁻¹) ∈ outerV₁ L T U₁ :=
    mul_mem (hA₁V₁ (inv_mem haA)) (mul_mem hz (inv_mem hwz))
  have hA : y⁻¹ * (w * y * w⁻¹) ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨mul_mem (inv_mem hy) hwy, ?_⟩
    rw [hrel]
    exact (mem_outerV₁.mp hRV).2
  have hyW : y ∈ W := (hWiff y hy).mp hA
  have hb : w * z * w⁻¹ * z⁻¹ ∈ szA₁ (szT₁ L T) := by
    have e2 : z * (w * z * w⁻¹)⁻¹ = a * (y⁻¹ * (w * y * w⁻¹)) := by rw [hrel]; group
    have h1 : z * (w * z * w⁻¹)⁻¹ ∈ szA₁ (szT₁ L T) := by rw [e2]; exact mul_mem haA hA
    have h2 := inv_mem h1
    rwa [mul_inv_rev, inv_inv] at h2
  have hσz := hL.muOne_comm_t_mem hS (hL.U₁_le hzU)
  set b := w * z * w⁻¹ * z⁻¹ with hbdef
  have hbt : b * t = t * b := mem_centralizer_iff.mp htC b (szA₁_le _ hb)
  have htb : t * b⁻¹ * t⁻¹ = b⁻¹ := by
    rw [(Commute.inv_right (Commute.symm hbt)).eq, mul_inv_cancel_right]
  have hbσ : b * (z * t * z⁻¹ * t⁻¹) = (z * t * z⁻¹ * t⁻¹) * b :=
    hS.conf.comm _ (hS.conf.le hb) _ hσz
  have e3 : w * (z * t * z⁻¹ * t⁻¹) * w⁻¹ = z * t * z⁻¹ * t⁻¹ := by
    have hwz' : w * z * w⁻¹ = b * z := by rw [hbdef]; group
    have hwtw : w * t * w⁻¹ = t := by rw [hwt, mul_inv_cancel_right]
    calc w * (z * t * z⁻¹ * t⁻¹) * w⁻¹ =
          (w * z * w⁻¹) * (w * t * w⁻¹) * (w * z * w⁻¹)⁻¹ * (w * t * w⁻¹)⁻¹ := by group
      _ = (b * z) * t * (b * z)⁻¹ * t⁻¹ := by rw [hwz', hwtw]
      _ = b * (z * t * z⁻¹ * t⁻¹) * (t * b⁻¹ * t⁻¹) := by group
      _ = b * (z * t * z⁻¹ * t⁻¹) * b⁻¹ := by rw [htb]
      _ = z * t * z⁻¹ * t⁻¹ := by rw [hbσ, mul_inv_cancel_right]
  have e4 := hwV _ hσz
  rw [e3] at e4
  have hσ2 : (z * t * z⁻¹ * t⁻¹) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [e4]
    exact mul_inv_cancel _
  have hzTV := hL.muOne_mem_sup_of_comm_t_mem_szA₁ hS hzU (hS.conf.omega _ hσz hσ2)
  obtain ⟨y₁, hy₁, r, hr, hyr⟩ := ncyc_exists_mul_of_mem_sup (hL.muOne_T₁_le_normalizer hS) hzTV
  have hy₁A : y₁ ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨hy₁, mem_centralizer_iff.mpr fun y₀ hy₀ => ?_⟩
    have hz₀ := mem_centralizer_iff.mp hzC y₀ hy₀
    have hr₀ := hL.muOne_T₁_comm hS hy₀ hr
    rw [show y₁ = z * r⁻¹ by rw [← hyr]; group]
    calc y₀ * (z * r⁻¹) = (y₀ * z) * r⁻¹ := by group
      _ = z * y₀ * r⁻¹ := by rw [hz₀]
      _ = z * (y₀ * r⁻¹) := by group
      _ = z * (r⁻¹ * y₀) := by rw [(Commute.inv_right hr₀).eq]
      _ = z * r⁻¹ * y₀ := by group
  have hzV : z ∈ V := by rw [← hyr]; exact mul_mem (hS.conf.le hy₁A) hr
  exact mul_mem (mem_sup_left hyW) (mem_sup_right hzV)

end Comm

end U3C1OuterLevelData

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem t_not_mem_T₁ : t ∉ szT₁ L T := fun h' =>
  hW.level.t_not_mem ((le_sup_left.trans hW.level.sup_le_U₁) h')

theorem sq_mul_t_not_mem {τ : G} (hτ : τ ∈ T) : τ ^ 2 * t ∉ szT₁ L T := by
  intro hτt
  have h := hW.step.start
  by_cases hτH : τ ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨y, hy, e, he, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hτH
    have hye : Commute y e := commute_of_mem_zpowers he
      (mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy)
    have he2 : e ^ 2 = 1 := by
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one he with rfl | rfl
      · exact one_pow 2
      · exact h.sq_eq_one
    rw [hye.mul_pow, he2, mul_one] at hτt
    apply hW.t_not_mem_T₁
    rw [show t = (y ^ 2)⁻¹ * (y ^ 2 * t) by group]
    exact mul_mem (inv_mem (pow_mem hy 2)) hτt
  · obtain ⟨m, -, hm, -⟩ := h.exists_sq_eq_t_of_card_sylow hW.step.card_sylow hτ hτt hτH
    exact hW.step.muOneCent_sq_ne_t m hm

theorem exists_sq_root_mod : ∃ d ∈ T, t * w * (d ^ 2)⁻¹ ∈ szT₁ L T := by
  have h := hW.step.start
  have hS2 := hW.step.card_sylow
  obtain ⟨b, hbT, hbS, hb2⟩ := hW.exists_outer_sq_not_mem
  obtain ⟨j, hcS, hc2⟩ := StrongClosureMod.exists_pow_not_mem h.isPGroup hbT hbS
  have hj : j ≠ 0 := by
    rintro rfl
    simp only [pow_zero, pow_one] at hc2
    exact hb2 hc2
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  have hpow : (b ^ 2 ^ i) ^ 2 = b ^ 2 ^ (i + 1) := by rw [← pow_mul, pow_succ]
  refine ⟨b ^ 2 ^ i, pow_mem hbT _, ?_⟩
  rw [hpow]
  have hcb : b ^ 2 ^ (i + 1) ∈ szT₁ L T ⊔ zpowers b := mem_sup_right (pow_mem (mem_zpowers b) _)
  have hM := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hW.tw_mem (pow_mem hbT _)
    (by rw [hW.tw_sq]; exact one_mem _) hc2 hW.tw_not_mem hcS
  obtain ⟨y, hy, e, he, hye⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hM
  rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one he with he1 | he1
  · rw [he1, mul_one] at hye
    rw [← hye]
    exact hy
  · exfalso
    rw [he1] at hye
    have hyt : y * t = t * y := mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy
    have e : w = y * b ^ 2 ^ (i + 1) := by
      calc w = t⁻¹ * (t * w * (b ^ 2 ^ (i + 1))⁻¹) * b ^ 2 ^ (i + 1) := by group
        _ = t⁻¹ * (y * t) * b ^ 2 ^ (i + 1) := by rw [hye]
        _ = t⁻¹ * (t * y) * b ^ 2 ^ (i + 1) := by rw [hyt]
        _ = y * b ^ 2 ^ (i + 1) := by group
    obtain ⟨g, hg⟩ := h.muOneCent_exists_sq_of_mem hS2 hbT hb2
      (by rw [e]; exact mul_mem (mem_sup_left hy) hcb) hW.w_sq hW.w_not_mem
    exact hW.w_not_sq g hg

theorem sq_mul_w_not_mem {τ : G} (hτ : τ ∈ T) : τ ^ 2 * w⁻¹ ∉ szT₁ L T := by
  intro hτw
  have h := hW.step.start
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hW.step.card_sylow
  obtain ⟨d', hdT, hd⟩ := hW.exists_sq_root_mod
  have hcomm := h.commutator_le_szT₁_of_card_sylow hW.step.card_sylow
  have hk : τ * d'⁻¹ * τ⁻¹ * d' ∈ szT₁ L T := by
    have := hcomm (commutator_mem_commutator hτ (inv_mem hdT))
    rwa [commutatorElement_def, inv_inv] at this
  have hy : d'⁻¹ * ((τ ^ 2 * w⁻¹) * (t * w * (d' ^ 2)⁻¹)) * d' ∈ szT₁ L T := by
    have := (mem_normalizer_iff.mp (hTN₁ (inv_mem hdT)) _).mp (mul_mem hτw hd)
    rwa [inv_inv] at this
  have hwtw : w⁻¹ * t * w = t := by
    rw [mul_assoc, ← hW.wt_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  have htd : t * d'⁻¹ = d'⁻¹ * t :=
    (Commute.inv_right (mem_centralizer_singleton_iff.mp (h.le hdT)).symm).eq
  have e : (τ * d'⁻¹ * τ⁻¹ * d') * (d'⁻¹ * ((τ ^ 2 * w⁻¹) * (t * w * (d' ^ 2)⁻¹)) * d') =
      (τ * d'⁻¹) ^ 2 * t := by
    calc (τ * d'⁻¹ * τ⁻¹ * d') * (d'⁻¹ * ((τ ^ 2 * w⁻¹) * (t * w * (d' ^ 2)⁻¹)) * d') =
          τ * d'⁻¹ * τ * (w⁻¹ * t * w) * d'⁻¹ := by rw [sq, sq]; group
      _ = τ * d'⁻¹ * τ * (t * d'⁻¹) := by rw [hwtw]; group
      _ = τ * d'⁻¹ * τ * (d'⁻¹ * t) := by rw [htd]
      _ = (τ * d'⁻¹) ^ 2 * t := by rw [sq]; group
  apply hW.sq_mul_t_not_mem (mul_mem hτ (inv_mem hdT))
  rw [← e]
  exact mul_mem hk hy

theorem pow_mul_mem {τ : G} (hτ : τ ∈ T) {u : G} (hu : u ∈ U₁) (n : ℕ) :
    (τ ^ n)⁻¹ * (τ * u) ^ n ∈ U₁ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : τ⁻¹ * ((τ ^ n)⁻¹ * (τ * u) ^ n) * τ ∈ U₁ := by
      have := (mem_normalizer_iff.mp (hW.level.T_le (inv_mem hτ)) _).mp ih
      rwa [inv_inv] at this
    rw [show (τ ^ (n + 1))⁻¹ * (τ * u) ^ (n + 1) =
      (τ⁻¹ * ((τ ^ n)⁻¹ * (τ * u) ^ n) * τ) * u by rw [pow_succ, pow_succ]; group]
    exact mul_mem h1 hu

theorem mem_cases {x : G} (hx : x ∈ U ⊔ T) :
    x ∈ U₁ ∨ x * t⁻¹ ∈ U₁ ∨ x * w⁻¹ ∈ U₁ ∨ ∃ n : ℕ, x ^ n * (t * w)⁻¹ ∈ U₁ := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hTU₁ : ∀ x ∈ T, ∀ u ∈ U₁, x * u * x⁻¹ ∈ U₁ := fun x hx u hu =>
    (mem_normalizer_iff.mp (hL.T_le hx) u).mp hu
  rw [hL.muOne_sup_eq hS] at hx
  obtain ⟨τ, hτ, u, hu, rfl⟩ := ncyc_exists_mul_of_mem_sup hL.T_le hx
  by_cases hτH : τ ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨y, hy, e, he, hye⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hτH
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one he with he1 | he1
    · left
      rw [← hye, he1, mul_one]
      exact mul_mem (hT₁U₁ hy) hu
    · right; left
      rw [← hye, he1, show y * t * u * t⁻¹ = y * (t * u * t⁻¹) by group]
      exact mul_mem (hT₁U₁ hy) (hTU₁ t hW.t_mem u hu)
  · obtain ⟨j, hcS, hc2⟩ := StrongClosureMod.exists_pow_not_mem h.isPGroup hτ hτH
    have hcT : τ ^ 2 ^ j ∈ T := pow_mem hτ _
    have hM := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hcT hW.tw_mem hc2
      (by rw [hW.tw_sq]; exact one_mem _) hcS hW.tw_not_mem
    obtain ⟨y, hy, e, he, hye⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hM
    have hpm := hW.pow_mul_mem hτ hu (2 ^ j)
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one he with he1 | he1
    · right; right; right
      refine ⟨2 ^ j, ?_⟩
      rw [he1, mul_one] at hye
      rw [show (τ * u) ^ 2 ^ j * (t * w)⁻¹ = (τ ^ 2 ^ j * (t * w)⁻¹) *
        ((t * w) * ((τ ^ 2 ^ j)⁻¹ * (τ * u) ^ 2 ^ j) * (t * w)⁻¹) by group, ← hye]
      exact mul_mem (hT₁U₁ hy) (hTU₁ _ hW.tw_mem _ hpm)
    ·
      rw [he1] at hye
      have hyt : y * t = t * y := mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy
      have hcw : τ ^ 2 ^ j * w⁻¹ = y := by
        have htt : t * t = 1 := by rw [← sq, h.sq_eq_one]
        calc τ ^ 2 ^ j * w⁻¹ = τ ^ 2 ^ j * (t * w)⁻¹ * t := by group
          _ = y * t * t := by rw [← hye]
          _ = y := by rw [mul_assoc, htt, mul_one]
      rcases j with _ | i
      · right; right; left
        simp only [pow_zero, pow_one] at hcw
        rw [show τ * u * w⁻¹ = (τ * w⁻¹) * (w * u * w⁻¹) by group, hcw]
        exact mul_mem (hT₁U₁ hy) (hTU₁ w hW.w_mem u hu)
      · exfalso
        apply hW.sq_mul_w_not_mem (pow_mem hτ (2 ^ i))
        rw [← pow_mul, ← pow_succ, hcw]
        exact hy

theorem relIndex_U₁_le : U₁.relIndex (U ⊔ T) ≤ 4 * f := by
  have hS := hW.step
  have hL := hW.level
  obtain ⟨hT₁card, -, -, -, -, -, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hU₁T : U₁ ⊓ T = szT₁ L T :=
    le_antisymm (fun z hz => hL.muOne_mem_T₁_of_mem_T hS (mem_inf.mp hz).1 (mem_inf.mp hz).2)
      (le_inf hT₁U₁ (szT₁_le_left L T))
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := U₁) (B := T) hL.T_le
  have hSU : U ⊔ T = U₁ ⊔ T := by rw [hL.muOne_sup_eq hS, sup_comm]
  rw [hU₁T, hT₁card, hL.muOne_card_U₁ hS, ← hSU] at hprod
  have h1 := relIndex_mul_card (H := U₁) (K := U ⊔ T)
  rw [inf_of_le_left (hL.U₁_le.trans le_sup_left), hL.muOne_card_U₁ hS] at h1
  have hT := hW.card_T_le
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  have h2 : U₁.relIndex (U ⊔ T) * (2 ^ f) ^ 5 * (2 ^ f) ^ 3 ≤
      4 * f * (2 ^ f) ^ 5 * (2 ^ f) ^ 3 := by
    rw [h1, hprod]
    calc (2 ^ f) ^ 5 * Nat.card T ≤ (2 ^ f) ^ 5 * (4 * f * (2 ^ f) ^ 3) :=
          Nat.mul_le_mul_left _ hT
      _ = 4 * f * (2 ^ f) ^ 5 * (2 ^ f) ^ 3 := by ring
  have h3 := Nat.le_of_mul_le_mul_right h2 (pow_pos hq0 3)
  exact Nat.le_of_mul_le_mul_right h3 (pow_pos hq0 5)

theorem le_U₁ {X : Subgroup G} (hXS : X ≤ U ⊔ T)
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ szA₁ (szT₁ L T))
    (hXcard : (2 ^ f) ^ 5 ≤ Nat.card X) : X ≤ U₁ := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  obtain ⟨hT₁card, hA₁card, -, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨W, hWT₁, -, hWcard, -, -, -, hWiff⟩ :=
    h.exists_W_of_card_sylow hS2 hW.w_mem hW.w_sq hW.w_not_mem
  obtain ⟨W', hW'T₁, hAW', hW'card, -, -, -, hW'iff⟩ :=
    h.exists_W_of_card_sylow hS2 hW.tw_mem hW.tw_sq hW.tw_not_mem
  have hcommA := hL.muOne_comm_mem_szA₁ hS hc hW.mu hK hμ
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have htN : ∀ u ∈ U₁, t * u * t⁻¹ ∈ U₁ := fun u hu =>
    (mem_normalizer_iff.mp (hL.T_le hW.t_mem) u).mp hu
  have hred : ∀ y ∈ U₁, ∀ u ∈ U₁, ∀ z : G, y * (u * z) * y⁻¹ * (u * z)⁻¹ ∈ szA₁ (szT₁ L T) →
      y * z * y⁻¹ * z⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro y hy u hu z hz
    have e : u * (y * z * y⁻¹ * z⁻¹) * u⁻¹ =
        (y * u * y⁻¹ * u⁻¹)⁻¹ * (y * (u * z) * y⁻¹ * (u * z)⁻¹) := by group
    have h1 : u * (y * z * y⁻¹ * z⁻¹) * u⁻¹ ∈ szA₁ (szT₁ L T) := by
      rw [e]
      exact mul_mem (inv_mem (hcommA y hy u hu)) hz
    have h2 := hL.conj_szA₁ u⁻¹ (hL.U₁_le (inv_mem hu)) _ h1
    rw [show u⁻¹ * (u * (y * z * y⁻¹ * z⁻¹) * u⁻¹) * u⁻¹⁻¹ = y * z * y⁻¹ * z⁻¹ by group] at h2
    rw [h2]
    exact h1
  have hTV : Nat.card (szT₁ L T ⊔ V : Subgroup G) = (2 ^ f) ^ 4 := by
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := V) (B := szT₁ L T) (hL.muOne_T₁_le_normalizer hS)
    have hinf : V ⊓ szT₁ L T = szA₁ (szT₁ L T) := le_antisymm
      (fun z hz => mem_szA₁.mpr ⟨(mem_inf.mp hz).2, hS.conf.le_centralizer (mem_inf.mp hz).1⟩)
      (le_inf hS.conf.le (szA₁_le _))
    rw [hinf, hA₁card, hS.conf.card, hT₁card, sup_comm] at h1
    apply Nat.eq_of_mul_eq_mul_right hq0
    rw [h1]
    ring
  have hW'V : Nat.card (W' ⊔ V : Subgroup G) ≤ (2 ^ f) ^ 3 := by
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := V) (B := W') (fun y hy => hL.muOne_T₁_le_normalizer hS (hW'T₁ hy))
    have hinf : 2 ^ f ≤ Nat.card (V ⊓ W' : Subgroup G) := by
      rw [← hA₁card]
      exact Subgroup.card_le_of_le (le_inf hS.conf.le hAW')
    rw [hS.conf.card, hW'card, sup_comm] at h1
    have h2 : Nat.card (W' ⊔ V : Subgroup G) * 2 ^ f ≤ (2 ^ f) ^ 3 * 2 ^ f := by
      calc Nat.card (W' ⊔ V : Subgroup G) * 2 ^ f ≤
            Nat.card (W' ⊔ V : Subgroup G) * Nat.card (V ⊓ W' : Subgroup G) :=
            Nat.mul_le_mul_left _ hinf
        _ = (2 ^ f) ^ 3 * 2 ^ f := by rw [h1]; ring
    exact Nat.le_of_mul_le_mul_right h2 hq0
  have hrT₁U₁ : (szT₁ L T).relIndex U₁ = (2 ^ f) ^ 2 := by
    have e2 := relIndex_mul_card (H := szT₁ L T) (K := U₁)
    rw [inf_of_le_left hT₁U₁, hT₁card, hL.muOne_card_U₁ hS] at e2
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq0 3)
    rw [e2]
    ring
  have hne : U₁.relIndex (U ⊔ T) ≠ 0 := by
    intro h0
    have h1 := relIndex_mul_card (H := U₁) (K := U ⊔ T)
    rw [h0, zero_mul] at h1
    exact (Nat.card_pos (α := (U ⊔ T : Subgroup G))).ne' h1.symm
  have hrX : U₁.relIndex X ≤ 4 * f :=
    (Subgroup.relIndex_le_of_le_right hXS hne).trans hW.relIndex_U₁_le
  set Y := U₁ ⊓ X with hYdef
  have hcardX : Nat.card X = U₁.relIndex X * Nat.card Y :=
    (relIndex_mul_card (H := U₁) (K := X)).symm
  have hcardY : Nat.card Y = (szT₁ L T).relIndex Y * Nat.card (szT₁ L T ⊓ Y : Subgroup G) :=
    (relIndex_mul_card (H := szT₁ L T) (K := Y)).symm
  have h4f : 4 * f * (2 ^ f) ^ 3 < (2 ^ f) ^ 5 := by
    have hfq : f < 2 ^ f := Nat.lt_two_pow_self
    have h1 : 4 * f < 2 ^ f * 2 ^ f :=
      calc 4 * f < 4 * 2 ^ f := by omega
        _ ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_right _ hq4
    calc 4 * f * (2 ^ f) ^ 3 < 2 ^ f * 2 ^ f * (2 ^ f) ^ 3 :=
          Nat.mul_lt_mul_of_pos_right h1 (pow_pos hq0 3)
      _ = (2 ^ f) ^ 5 := by ring
  have hq5 : 2 * (2 ^ f) ^ 4 < (2 ^ f) ^ 5 := by
    calc 2 * (2 ^ f) ^ 4 < 2 ^ f * (2 ^ f) ^ 4 :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = (2 ^ f) ^ 5 := by ring
  by_cases hC1 : ∃ x ∈ X, ∃ n : ℕ, x ^ n * (t * w)⁻¹ ∈ U₁
  · exfalso
    obtain ⟨x, hx, n, hxn⟩ := hC1
    have hYle : Y ≤ W' ⊔ V := fun y hy => by
      obtain ⟨hyU, hyX⟩ := mem_inf.mp hy
      have h1 := hXc y hyX (x ^ n) (pow_mem hx n)
      rw [show x ^ n = (x ^ n * (t * w)⁻¹) * (t * w) by group] at h1
      exact hL.gms_mem_sup_of_comm_mem_szA₁ hS hW.tw_mem (fun r hr => hW.tw_inv hr) hW'iff hyU
        (hred y hyU _ hxn (t * w) h1)
    have hYc : Nat.card Y ≤ (2 ^ f) ^ 3 := (Subgroup.card_le_of_le hYle).trans hW'V
    have h1 : Nat.card X ≤ 4 * f * (2 ^ f) ^ 3 := by
      rw [hcardX]
      exact Nat.mul_le_mul hrX hYc
    omega
  push Not at hC1
  have hcover : ∀ x ∈ X, x ∈ U₁ ∨ x * t⁻¹ ∈ U₁ ∨ x * w⁻¹ ∈ U₁ := fun x hx => by
    rcases hW.mem_cases (hXS hx) with h1 | h1 | h1 | ⟨n, h1⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
    · exact absurd h1 (hC1 x hx n)
  by_contra hXU
  by_cases hA : ∃ x ∈ X, x * t⁻¹ ∈ U₁
  · by_cases hB : ∃ x ∈ X, x * w⁻¹ ∈ U₁
    · obtain ⟨x₁, hx₁, h₁⟩ := hA
      obtain ⟨x₂, hx₂, h₂⟩ := hB
      apply hC1 (x₁ * x₂) (mul_mem hx₁ hx₂) 1
      rw [pow_one, show x₁ * x₂ * (t * w)⁻¹ = (x₁ * t⁻¹) * (t * (x₂ * w⁻¹) * t⁻¹) by group]
      exact mul_mem h₁ (htN _ h₂)
    ·
      push Not at hB
      obtain ⟨x₁, hx₁, hx₁U⟩ := hA
      have hYA : Y ≤ szT₁ L T ⊔ V := fun y hy => by
        obtain ⟨hyU, hyX⟩ := mem_inf.mp hy
        have h1 := hXc y hyX x₁ hx₁
        rw [show x₁ = (x₁ * t⁻¹) * t by group] at h1
        exact hL.muOne_mem_sup_of_comm_t_mem_szA₁ hS hyU (hred y hyU _ hx₁U t h1)
      have hXle : X ≤ U₁ ⊔ zpowers t := fun x hx => by
        rcases hcover x hx with h1 | h1 | h1
        · exact mem_sup_left h1
        · rw [show x = (x * t⁻¹) * t by group]
          exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers t))
        · exact absurd h1 (hB x hx)
      have hr := RankOne.Endings.relIndex_sup_zpowers_eq_two hL.t_not_mem
        (hL.T_le hW.t_mem) (by rw [← sq]; exact h.sq_eq_one)
      have r : U₁.relIndex X ≤ 2 := by
        have := Subgroup.relIndex_le_of_le_right hXle (by rw [hr]; norm_num)
        rwa [hr] at this
      have c1 : Nat.card Y ≤ (2 ^ f) ^ 4 := by
        rw [← hTV]
        exact Subgroup.card_le_of_le hYA
      have h1 : Nat.card X ≤ 2 * (2 ^ f) ^ 4 := by
        rw [hcardX]
        exact Nat.mul_le_mul r c1
      omega
  · push Not at hA
    by_cases hB : ∃ x ∈ X, x * w⁻¹ ∈ U₁
    ·
      obtain ⟨x₂, hx₂, hx₂U⟩ := hB
      have hYB : szT₁ L T ⊓ Y ≤ W := fun y hy => by
        obtain ⟨hyT₁, hyY⟩ := mem_inf.mp hy
        obtain ⟨hyU, hyX⟩ := mem_inf.mp hyY
        have h1 := hXc y hyX x₂ hx₂
        rw [show x₂ = (x₂ * w⁻¹) * w by group] at h1
        have hyw := hred y hyU _ hx₂U w h1
        refine (hWiff y hyT₁).mp ?_
        have e : y⁻¹ * (w * y * w⁻¹) = y⁻¹ * (y * w * y⁻¹ * w⁻¹)⁻¹ * y := by group
        rw [e]
        have h5 := mem_centralizer_iff.mp (mem_szA₁.mp (inv_mem hyw)).2 y hyT₁
        rw [mul_assoc, ← h5, ← mul_assoc, inv_mul_cancel, one_mul]
        exact inv_mem hyw
      have hXle : X ≤ U₁ ⊔ zpowers w := fun x hx => by
        rcases hcover x hx with h1 | h1 | h1
        · exact mem_sup_left h1
        · exact absurd h1 (hA x hx)
        · rw [show x = (x * w⁻¹) * w by group]
          exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers w))
      have hwU : w ∉ U₁ := fun h' =>
        hW.w_not_mem (mem_sup_left (hL.muOne_mem_T₁_of_mem_T hS h' hW.w_mem))
      have hr := RankOne.Endings.relIndex_sup_zpowers_eq_two hwU (hL.T_le hW.w_mem)
        (by rw [← sq]; exact hW.w_sq)
      have r : U₁.relIndex X ≤ 2 := by
        have := Subgroup.relIndex_le_of_le_right hXle (by rw [hr]; norm_num)
        rwa [hr] at this
      have c1 : Nat.card Y ≤ (2 ^ f) ^ 4 := by
        have r1 : (szT₁ L T).relIndex Y ≤ (2 ^ f) ^ 2 := by
          have := Subgroup.relIndex_le_of_le_right (inf_le_left : Y ≤ U₁)
            (by rw [hrT₁U₁]; positivity)
          rwa [hrT₁U₁] at this
        have c2 : Nat.card (szT₁ L T ⊓ Y : Subgroup G) ≤ (2 ^ f) ^ 2 := by
          rw [← hWcard]
          exact Subgroup.card_le_of_le hYB
        rw [hcardY, show (2 ^ f) ^ 4 = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 by ring]
        exact Nat.mul_le_mul r1 c2
      have h1 : Nat.card X ≤ 2 * (2 ^ f) ^ 4 := by
        rw [hcardX]
        exact Nat.mul_le_mul r c1
      omega
    · push Not at hB
      apply hXU
      intro x hx
      rcases hcover x hx with h1 | h1 | h1
      · exact h1
      · exact absurd h1 (hA x hx)
      · exact absurd h1 (hB x hx)

theorem conj_s_U₁ {u : G} (hu : u ∈ U₁) : s * u * s⁻¹ ∈ U₁ := by
  have hS := hW.step
  have hL := hW.level
  set X : Subgroup G := U₁.map (MulAut.conj s).toMonoidHom with hXdef
  have hXmem : ∀ y ∈ U₁, s * y * s⁻¹ ∈ X := fun y hy => ⟨y, hy, by simp⟩
  have hXS : X ≤ U ⊔ T := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (mem_normalizer_iff.mp hW.s_mem_normalizer y).mp (mem_sup_left (hL.U₁_le hy))
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ szA₁ (szT₁ L T) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := hL.muOne_comm_mem_szA₁ hS hc hW.mu hK hμ a ha b hb
    have h2 := hW.conj_szA₁ h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show s * a * s⁻¹ * (s * b * s⁻¹) * (s * a * s⁻¹)⁻¹ * (s * b * s⁻¹)⁻¹ =
      s * (a * b * a⁻¹ * b⁻¹) * s⁻¹ by group]
    exact h2
  have h1 : Nat.card X = Nat.card U₁ := card_map_of_injective (MulAut.conj s).injective
  have hXcard : (2 ^ f) ^ 5 ≤ Nat.card X := (h1.trans (hL.muOne_card_U₁ hS)).ge
  exact hW.le_U₁ hXS hXc hXcard (hXmem u hu)

theorem conj_U₁ {g : G} (hg : g ∈ swapS₂ P U T) {u : G} (hu : u ∈ U₁) : g * u * g⁻¹ ∈ U₁ := by
  have hSN := hW.level.muOne_sup_le_normalizer hW.step
  obtain ⟨-, -, -, hcov⟩ := hW.level.norm_swap_facts hW.step hW.mu hW.w_mem hW.w_sq hW.w_not_mem
    hW.w_cent hW.isPGroup hW.le hW.s_mem_normalizer hW.s_mem hW.conj_t hW.conj_w
  rcases hcov g (mem_swapS₂.mp hg).2 (mem_swapS₂.mp hg).1 with h1 | h1
  · exact (mem_normalizer_iff.mp (hSN h1) u).mp hu
  · rw [show g * u * g⁻¹ = (g * s⁻¹) * (s * u * s⁻¹) * (g * s⁻¹)⁻¹ by group]
    exact (mem_normalizer_iff.mp (hSN h1) _).mp (hW.conj_s_U₁ hu)

theorem conj_szA₁_of_mem {g : G} (hg : g ∈ swapS₂ P U T) {a : G} (ha : a ∈ szA₁ (szT₁ L T)) :
    g * a * g⁻¹ ∈ szA₁ (szT₁ L T) :=
  hW.level.gms_conj_szA₁ hW.step (mem_swapS₂.mp hg).2 ha

end U3C1OuterSwapHigh

theorem u3C1GmsNormInput_holds : U3C1GmsNormInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW _ hu => hW.conj_s_U₁ hu

end CFSG.SeitzReduction.RankOne
