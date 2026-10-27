module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialParameterSumClauses

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem mem_centralizer_conj_iff {G : Type*} [Group G] (k w x : G) :
    x ∈ Subgroup.centralizer {k * w * k⁻¹} ↔ k⁻¹ * x * k ∈ Subgroup.centralizer {w} := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hc
    calc k⁻¹ * x * k * w = k⁻¹ * (x * (k * w * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * w * k⁻¹) * x) * k := by rw [hc]
      _ = w * (k⁻¹ * x * k) := by group
  · intro hc
    calc x * (k * w * k⁻¹) = k * ((k⁻¹ * x * k) * w) * k⁻¹ := by group
      _ = k * (w * (k⁻¹ * x * k)) * k⁻¹ := by rw [hc]
      _ = k * w * k⁻¹ * x := by group

namespace CaseIData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {q : ℕ}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
  (h : CaseIData G t s₀ d d₁ J q F' φ)
include h

theorem conj_torusW_le_torusU {k w₀ : G} (hw₀ : w₀ ∈ torusW G t s₀) (hw₀1 : w₀ ≠ 1)
    (hU : k * w₀ * k⁻¹ ∈ torusU G t s₀ d) :
    (torusW G t s₀).map (MulAut.conj k).toMonoidHom ≤ torusU G t s₀ d := by
  have hC := h.centralizer_eq w₀ hw₀ hw₀1
  have hK : ∀ x : G, x * (k * w₀ * k⁻¹) = k * w₀ * k⁻¹ * x → k⁻¹ * x * k ∈ torusK G t s₀ := by
    intro x hx
    rw [← hC, ← mem_centralizer_conj_iff, Subgroup.mem_centralizer_singleton_iff]
    exact hx
  have hUK := h.U_le_K hU
  rintro _ ⟨w, hw, rfl⟩
  change k * w * k⁻¹ ∈ torusU G t s₀ d
  apply h.mem_torusU_of_odd
  · refine ⟨?_, ?_⟩
    ·
      apply K_le_H
      rw [torusK, Subgroup.mem_centralizer_iff]
      intro w' hw'
      have h1 : w' * (k * w₀ * k⁻¹) = k * w₀ * k⁻¹ * w' :=
        (Subgroup.mem_centralizer_iff.mp hUK) w' hw'
      have h2 := Subgroup.mem_centralizer_iff.mp (hK w' h1) w hw
      calc w' * (k * w * k⁻¹) = k * ((k⁻¹ * w' * k) * w) * k⁻¹ := by group
        _ = k * (w * (k⁻¹ * w' * k)) * k⁻¹ := by rw [← h2]
        _ = k * w * k⁻¹ * w' := by group
    ·
      show k * w * k⁻¹ ∈ Subgroup.centralizer {s₀ * d}
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : s₀ * d * (k * w₀ * k⁻¹) = k * w₀ * k⁻¹ * (s₀ * d) :=
        (Subgroup.mem_centralizer_singleton_iff.mp (U_le_centralizer hU)).symm
      have h2 := Subgroup.mem_centralizer_iff.mp (hK (s₀ * d) h1) w hw
      calc k * w * k⁻¹ * (s₀ * d) = k * (w * (k⁻¹ * (s₀ * d) * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * (s₀ * d) * k) * w) * k⁻¹ := by rw [h2]
        _ = s₀ * d * (k * w * k⁻¹) := by group
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact odd_orderOf_of_mem_W hw

theorem mem_torusW_of_odd_of_commute {x : G} (hxt : x * t = t * x) (hxs : x * s₀ = s₀ * x)
    (hodd : Odd (orderOf x)) : x ∈ torusW G t s₀ := by
  have hL := h.localData
  have hxV : x ∈ Subgroup.centralizer
      ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hL.mem_V_cases hy with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact hxt.symm
    · exact hxs.symm
    · calc t * s₀ * x = t * (x * s₀) := by rw [mul_assoc, hxs]
        _ = x * (t * s₀) := by rw [← mul_assoc, ← hxt, mul_assoc]
  rw [← h.V_sup_W] at hxV
  have hcomm : ∀ a ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s₀, ∀ w ∈ torusW G t s₀,
      a * w = w * a := by
    intro a ha w hw
    have hwD : w ∈ Subgroup.centralizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G) := by
      rw [← h.V_sup_W]
      exact Subgroup.mem_sup_right hw
    exact Subgroup.mem_centralizer_iff.mp hwD a ha
  obtain ⟨a, ha, w, hw, rfl⟩ := exists_mul_of_mem_sup hcomm hxV
  have haodd : Odd (orderOf a) :=
    odd_orderOf_of_mul (hcomm a ha w hw) hodd (odd_orderOf_of_mem_W hw)
  have ha2 : a * a = 1 := by
    rcases hL.mem_V_cases ha with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact hL.t_sq
    · exact hL.s_sq
    · calc t * s₀ * (t * s₀) = t * (s₀ * t) * s₀ := by group
        _ = t * (t * s₀) * s₀ := by rw [hL.ts]
        _ = (t * t) * (s₀ * s₀) := by group
        _ = 1 := by rw [hL.t_sq, hL.s_sq, one_mul]
  rw [eq_one_of_mul_self_eq_one_of_odd haodd ha2, one_mul]
  exact hw

theorem card_torusU_eq_of_commute {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a ≠ b) (hc : a * b = b * a)
    (hUa : torusU G t s₀ d ≤ Subgroup.centralizer {a})
    (hUb : torusU G t s₀ d ≤ Subgroup.centralizer {b}) :
    Nat.card (torusU G t s₀ d) = Nat.card (torusW G t s₀) := by
  have hL := h.localData
  obtain ⟨c, hca⟩ := isConj_iff.mp (h.conj_t a ha)
  have hbC : c * b * c⁻¹ ∈ C t := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hca]
    calc c * b * c⁻¹ * (c * a * c⁻¹) = c * (b * a) * c⁻¹ := by group
      _ = c * (a * b) * c⁻¹ := by rw [hc]
      _ = c * a * c⁻¹ * (c * b * c⁻¹) := by group
  have hb2 : orderOf (c * b * c⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hb
  have hbt : c * b * c⁻¹ ≠ t := by
    intro hbt
    apply hab
    have h1 : c * b * c⁻¹ = c * a * c⁻¹ := hbt.trans hca.symm
    exact (by simpa using h1 : b = a).symm
  obtain ⟨c₂, hc₂, hc₂b⟩ := h.conj_s₀ _ hbC hb2 hbt
  have hc₂t : c₂ * t = t * c₂ := Subgroup.mem_centralizer_singleton_iff.mp hc₂
  set k : G := (c₂ * c)⁻¹ with hk
  have hkt : k⁻¹ * a * k = t := by
    rw [hk, inv_inv]
    calc c₂ * c * a * (c₂ * c)⁻¹ = c₂ * (c * a * c⁻¹) * c₂⁻¹ := by group
      _ = c₂ * t * c₂⁻¹ := by rw [hca]
      _ = t := by rw [hc₂t]; group
  have hks : k⁻¹ * b * k = s₀ := by
    rw [hk, inv_inv, ← hc₂b]
    group
  have hUW : torusU G t s₀ d ≤ (torusW G t s₀).map (MulAut.conj k).toMonoidHom := by
    intro u hu
    have hua := Subgroup.mem_centralizer_singleton_iff.mp (hUa hu)
    have hub := Subgroup.mem_centralizer_singleton_iff.mp (hUb hu)
    have hxt : k⁻¹ * u * k * t = t * (k⁻¹ * u * k) := by
      rw [← hkt]
      calc k⁻¹ * u * k * (k⁻¹ * a * k) = k⁻¹ * (u * a) * k := by group
        _ = k⁻¹ * (a * u) * k := by rw [hua]
        _ = k⁻¹ * a * k * (k⁻¹ * u * k) := by group
    have hxs : k⁻¹ * u * k * s₀ = s₀ * (k⁻¹ * u * k) := by
      rw [← hks]
      calc k⁻¹ * u * k * (k⁻¹ * b * k) = k⁻¹ * (u * b) * k := by group
        _ = k⁻¹ * (b * u) * k := by rw [hub]
        _ = k⁻¹ * b * k * (k⁻¹ * u * k) := by group
    have hodd : Odd (orderOf (k⁻¹ * u * k)) := by
      have : k⁻¹ * u * k = MulAut.conj k⁻¹ u := by simp
      rw [this, MulEquiv.orderOf_eq]
      exact odd_orderOf_of_mem_U hu
    refine ⟨k⁻¹ * u * k, h.mem_torusW_of_odd_of_commute hxt hxs hodd, ?_⟩
    change k * (k⁻¹ * u * k) * k⁻¹ = u
    group
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.U_ne_bot
  obtain ⟨w₀, hw₀, hw₀u⟩ := hUW u.2
  have hw₀1 : w₀ ≠ 1 := by
    rintro rfl
    apply hu1
    apply Subtype.ext
    simpa using hw₀u.symm
  have hle := h.conj_torusW_le_torusU hw₀ hw₀1 (k := k) (by
    have : k * w₀ * k⁻¹ = (u : G) := by simpa [MulAut.conj_apply] using hw₀u
    rw [this]
    exact u.2)
  rw [le_antisymm hUW hle, Subgroup.card_map_of_injective (MulAut.conj k).injective]

theorem torusU_le_map_conj {g : G} (hg : g * t * g⁻¹ = s₀ * d) :
    torusU G t s₀ d ≤ J.map (MulAut.conj g).toMonoidHom := by
  have hL := h.localData
  intro u hu
  set x : G := g⁻¹ * u * g with hx
  have hxC : x ∈ C t := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have huv := Subgroup.mem_centralizer_singleton_iff.mp (U_le_centralizer hu)
    rw [← hg] at huv
    calc x * t = g⁻¹ * (u * (g * t * g⁻¹)) * g := by rw [hx]; group
      _ = g⁻¹ * ((g * t * g⁻¹) * u) * g := by rw [huv]
      _ = t * x := by rw [hx]; group
  have hxodd : Odd (orderOf x) := by
    have : x = MulAut.conj g⁻¹ u := by simp [hx]
    rw [this, MulEquiv.orderOf_eq]
    exact odd_orderOf_of_mem_U hu
  obtain ⟨j, hj, b, hb, hjb⟩ := exists_mul_of_mem_sup hL.JB_comm (hL.odd_mem x hxC hxodd)
  have hxU : x ^ Nat.card (torusU G t s₀ d) = 1 := by
    have h1 : u ^ Nat.card (torusU G t s₀ d) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hu)
    have : x = MulAut.conj g⁻¹ u := by simp [hx]
    rw [this, ← map_pow, h1, map_one]
  have hbU : b ^ Nat.card (torusU G t s₀ d) = 1 := by
    rw [hjb, (show Commute j b from hL.JB_comm j hj b hb).mul_pow] at hxU
    have hbJ : b ^ Nat.card (torusU G t s₀ d) ∈ J := by
      have : b ^ Nat.card (torusU G t s₀ d) = (j ^ Nat.card (torusU G t s₀ d))⁻¹ :=
        eq_inv_of_mul_eq_one_right hxU
      rw [this]
      exact J.inv_mem (J.pow_mem hj _)
    have hmem : b ^ Nat.card (torusU G t s₀ d) ∈ J ⊓ (N t).map (C t).subtype :=
      ⟨hbJ, Subgroup.pow_mem _ hb _⟩
    rw [hL.JB_disj, Subgroup.mem_bot] at hmem
    exact hmem
  have hbB : b ^ Nat.card ((N t).map (C t).subtype) = 1 := by
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hb)
  have hb1 : b = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hbU, hbB⟩
    rwa [h.coprime_U_B, pow_one] at this
  rw [hb1, mul_one] at hjb
  refine ⟨j, hj, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hjb, hx]
  group

omit h in
theorem card_sl2_eq_of_two_mul_eq_add {q w : ℕ} (hw : 2 * w = q + 1) :
    q * (q ^ 2 - 1) = w * (2 * q * (q - 1)) := by
  have hq : 1 ≤ q := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hq
  have : (1 + m) ^ 2 - 1 = m * (m + 2) := by
    rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
    ring
  rw [this, show 1 + m - 1 = m by omega]
  have hw' : w * 2 = m + 2 := by omega
  calc (1 + m) * (m * (m + 2)) = (1 + m) * m * (w * 2) := by rw [hw']; ring
    _ = w * (2 * (1 + m) * m) := by ring

omit h in
theorem card_sl2_eq_of_two_mul_add_eq {q w : ℕ} (hw : 2 * w + 1 = q) :
    q * (q ^ 2 - 1) = w * (2 * q * (q + 1)) := by
  subst hw
  have : (2 * w + 1) ^ 2 - 1 = 4 * w * (w + 1) := by
    rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
    ring
  rw [this]
  ring

theorem exists_card_J_eq_mul :
    ∃ m : ℕ, Nat.card J = Nat.card (torusW G t s₀) * m ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card (torusW G t s₀) → ¬ r ∣ m := by
  obtain ⟨F, _, _, hF, ⟨ι⟩⟩ := h.sl2
  have hJcard : Nat.card J = q * (q ^ 2 - 1) := by
    rw [Nat.card_congr ι.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, hF]
  have h2 := h.two_mul_card_W_int
  have hodd := odd_card_W (G := G) (t := t) (s₀ := s₀)
  set w := Nat.card (torusW G t s₀) with hwdef
  by_cases h4 : q % 4 = 1
  · have h2' : 2 * (w : ℤ) = q + 1 := by simpa [h4] using h2
    have hw : 2 * w = q + 1 := by exact_mod_cast h2'
    refine ⟨2 * q * (q - 1), hJcard.trans (card_sl2_eq_of_two_mul_eq_add hw), ?_⟩
    intro r hr hrw hrm
    have hrq1 : r ∣ q + 1 := hw ▸ dvd_mul_of_dvd_right hrw 2
    rcases (Nat.Prime.dvd_mul hr).mp hrm with hr2 | hr3
    · rcases (Nat.Prime.dvd_mul hr).mp hr2 with hr2 | hr2
      · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hr2
        subst this
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrw)
      · exact hr.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hr2).mp hrq1))
    · have h2' : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub hrq1 hr3
      rw [show q + 1 - (q - 1) = 2 by omega] at h2'
      have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2'
      subst this
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrw)
  · have h2' : 2 * (w : ℤ) = q + -1 := by simpa [h4] using h2
    have hq := h.q_odd
    have hw : 2 * w + 1 = q := by
      obtain ⟨k, hk⟩ := hq
      have : (2 * (w : ℤ)) + 1 = q := by linarith [h2']
      exact_mod_cast this
    refine ⟨2 * q * (q + 1), hJcard.trans (card_sl2_eq_of_two_mul_add_eq hw), ?_⟩
    intro r hr hrw hrm
    have hrq1 : r ∣ q - 1 := by
      rw [show q - 1 = 2 * w by omega]
      exact dvd_mul_of_dvd_right hrw 2
    rcases (Nat.Prime.dvd_mul hr).mp hrm with hr2 | hr3
    · rcases (Nat.Prime.dvd_mul hr).mp hr2 with hr2 | hr2
      · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hr2
        subst this
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrw)
      · have h1 : r ∣ q - (q - 1) := Nat.dvd_sub hr2 hrq1
        rw [show q - (q - 1) = 1 by omega] at h1
        exact hr.one_lt.ne' (Nat.dvd_one.mp h1)
    · have h2' : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub hr3 hrq1
      rw [show q + 1 - (q - 1) = 2 by omega] at h2'
      have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2'
      subst this
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrw)

theorem exists_conj_mem_torusW {r : ℕ} [hr : Fact r.Prime] (hrW : r ∣ Nat.card (torusW G t s₀))
    {x : G} (hxJ : x ∈ J) (hx : orderOf x = r) :
    ∃ j ∈ J, j⁻¹ * x * j ∈ torusW G t s₀ := by
  classical
  have hL := h.localData
  obtain ⟨m, hJm, hrm⟩ := h.exists_card_J_eq_mul
  let PW : Sylow r (torusW G t s₀) := default
  let P : Subgroup G := (PW : Subgroup (torusW G t s₀)).map (torusW G t s₀).subtype
  have hPW : P ≤ torusW G t s₀ := Subgroup.map_subtype_le _
  have hPJ : P ≤ J := hPW.trans hL.W_le_J
  have hPcard : Nat.card (P.subgroupOf J) = Nat.card PW := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPJ).toEquiv,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hPp : IsPGroup r (P.subgroupOf J) := by
    obtain ⟨k, hk⟩ := PW.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (hPcard.trans hk)
  have hPidx : ¬ r ∣ (P.subgroupOf J).index := by
    have h1 := Subgroup.card_mul_index (P.subgroupOf J)
    have h2 := Subgroup.card_mul_index (PW : Subgroup (torusW G t s₀))
    rw [hPcard, hJm, ← h2, mul_assoc] at h1
    have h3 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    rw [h3]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hr.out).mp hdvd with h4 | h4
    · exact PW.not_dvd_index h4
    · exact hrm r hr.out hrW h4
  let T : Sylow r J := hPp.toSylow hPidx
  have hxp : IsPGroup r (Subgroup.zpowers (⟨x, hxJ⟩ : J)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx, pow_one])
  obtain ⟨T', hT'⟩ := hxp.exists_le_sylow
  obtain ⟨j, hj⟩ := MulAction.exists_smul_eq J T T'
  have hmem : (⟨x, hxJ⟩ : J) ∈ ((j • T : Sylow r J) : Subgroup J) := by
    rw [hj]
    exact hT' (Subgroup.mem_zpowers _)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨y, hyT, hyx⟩ := hmem
  have hyP : (y : G) ∈ P := by
    have : y ∈ (T : Subgroup J) := hyT
    rw [IsPGroup.toSylow_coe] at this
    exact Subgroup.mem_subgroupOf.mp this
  refine ⟨j, j.2, ?_⟩
  have hyx' : (j : G) * y * (j : G)⁻¹ = x := by
    have := congrArg Subtype.val hyx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [← hyx']
  have : (j : G)⁻¹ * ((j : G) * y * (j : G)⁻¹) * j = y := by group
  rw [this]
  exact hPW hyP

theorem coprime_card_torusU_torusW
    (hne : Nat.card (torusU G t s₀ d) ≠ Nat.card (torusW G t s₀)) :
    Nat.Coprime (Nat.card (torusU G t s₀ d)) (Nat.card (torusW G t s₀)) := by
  classical
  have hL := h.localData
  by_contra hcop
  obtain ⟨r, hr, hrU, hrW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := torusU G t s₀ d) r hrU
  obtain ⟨c, hc⟩ := isConj_iff.mp (h.conj_t (s₀ * d) h.v_orderOf)
  have hg : c⁻¹ * t * c⁻¹⁻¹ = s₀ * d := by rw [← hc]; group
  have hUJ := h.torusU_le_map_conj hg
  obtain ⟨us, husJ, hus⟩ := hUJ u.2
  have hus' : c⁻¹ * us * c = u := by simpa [MulAut.conj_apply] using hus
  have husord : orderOf us = r := by
    have h1 : us = MulAut.conj c (u : G) := by rw [← hus']; simp [MulAut.conj_apply]; group
    rw [h1, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hu]
  obtain ⟨j, hjJ, hjW⟩ := h.exists_conj_mem_torusW hrW husJ husord
  set k : G := c⁻¹ * j with hk
  set y : G := j⁻¹ * us * j with hy
  have hy1 : y ≠ 1 := by
    intro hy1
    have : us = 1 := by
      have : us = j * y * j⁻¹ := by rw [hy]; group
      rw [this, hy1]; group
    rw [this] at husord
    rw [orderOf_one] at husord
    exact hr.one_lt.ne husord
  have hku : k * y * k⁻¹ = u := by rw [hk, hy, ← hus']; group
  have hle := h.conj_torusW_le_torusU hjW hy1 (k := k) (by rw [hku]; exact u.2)
  have hUc := h.U_cyclic
  have hcomm : ∀ a ∈ torusU G t s₀ d, ∀ b ∈ torusU G t s₀ d, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val
      ((IsCyclic.commGroup (α := torusU G t s₀ d)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hge : torusU G t s₀ d ≤ (torusW G t s₀).map (MulAut.conj k).toMonoidHom := by
    intro u' hu'
    obtain ⟨us', hus'J, hus'u⟩ := hUJ hu'
    have hus'u' : c⁻¹ * us' * c = u' := by simpa [MulAut.conj_apply] using hus'u
    set x' : G := j⁻¹ * us' * j with hx'
    have hx'J : x' ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hjJ) hus'J) hjJ
    have hx'k : k * x' * k⁻¹ = u' := by rw [hk, hx', ← hus'u']; group
    have hc' : x' * y = y * x' := by
      have h1 := hcomm u' hu' u u.2
      rw [← hx'k, ← hku] at h1
      have h2 : k * (x' * y) * k⁻¹ = k * (y * x') * k⁻¹ := by
        calc k * (x' * y) * k⁻¹ = k * x' * k⁻¹ * (k * y * k⁻¹) := by group
          _ = k * y * k⁻¹ * (k * x' * k⁻¹) := h1
          _ = k * (y * x') * k⁻¹ := by group
      simpa using h2
    have hx'tW := hL.mem_of_commute (Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hjW)
      (by
        intro hbot
        apply hy1
        have : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
        rw [hbot, Subgroup.mem_bot] at this
        exact this)
      hx'J (by
        intro w hw
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact (Commute.zpow_right hc' n).eq)
    have hx'odd : Odd (orderOf x') := by
      have : x' = MulAut.conj k⁻¹ u' := by rw [← hx'k]; simp; group
      rw [this, MulEquiv.orderOf_eq]
      exact odd_orderOf_of_mem_U hu'
    refine ⟨x', hL.mem_W_of_odd hx'tW hx'odd, ?_⟩
    simpa [MulAut.conj_apply] using hx'k
  apply hne
  rw [le_antisymm hge hle, Subgroup.card_map_of_injective (MulAut.conj k).injective]

end CaseIData

end CFSG.Semidihedral.FixedCoreNontrivial
