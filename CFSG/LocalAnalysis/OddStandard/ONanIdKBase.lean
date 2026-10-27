module

public import CFSG.LocalAnalysis.OddStandard.ONanIdFuse

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris
open scoped Pointwise

@[expose] def jE : AlpE := invE 3

@[expose] def InY0E (e : AlpE) : Prop := e = 1 ∨ e = y0E ∨ e = zc ∨ e = y0E * zc

instance (e : AlpE) : Decidable (InY0E e) := inferInstanceAs (Decidable (_ ∨ _))

@[expose] def InW0E (e : AlpE) : Prop := InWE e ∨ InWE (y0E⁻¹ * e)

instance (e : AlpE) : Decidable (InW0E e) := inferInstanceAs (Decidable (_ ∨ _))

set_option maxRecDepth 100000 in
theorem mY0_cases : ∀ e : AlpE, InY0E e → e = 1 ∨ e = y0E ∨ e = zc ∨ e = y0E * zc := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mW0_mul : ∀ ew ∈ WEL, ∀ ey ∈ [1, y0E, zc, y0E * zc], InW0E (ew * ey) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mA_of : ∀ e : AlpE, e.d = 0 → InY0E (e * e) → InW0E e := by decide +kernel

set_option maxRecDepth 100000 in
theorem mA_sq : ∀ e : AlpE, InW0E e → InY0E (e * e) := by decide +kernel

set_option maxRecDepth 100000 in
theorem mSsq : ∀ e : AlpE, e.d = 0 → InW0E (jE * e * (jE * e)) := by decide +kernel

set_option maxRecDepth 100000 in
theorem mcomm : ∀ e : AlpE, e.d = 0 → InW0E (e * jE * e⁻¹ * jE) := by decide +kernel

@[expose] def commWit : List (AlpE × AlpE) :=
  [(⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩), (⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 1⟩), (⟨0, 0, 2, 0⟩, ⟨0, 0, 1, 0⟩),
    (⟨0, 0, 2, 2⟩, ⟨0, 0, 1, 1⟩), (⟨0, 1, 0, 1⟩, ⟨0, 0, 0, 0⟩), (⟨0, 1, 0, 3⟩, ⟨0, 0, 0, 1⟩),
    (⟨0, 1, 2, 1⟩, ⟨0, 0, 1, 0⟩), (⟨0, 1, 2, 3⟩, ⟨0, 0, 1, 1⟩), (⟨0, 2, 0, 0⟩, ⟨0, 0, 0, 1⟩),
    (⟨0, 2, 0, 2⟩, ⟨0, 0, 0, 0⟩), (⟨0, 2, 2, 0⟩, ⟨0, 0, 1, 1⟩), (⟨0, 2, 2, 2⟩, ⟨0, 0, 1, 0⟩),
    (⟨0, 3, 0, 1⟩, ⟨0, 0, 0, 1⟩), (⟨0, 3, 0, 3⟩, ⟨0, 0, 0, 0⟩), (⟨0, 3, 2, 1⟩, ⟨0, 0, 1, 1⟩),
    (⟨0, 3, 2, 3⟩, ⟨0, 0, 1, 0⟩)]

set_option maxRecDepth 100000 in
theorem mcomm_surj : ∀ e : AlpE, InW0E e →
    ((commWit.lookup e).getD 1).d = 0 ∧
      InY0E ((((commWit.lookup e).getD 1) * jE * ((commWit.lookup e).getD 1)⁻¹ * jE)⁻¹ * e) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mQinv : ∀ e : AlpE, e * y0E = y0E * e → InY0E (e * e) → e.d = 0 ∨ (jE⁻¹ * e).d = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mw1 : ∀ e : AlpE, e * y0E = y0E * e →
    e * gen 0 ^ 2 * e⁻¹ ≠ invE 1 ∧ e * gen 0 ^ 2 * e⁻¹ ≠ invE 1 * zc := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem msx : ∀ e : AlpE, e.d = 2 → e * e = 1 →
    ¬ InY0E (gen 3 * e * (gen 3)⁻¹ * e * (gen 3 * e * (gen 3)⁻¹ * e)) := by
  decide +kernel

theorem jE_sq : jE * jE = 1 := by decide

theorem jE_d : jE.d = 2 := by decide

theorem y0E_comm_jE : jE * y0E = y0E * jE := by decide

theorem y0E_comm_s : gen 3 * y0E = y0E * gen 3 := by decide

@[expose] def alpW0 {G : Type*} [Group G] (v1 v2 v3 : G) : Subgroup G :=
  alpW v1 v2 v3 ⊔ zpowers (v1 * v3)

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem j_eq : invRep v1 v2 v3 s t 3 = D.E.φ jE := (AlpEmb.φ_invE D.E 3).symm

theorem mem_Y0_iff (e : AlpE) : D.E.φ e ∈ zpowers (v1 * v3) ↔ InY0E e := by
  classical
  have hy0 : orderOf (v1 * v3) = 4 := by
    have h1 : orderOf y0E = 4 := by
      rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide, fun m hm hm0 => ?_⟩
      interval_cases m <;> decide
    rw [D.y0_eq, orderOf_injective D.E.φ D.E.inj, h1]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    rw [← zpow_mod_orderOf, hy0, D.y0_eq, ← map_zpow] at hk
    have he := D.E.inj hk
    have h4 : k % (4 : ℕ) = 0 ∨ k % (4 : ℕ) = 1 ∨ k % (4 : ℕ) = 2 ∨ k % (4 : ℕ) = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] at he <;> rw [← he] <;> decide
  · intro h
    rcases mY0_cases e h with rfl | rfl | rfl | rfl
    · rw [map_one]; exact one_mem _
    · rw [← D.y0_eq]; exact mem_zpowers _
    · rw [show zc = y0E ^ 2 by decide, map_pow, ← D.y0_eq]; exact pow_mem (mem_zpowers _) 2
    · rw [show y0E * zc = y0E ^ 3 by decide, map_pow, ← D.y0_eq]
      exact pow_mem (mem_zpowers _) 3

theorem Y0_le_V : zpowers (v1 * v3) ≤ alpV v1 v2 v3 := zpowers_le.2 D.y0_mem_V

theorem W0_le_V : alpW0 v1 v2 v3 ≤ alpV v1 v2 v3 := sup_le D.W_le_V D.Y0_le_V

theorem mem_W0_phi (e : AlpE) : D.E.φ e ∈ alpW0 v1 v2 v3 ↔ InW0E e := by
  constructor
  · intro h
    have hle : alpW v1 v2 v3 ≤ normalizer (zpowers (v1 * v3) : Set G) := fun w hw =>
      (centralizer_le_normalizer _) (mem_centralizer_iff.2 fun v hv =>
        D.comm_V (D.Y0_le_V hv) (D.W_le_V hw))
    have h' : D.E.φ e ∈ ((alpW v1 v2 v3 : Set G) * (zpowers (v1 * v3) : Set G)) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hle]
      exact h
    obtain ⟨w, hw, y, hy, he⟩ := h'
    obtain ⟨ew, hew, rfl⟩ := D.exists_phi_WEL hw
    have hyV : y ∈ alpV v1 v2 v3 := D.Y0_le_V hy
    rw [AlpEmb.alpV_eq_map D.E] at hyV
    obtain ⟨ey, -, rfl⟩ := Subgroup.mem_map.1 hyV
    have hy' : D.E.φ ey ∈ zpowers (v1 * v3) := hy
    rw [D.mem_Y0_iff] at hy'
    have he' : D.E.φ ew * D.E.φ ey = D.E.φ e := he
    have hee : e = ew * ey := D.E.inj (by rw [map_mul, he'])
    rw [hee]
    exact mW0_mul ew hew ey (by rcases mY0_cases ey hy' with rfl | rfl | rfl | rfl <;> simp)
  · rintro (h | h)
    · exact mem_sup_left ((D.mem_W_phi e).2 h)
    · have hw := (D.mem_W_phi _).2 h
      have e' : D.E.φ e = D.E.φ y0E * D.E.φ (y0E⁻¹ * e) := by rw [← map_mul, mul_inv_cancel_left]
      rw [e', ← D.y0_eq]
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hw)

theorem exists_phi_of_mem_P {g : G} (hg : g ∈ alpP v1 v2 v3 s t) : ∃ e : AlpE, D.E.φ e = g :=
  (AlpEmb.mem_alpP_iff D.E).1 hg

theorem mem_V_phi (e : AlpE) : D.E.φ e ∈ alpV v1 v2 v3 ↔ e.d = 0 := by
  rw [AlpEmb.alpV_eq_map D.E, Subgroup.mem_map_iff_mem D.E.inj, mem_Vsub]

theorem comm_y0_phi (e : AlpE) :
    D.E.φ e * (v1 * v3) = v1 * v3 * D.E.φ e ↔ e * y0E = y0E * e := by
  rw [D.y0_eq, ← map_mul, ← map_mul, D.E.φ_eq_iff]

theorem exists_normalizer_Y_conj {a b k : G} (ha : a ∈ alpV v1 v2 v3) (hb : b ∈ alpV v1 v2 v3)
    (hk : k ∈ Subgroup.centralizer ({v1 * v3} : Set G)) (hab : k * a * k⁻¹ = b) :
    ∃ n ∈ normalizer (alpV v1 v2 v3 : Set G), n ∈ Subgroup.centralizer ({v1 * v3} : Set G) ∧
      n * a * n⁻¹ = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := centralizer ({v1 * v3} : Set G) with hY
  set Cb : Subgroup G := Y ⊓ centralizer ({b} : Set G) with hCb
  have hVY : alpV v1 v2 v3 ≤ Y := fun v hv => mem_centralizer_singleton_iff.2
    (D.comm_V hv D.y0_mem_V)
  have hVCb : alpV v1 v2 v3 ≤ Cb := fun v hv => Subgroup.mem_inf.2 ⟨hVY hv,
    mem_centralizer_singleton_iff.2 (D.comm_V hv hb)⟩
  set V' := (alpV v1 v2 v3).map (MulAut.conj k).toMonoidHom with hV'
  have hV'Cb : V' ≤ Cb := by
    rintro _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hY1 : k * v * k⁻¹ ∈ Y := mul_mem (mul_mem hk (hVY hv)) (inv_mem hk)
    refine Subgroup.mem_inf.2 ⟨hY1, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hab]
    have := D.comm_V hv ha
    calc k * v * k⁻¹ * (k * a * k⁻¹) = k * (v * a) * k⁻¹ := by group
      _ = k * (a * v) * k⁻¹ := by rw [this]
      _ = k * a * k⁻¹ * (k * v * k⁻¹) := by group
  have hVp : IsPGroup 2 (alpV v1 v2 v3) := D.isPGroup_P.to_le D.V_le_P
  obtain ⟨T, hT, hVT⟩ := exists_isSylowOf_of_le' hVp hVCb
  obtain ⟨d, hd, hdV'⟩ := exists_conj_le_of_isSylowOf hT hV'Cb (hVp.map _)
  have hTY : T ≤ Y := hT.le.trans inf_le_left
  obtain ⟨e, he, heT⟩ := exists_conj_le_of_isSylowOf D.isSylowOf_Q hTY hT.isPGroup
  have hwc : ∀ g : G, (∀ v ∈ alpV v1 v2 v3, g * v * g⁻¹ ∈ alpP v1 v2 v3 s t) →
      ∀ v ∈ alpV v1 v2 v3, g * v * g⁻¹ ∈ alpV v1 v2 v3 := by
    intro g hg v hv
    have hle : (alpV v1 v2 v3).map (MulAut.conj g).toMonoidHom ≤ alpP v1 v2 v3 s t := by
      rintro _ ⟨u, hu, rfl⟩
      exact hg u hu
    have heq := D.V_weaklyClosed g hle
    rw [← heq]
    exact ⟨v, hv, rfl⟩
  have h1 : ∀ v ∈ alpV v1 v2 v3, e * v * e⁻¹ ∈ alpV v1 v2 v3 :=
    hwc e fun v hv => (heT v (hVT hv)).1
  have h2 : ∀ v ∈ alpV v1 v2 v3, (e * d * k) * v * (e * d * k)⁻¹ ∈ alpV v1 v2 v3 := by
    refine hwc _ fun v hv => ?_
    have := heT _ (hdV' _ ⟨v, hv, rfl⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [show e * d * k * v * (e * d * k)⁻¹ = e * (d * (k * v * k⁻¹) * d⁻¹) * e⁻¹ by group]
    exact this.1
  have hnorm : ∀ g : G, (∀ v ∈ alpV v1 v2 v3, g * v * g⁻¹ ∈ alpV v1 v2 v3) →
      g ∈ normalizer (alpV v1 v2 v3 : Set G) := by
    intro g hg
    have hle : (alpV v1 v2 v3).map (MulAut.conj g).toMonoidHom ≤ alpV v1 v2 v3 := by
      rintro _ ⟨u, hu, rfl⟩
      exact hg u hu
    have heq : (alpV v1 v2 v3).map (MulAut.conj g).toMonoidHom = alpV v1 v2 v3 :=
      eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])
    rw [mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hg v hv, fun hv => ?_⟩
    rw [← heq] at hv
    obtain ⟨u, hu, hu'⟩ := hv
    have : u = v := by
      have := congrArg (fun y => g⁻¹ * y * g) hu'
      simpa [MulAut.conj_apply, mul_assoc] using this
    rw [← this]
    exact hu
  have hen := hnorm e h1
  have hedk := hnorm _ h2
  refine ⟨d * k, ?_, mul_mem hd.1 hk, ?_⟩
  · have := mul_mem (inv_mem hen) hedk
    rwa [show e⁻¹ * (e * d * k) = d * k by group] at this
  · have hdb : d * b * d⁻¹ = b := by
      rw [mem_centralizer_singleton_iff.1 hd.2, mul_inv_cancel_right]
    rw [show d * k * a * (d * k)⁻¹ = d * (k * a * k⁻¹) * d⁻¹ by group, hab, hdb]

end FusCtx

end CFSG.OddStandard.ONanRec
