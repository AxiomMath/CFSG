module

public import CFSG.ClassicalInvolution.Balance.TheoremQNormalizer

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Core

variable {G : Type} [Group G] [Finite G]

@[expose] def OddCoreFreeInvolutions (S : Subgroup G) : Prop :=
  ∀ s ∈ S, s * s = 1 → oddCoreIn (S ⊓ Subgroup.centralizer ({s} : Set G)) = ⊥

omit [Finite G] in
theorem mem_sup_iff_of_commute {R R' : Subgroup G} (hc : ∀ a ∈ R, ∀ b ∈ R', a * b = b * a)
    {x : G} : x ∈ R ⊔ R' ↔ ∃ a ∈ R, ∃ b ∈ R', a * b = x := by
  constructor
  · intro hx
    let P : Subgroup G :=
      { carrier := {x | ∃ a ∈ R, ∃ b ∈ R', a * b = x}
        one_mem' := ⟨1, R.one_mem, 1, R'.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', R.mul_mem ha ha', b * b', R'.mul_mem hb hb', ?_⟩
          have h := hc a' ha' b hb
          calc a * a' * (b * b') = a * (a' * b) * b' := by group
            _ = a * (b * a') * b' := by rw [h]
            _ = a * b * (a' * b') := by group
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, R.inv_mem ha, b⁻¹, R'.inv_mem hb, ?_⟩
          rw [mul_inv_rev]
          exact hc a⁻¹ (R.inv_mem ha) b⁻¹ (R'.inv_mem hb) }
    have hle : R ⊔ R' ≤ P :=
      sup_le (fun a ha => ⟨a, ha, 1, R'.one_mem, by simp⟩)
        (fun b hb => ⟨1, R.one_mem, b, hb, by simp⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem eq_one_of_central_of_oddCoreIn_eq_bot {X₁ : Subgroup G} (hX₁ : oddCoreIn X₁ = ⊥) {x : G}
    (hx : x ∈ X₁) (hcent : ∀ r ∈ X₁, x * r = r * x) {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) :
    x = 1 := by
  have hle : Subgroup.zpowers x ≤ oddCoreIn X₁ := by
    refine le_oddCoreIn_of_normalizes ((Subgroup.zpowers_le).mpr hx) ?_ ?_
    · intro u hu
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hux : u * x = x * u := (hcent u hu).symm
      have hcu : ∀ k : ℤ, u * x ^ k = x ^ k * u := fun k =>
        ((Commute.zpow_right (show Commute u x from hux) k).eq)
      constructor
      · intro hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have : u * x ^ k * u⁻¹ = x ^ k := by rw [hcu k]; group
        rw [this]; exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
      · intro hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
        have h2 : y = x ^ k := by
          calc y = u⁻¹ * (u * y * u⁻¹) * u := by group
            _ = u⁻¹ * x ^ k * u := by rw [← hk]
            _ = u⁻¹ * (x ^ k * u) := by group
            _ = u⁻¹ * (u * x ^ k) := by rw [hcu k]
            _ = x ^ k := by group
        rw [h2]; exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    · rw [Nat.card_zpowers]
      exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hxm)
  rw [hX₁, le_bot_iff] at hle
  have hx' : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  rw [hle] at hx'
  exact Subgroup.mem_bot.mp hx'

theorem commute_of_oddCoreIn_inf_eq_bot {W X₁ : Subgroup G} {s n : G} (hX₁W : X₁ ≤ W)
    (hX₁C : X₁ ≤ Subgroup.centralizer ({s} : Set G)) (hX₁ : oddCoreIn X₁ = ⊥)
    (hn : n ∈ oddCoreIn (W ⊓ Subgroup.centralizer ({s} : Set G)))
    (hnorm : ∀ r ∈ X₁, n * r * n⁻¹ ∈ X₁) : ∀ r ∈ X₁, n * r = r * n := by
  intro r hr
  set C : Subgroup G := W ⊓ Subgroup.centralizer ({s} : Set G) with hC
  have hrC : r ∈ C := ⟨hX₁W hr, hX₁C hr⟩
  have hcN : n * r * n⁻¹ * r⁻¹ ∈ oddCoreIn C := by
    have h1 : r * n⁻¹ * r⁻¹ ∈ oddCoreIn C := conj_mem_oddCoreIn hrC ((oddCoreIn C).inv_mem hn)
    have : n * r * n⁻¹ * r⁻¹ = n * (r * n⁻¹ * r⁻¹) := by group
    rw [this]
    exact (oddCoreIn C).mul_mem hn h1
  have hcX : n * r * n⁻¹ * r⁻¹ ∈ X₁ := X₁.mul_mem (hnorm r hr) (X₁.inv_mem hr)
  have hS : oddCoreIn C ⊓ X₁ ≤ oddCoreIn X₁ := by
    refine le_oddCoreIn_of_normalizes inf_le_right ?_ ?_
    · intro u hu
      have huC : u ∈ C := ⟨hX₁W hu, hX₁C hu⟩
      have huC' : u⁻¹ ∈ C := C.inv_mem huC
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hy1, hy2⟩
        exact ⟨conj_mem_oddCoreIn huC hy1, X₁.mul_mem (X₁.mul_mem hu hy2) (X₁.inv_mem hu)⟩
      · rintro ⟨hy1, hy2⟩
        have h1 := conj_mem_oddCoreIn huC' hy1
        have h2 := X₁.mul_mem (X₁.mul_mem (X₁.inv_mem hu) hy2) hu
        simp only [inv_inv, mul_assoc, inv_mul_cancel_left] at h1 h2 ⊢
        exact ⟨by simpa [mul_assoc] using h1, by simpa [mul_assoc] using h2⟩
    · exact (odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have h1 : n * r * n⁻¹ * r⁻¹ ∈ oddCoreIn X₁ := hS ⟨hcN, hcX⟩
  rw [hX₁, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

omit [Finite G] in
theorem commutator_pair {R R' : Subgroup G} (hc : ∀ a ∈ R, ∀ b ∈ R', a * b = b * a) {n₁ a n₂ b : G}
    (hn₁ : n₁ ∈ R) (ha : a ∈ R) (hn₂ : n₂ ∈ R') (hb : b ∈ R') :
    ⁅n₁ * n₂, a * b⁆ = ⁅n₁, a⁆ * ⁅n₂, b⁆ := by
  have e1 : n₂ * a = a * n₂ := (hc a ha n₂ hn₂).symm
  have e2 : n₁⁻¹ * (n₂ * b * n₂⁻¹) = (n₂ * b * n₂⁻¹) * n₁⁻¹ :=
    hc n₁⁻¹ (R.inv_mem hn₁) (n₂ * b * n₂⁻¹)
      (R'.mul_mem (R'.mul_mem hn₂ hb) (R'.inv_mem hn₂))
  have e3 : a⁻¹ * (n₂ * b * n₂⁻¹ * b⁻¹) = (n₂ * b * n₂⁻¹ * b⁻¹) * a⁻¹ :=
    hc a⁻¹ (R.inv_mem ha) (n₂ * b * n₂⁻¹ * b⁻¹)
      (R'.mul_mem (R'.mul_mem (R'.mul_mem hn₂ hb) (R'.inv_mem hn₂)) (R'.inv_mem hb))
  calc ⁅n₁ * n₂, a * b⁆ = n₁ * n₂ * (a * b) * (n₂⁻¹ * n₁⁻¹) * (b⁻¹ * a⁻¹) := by
        simp only [commutatorElement_def, mul_inv_rev]
    _ = n₁ * (n₂ * a) * b * n₂⁻¹ * n₁⁻¹ * b⁻¹ * a⁻¹ := by group
    _ = n₁ * (a * n₂) * b * n₂⁻¹ * n₁⁻¹ * b⁻¹ * a⁻¹ := by rw [e1]
    _ = n₁ * a * (n₂ * b * n₂⁻¹ * n₁⁻¹) * b⁻¹ * a⁻¹ := by group
    _ = n₁ * a * (n₁⁻¹ * (n₂ * b * n₂⁻¹)) * b⁻¹ * a⁻¹ := by rw [← e2]
    _ = n₁ * a * n₁⁻¹ * ((n₂ * b * n₂⁻¹ * b⁻¹) * a⁻¹) := by group
    _ = n₁ * a * n₁⁻¹ * (a⁻¹ * (n₂ * b * n₂⁻¹ * b⁻¹)) := by rw [← e3]
    _ = ⁅n₁, a⁆ * ⁅n₂, b⁆ := by simp only [commutatorElement_def]; group

theorem oddCoreFreeInvolutions_sup {R R' : Subgroup G} (hc : ∀ a ∈ R, ∀ b ∈ R', a * b = b * a)
    (hi : R ⊓ R' = ⊥) (hR : OddCoreFreeInvolutions R) (hR' : OddCoreFreeInvolutions R') :
    OddCoreFreeInvolutions (R ⊔ R') := by
  intro s hs hs2
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hc).mp hs
  have hab : a * b = b * a := hc a ha b hb
  have hsq : a * a * (b * b) = 1 := by
    have : a * b * (a * b) = a * a * (b * b) := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = a * a * (b * b) := by group
    rw [← this]
    exact hs2
  have haa : a * a = 1 := by
    have hmem : a * a ∈ R ⊓ R' := by
      refine ⟨R.mul_mem ha ha, ?_⟩
      have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact R'.inv_mem (R'.mul_mem hb hb)
    rw [hi] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hbb : b * b = 1 := by
    rw [haa, one_mul] at hsq
    exact hsq
  have hRC : R ⊓ Subgroup.centralizer ({a * b} : Set G) =
      R ⊓ Subgroup.centralizer ({a} : Set G) := by
    ext r
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hr, h⟩
      refine ⟨hr, ?_⟩
      have hrb := hc r hr b hb
      have : r * a * b = a * r * b := by
        calc r * a * b = r * (a * b) := by group
          _ = a * b * r := h
          _ = a * (b * r) := by group
          _ = a * (r * b) := by rw [← hrb]
          _ = a * r * b := by group
      exact mul_right_cancel this
    · rintro ⟨hr, h⟩
      refine ⟨hr, ?_⟩
      have hrb := hc r hr b hb
      calc r * (a * b) = r * a * b := by group
        _ = a * r * b := by rw [h]
        _ = a * (r * b) := by group
        _ = a * (b * r) := by rw [hrb]
        _ = a * b * r := by group
  have hR'C : R' ⊓ Subgroup.centralizer ({a * b} : Set G) =
      R' ⊓ Subgroup.centralizer ({b} : Set G) := by
    ext r
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hr, h⟩
      refine ⟨hr, ?_⟩
      have hra := hc a ha r hr
      have : a * (r * b) = a * (b * r) := by
        calc a * (r * b) = a * r * b := by group
          _ = r * a * b := by rw [hra]
          _ = r * (a * b) := by group
          _ = a * b * r := h
          _ = a * (b * r) := by group
      exact mul_left_cancel this
    · rintro ⟨hr, h⟩
      refine ⟨hr, ?_⟩
      have hra := hc a ha r hr
      calc r * (a * b) = r * a * b := by group
        _ = a * r * b := by rw [← hra]
        _ = a * (r * b) := by group
        _ = a * (b * r) := by rw [h]
        _ = a * b * r := by group
  have hX₁ : oddCoreIn (R ⊓ Subgroup.centralizer ({a * b} : Set G)) = ⊥ := by
    rw [hRC]; exact hR a ha haa
  have hX₂ : oddCoreIn (R' ⊓ Subgroup.centralizer ({a * b} : Set G)) = ⊥ := by
    rw [hR'C]; exact hR' b hb hbb
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hnC : n ∈ (R ⊔ R') ⊓ Subgroup.centralizer ({a * b} : Set G) := oddCoreIn_le _ hn
  obtain ⟨n₁, hn₁, n₂, hn₂, rfl⟩ := (mem_sup_iff_of_commute hc).mp hnC.1
  have hcn : Commute n₁ n₂ := hc n₁ hn₁ n₂ hn₂
  have hcomm₁ : ∀ r ∈ R ⊓ Subgroup.centralizer ({a * b} : Set G), n₁ * r = r * n₁ := by
    have h := commute_of_oddCoreIn_inf_eq_bot (W := R ⊔ R') (s := a * b)
      (X₁ := R ⊓ Subgroup.centralizer ({a * b} : Set G)) (inf_le_left.trans le_sup_left)
      inf_le_right hX₁ hn (by
        intro r hr
        refine ⟨?_, ?_⟩
        · have e : n₂ * r * n₂⁻¹ = r := by
            have := hc r hr.1 n₂ hn₂
            rw [← this]; group
          have : n₁ * n₂ * r * (n₁ * n₂)⁻¹ = n₁ * r * n₁⁻¹ := by
            calc n₁ * n₂ * r * (n₁ * n₂)⁻¹ = n₁ * (n₂ * r * n₂⁻¹) * n₁⁻¹ := by group
              _ = n₁ * r * n₁⁻¹ := by rw [e]
          rw [this]
          exact R.mul_mem (R.mul_mem hn₁ hr.1) (R.inv_mem hn₁)
        · exact (Subgroup.centralizer ({a * b} : Set G)).mul_mem
            ((Subgroup.centralizer ({a * b} : Set G)).mul_mem hnC.2 hr.2)
            ((Subgroup.centralizer ({a * b} : Set G)).inv_mem hnC.2))
    intro r hr
    have h1 := h r hr
    have h2 := hc r hr.1 n₂ hn₂
    have : n₁ * r * n₂ = r * n₁ * n₂ := by
      calc n₁ * r * n₂ = n₁ * (r * n₂) := by group
        _ = n₁ * (n₂ * r) := by rw [h2]
        _ = n₁ * n₂ * r := by group
        _ = r * (n₁ * n₂) := h1
        _ = r * n₁ * n₂ := by group
    exact mul_right_cancel this
  have hcomm₂ : ∀ r ∈ R' ⊓ Subgroup.centralizer ({a * b} : Set G), n₂ * r = r * n₂ := by
    have h := commute_of_oddCoreIn_inf_eq_bot (W := R ⊔ R') (s := a * b)
      (X₁ := R' ⊓ Subgroup.centralizer ({a * b} : Set G)) (inf_le_left.trans le_sup_right)
      inf_le_right hX₂ hn (by
        intro r hr
        refine ⟨?_, ?_⟩
        · have e : n₁ * r * n₁⁻¹ = r := by
            have := hc n₁ hn₁ r hr.1
            rw [this]; group
          have : n₁ * n₂ * r * (n₁ * n₂)⁻¹ = n₂ * r * n₂⁻¹ := by
            calc n₁ * n₂ * r * (n₁ * n₂)⁻¹ = n₁ * (n₂ * r * n₂⁻¹) * n₁⁻¹ := by group
              _ = n₂ * r * n₂⁻¹ := by
                have hq : n₂ * r * n₂⁻¹ ∈ R' := R'.mul_mem (R'.mul_mem hn₂ hr.1) (R'.inv_mem hn₂)
                have := hc n₁ hn₁ _ hq
                rw [this]; group
          rw [this]
          exact R'.mul_mem (R'.mul_mem hn₂ hr.1) (R'.inv_mem hn₂)
        · exact (Subgroup.centralizer ({a * b} : Set G)).mul_mem
            ((Subgroup.centralizer ({a * b} : Set G)).mul_mem hnC.2 hr.2)
            ((Subgroup.centralizer ({a * b} : Set G)).inv_mem hnC.2))
    intro r hr
    have h1 := h r hr
    have h2 := hc n₁ hn₁ r hr.1
    have : n₁ * (n₂ * r) = n₁ * (r * n₂) := by
      calc n₁ * (n₂ * r) = n₁ * n₂ * r := by group
        _ = r * (n₁ * n₂) := h1
        _ = r * n₁ * n₂ := by group
        _ = n₁ * r * n₂ := by rw [← h2]
        _ = n₁ * (r * n₂) := by group
    exact mul_left_cancel this
  have hcab : ⁅n₁ * n₂, a * b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp hnC.2)
  rw [commutator_pair hc hn₁ ha hn₂ hb] at hcab
  have hu : ⁅n₁, a⁆ ∈ R := by
    have : ⁅n₁, a⁆ = n₁ * (a * n₁⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact R.mul_mem hn₁ (R.mul_mem (R.mul_mem ha (R.inv_mem hn₁)) (R.inv_mem ha))
  have hv : ⁅n₂, b⁆ ∈ R' := by
    have : ⁅n₂, b⁆ = n₂ * (b * n₂⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact R'.mul_mem hn₂ (R'.mul_mem (R'.mul_mem hb (R'.inv_mem hn₂)) (R'.inv_mem hb))
  have huv : ⁅n₁, a⁆ = ⁅n₂, b⁆⁻¹ := eq_inv_of_mul_eq_one_left hcab
  have hu1 : ⁅n₁, a⁆ = 1 := by
    have hmem : ⁅n₁, a⁆ ∈ R ⊓ R' := ⟨hu, by rw [huv]; exact R'.inv_mem hv⟩
    rw [hi] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hv1 : ⁅n₂, b⁆ = 1 := by
    rw [hu1] at huv
    have := congrArg (fun z => z⁻¹) huv
    simpa using this.symm
  have hna : n₁ * a = a * n₁ := commutatorElement_eq_one_iff_mul_comm.mp hu1
  have hnb : n₂ * b = b * n₂ := commutatorElement_eq_one_iff_mul_comm.mp hv1
  obtain hmodd : Odd (orderOf (n₁ * n₂)) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.orderOf_dvd_natCard _ hn)
  set m := orderOf (n₁ * n₂) with hm
  have hnm : (n₁ * n₂) ^ m = 1 := pow_orderOf_eq_one _
  rw [hcn.mul_pow] at hnm
  have hpow₁ : n₁ ^ m = 1 := by
    have hmem : n₁ ^ m ∈ R ⊓ R' := by
      refine ⟨R.pow_mem hn₁ m, ?_⟩
      have : n₁ ^ m = (n₂ ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hnm
      rw [this]
      exact R'.inv_mem (R'.pow_mem hn₂ m)
    rw [hi] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hpow₂ : n₂ ^ m = 1 := by rw [hpow₁, one_mul] at hnm; exact hnm
  have hn₁1 : n₁ = 1 := by
    have hn₁X : n₁ ∈ R ⊓ Subgroup.centralizer ({a * b} : Set G) :=
      ⟨hn₁, Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc n₁ * (a * b) = (n₁ * a) * b := by group
          _ = (a * n₁) * b := by rw [hna]
          _ = a * (n₁ * b) := by group
          _ = a * (b * n₁) := by rw [hc n₁ hn₁ b hb]
          _ = a * b * n₁ := by group)⟩
    exact eq_one_of_central_of_oddCoreIn_eq_bot hX₁ hn₁X hcomm₁ hmodd hpow₁
  have hn₂1 : n₂ = 1 := by
    have hn₂X : n₂ ∈ R' ⊓ Subgroup.centralizer ({a * b} : Set G) :=
      ⟨hn₂, Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc n₂ * (a * b) = (n₂ * a) * b := by group
          _ = (a * n₂) * b := by rw [← hc a ha n₂ hn₂]
          _ = a * (n₂ * b) := by group
          _ = a * (b * n₂) := by rw [hnb]
          _ = a * b * n₂ := by group)⟩
    exact eq_one_of_central_of_oddCoreIn_eq_bot hX₂ hn₂X hcomm₂ hmodd hpow₂
  rw [hn₁1, hn₂1, one_mul]

omit [Finite G] in
theorem oddCoreIn_bot : oddCoreIn (⊥ : Subgroup G) = ⊥ := le_bot_iff.mp (oddCoreIn_le _)

theorem oddCoreFreeInvolutions_iSup {ι : Type*} [DecidableEq ι] (R : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ R i, ∀ b ∈ R j, a * b = b * a)
    (hint : ∀ (j : ι) (s : Finset ι), j ∉ s → R j ⊓ (⨆ i ∈ s, R i) = ⊥)
    (hR : ∀ i, OddCoreFreeInvolutions (R i)) (s : Finset ι) :
    OddCoreFreeInvolutions (⨆ i ∈ s, R i) := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (⨆ i ∈ (∅ : Finset ι), R i) = ⊥ := by simp
    rw [h0]
    intro x hx _
    rw [bot_inf_eq]
    exact oddCoreIn_bot
  | insert j s hj ih =>
    rw [Finset.iSup_insert]
    refine oddCoreFreeInvolutions_sup ?_ (hint j s hj) (hR j) ih
    intro a ha b hb
    have hle : (⨆ i ∈ s, R i) ≤ Subgroup.centralizer (R j : Set G) := by
      refine iSup₂_le fun i hi => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hc j i (fun h => hj (h ▸ hi)) y hy x hx
    exact Subgroup.mem_centralizer_iff.mp (hle hb) a ha

end Core

section Map

variable {Y X : Type} [Group Y] [Finite Y] [Group X] [Finite X]

theorem map_oddCoreIn_le {C : Subgroup Y} {C' : Subgroup X} (π : Y →* X) (h : C.map π = C') :
    (oddCoreIn C).map π ≤ oddCoreIn C' := by
  subst h
  refine le_oddCoreIn_of_normalizes (Subgroup.map_mono (oddCoreIn_le C)) ?_
    ((odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_map_dvd _ π))
  rintro _ ⟨c, hc, rfl⟩
  have fwd : ∀ c ∈ C, ∀ x ∈ (oddCoreIn C).map π, π c * x * (π c)⁻¹ ∈ (oddCoreIn C).map π := by
    rintro c hc _ ⟨s, hs, rfl⟩
    exact ⟨c * s * c⁻¹, conj_mem_oddCoreIn hc hs, by simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => fwd c hc x hx, fun hx => ?_⟩
  have := fwd c⁻¹ (C.inv_mem hc) _ hx
  simpa [mul_assoc] using this

end Map

section Quotient

variable {X : Type} [Group X] [Finite X]

theorem oddCoreIn_centralizer_le_of_quotient (Z : Subgroup X) [Z.Normal]
    (hZ : Z ≤ Subgroup.center X) (t : X)
    (h : oddCoreIn (Subgroup.centralizer ({QuotientGroup.mk' Z t} : Set (X ⧸ Z))) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({t} : Set X)) ≤ Z := by
  set π := QuotientGroup.mk' Z with hπ
  set C := Subgroup.centralizer ({t} : Set X) with hC
  set C' := Subgroup.centralizer ({π t} : Set (X ⧸ Z)) with hC'
  have key : ∀ y : X, π y ∈ C' → ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
    intro y hy c hc
    have hy' : π y * π t = π t * π y := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hzZ : y * t * y⁻¹ * t⁻¹ ∈ Z := by
      rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker]
      calc π (y * t * y⁻¹ * t⁻¹) = (π y * π t) * (π y)⁻¹ * (π t)⁻¹ := by
            simp only [map_mul, map_inv]
        _ = (π t * π y) * (π y)⁻¹ * (π t)⁻¹ := by rw [hy']
        _ = 1 := by group
    have hzc := Subgroup.mem_center_iff.mp (hZ hzZ)
    set z := y * t * y⁻¹ * t⁻¹ with hz
    have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hzt : z * t = y * t * y⁻¹ := by rw [hz]; group
    have e1 : (z * t) * (y * c * y⁻¹) = (y * c * y⁻¹) * (z * t) := by
      rw [hzt]
      calc y * t * y⁻¹ * (y * c * y⁻¹) = y * (t * c) * y⁻¹ := by group
        _ = y * (c * t) * y⁻¹ := by rw [hct]
        _ = y * c * y⁻¹ * (y * t * y⁻¹) := by group
    have e2 : z * (t * (y * c * y⁻¹)) = z * ((y * c * y⁻¹) * t) := by
      calc z * (t * (y * c * y⁻¹)) = (z * t) * (y * c * y⁻¹) := by group
        _ = (y * c * y⁻¹) * (z * t) := e1
        _ = ((y * c * y⁻¹) * z) * t := by group
        _ = (z * (y * c * y⁻¹)) * t := by rw [hzc (y * c * y⁻¹)]
        _ = z * ((y * c * y⁻¹) * t) := by group
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_left_cancel e2).symm
  have hnorm : ∀ y : X, π y ∈ C' → y ∈ Subgroup.normalizer (C : Set X) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => key y hy c hc, fun hc => ?_⟩
    have hy' : π y⁻¹ ∈ C' := by rw [map_inv]; exact C'.inv_mem hy
    have := key y⁻¹ hy' _ hc
    simpa [mul_assoc] using this
  have hCC' : C.map π ≤ C' := by
    rintro _ ⟨c, hc, rfl⟩
    have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hct])
  have hS : (oddCoreIn C).map π ≤ oddCoreIn C' := by
    refine le_oddCoreIn_of_normalizes ((Subgroup.map_mono (oddCoreIn_le C)).trans hCC') ?_
      ((odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_map_dvd _ π))
    intro c' hc'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z c'
    have hyO : y ∈ Subgroup.normalizer (oddCoreIn C : Set X) :=
      mem_normalizer_oddCoreIn_of_mem_normalizer (hnorm y hc')
    have fwd : ∀ y : X, y ∈ Subgroup.normalizer (oddCoreIn C : Set X) →
        ∀ x ∈ (oddCoreIn C).map π, π y * x * (π y)⁻¹ ∈ (oddCoreIn C).map π := by
      intro y hy
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨y * s * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy s).mp hs, by simp⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => fwd y hyO x hx, fun hx => ?_⟩
    have := fwd y⁻¹ ((Subgroup.normalizer (oddCoreIn C : Set X)).inv_mem hyO) _ hx
    rw [map_inv] at this
    have e : (π y)⁻¹ * (π y * x * (π y)⁻¹) * ((π y)⁻¹)⁻¹ = x := by group
    rwa [e] at this
  rw [h, le_bot_iff] at hS
  intro s hs
  have : π s ∈ (oddCoreIn C).map π := ⟨s, hs, rfl⟩
  rw [hS, Subgroup.mem_bot] at this
  exact (QuotientGroup.ker_mk' Z) ▸ this

theorem le_oddCoreIn_top_of_le_center {S : Subgroup X} (hS : S ≤ Subgroup.center X)
    (hodd : Odd (Nat.card S)) : S ≤ oddCoreIn (⊤ : Subgroup X) := by
  have hN : S.Normal := Subgroup.normal_of_le_center hS
  refine le_oddCoreIn_of_normalizes le_top ?_ hodd
  intro g _
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hN.conj_mem x hx g, fun hx => ?_⟩
  have := hN.conj_mem _ hx g⁻¹
  simpa [mul_assoc] using this

theorem oddCoreIn_centralizer_le_oddCoreIn_top_of_quotient (Z : Subgroup X) [Z.Normal]
    (hZ : Z ≤ Subgroup.center X) (t : X)
    (h : oddCoreIn (Subgroup.centralizer ({QuotientGroup.mk' Z t} : Set (X ⧸ Z))) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({t} : Set X)) ≤ oddCoreIn (⊤ : Subgroup X) :=
  le_oddCoreIn_top_of_le_center ((oddCoreIn_centralizer_le_of_quotient Z hZ t h).trans hZ)
    (odd_card_oddCoreIn _)

end Quotient

section Product

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem map_center_inf_iSup_eq_bot {ι : Type} (R : ι → Subgroup X)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ R i, ∀ b ∈ R j, a * b = b * a) (hgen : ⨆ i, R i = ⊤)
    (j : ι) (s : Finset ι) (hj : j ∉ s) :
    (R j).map (QuotientGroup.mk' (Subgroup.center X)) ⊓
      (⨆ i ∈ s, R i).map (QuotientGroup.mk' (Subgroup.center X)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro _ ⟨⟨r, hr, rfl⟩, ⟨r', hr', hrr'⟩⟩
  have hz : r⁻¹ * r' ∈ Subgroup.center X :=
    QuotientGroup.eq.mp (by simpa using hrr'.symm)
  have hTc : ∀ a ∈ R j, ∀ b ∈ (⨆ i ∈ s, R i), a * b = b * a := by
    intro a ha b hb
    have hle : (⨆ i ∈ s, R i) ≤ Subgroup.centralizer (R j : Set X) := by
      refine iSup₂_le fun i hi => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hc j i (fun h => hj (h ▸ hi)) y hy x hx
    exact Subgroup.mem_centralizer_iff.mp (hle hb) a ha
  have hr_eq : r = r' * (r⁻¹ * r')⁻¹ := by group
  have hrc : r ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ ⨆ i, R i := by rw [hgen]; trivial
    have hle : (⨆ i, R i) ≤ Subgroup.centralizer ({r} : Set X) := by
      refine iSup_le fun i => ?_
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hij : i = j
      · subst hij
        have h1 : a * r' = r' * a := hTc a ha r' hr'
        have h2 : a * (r⁻¹ * r')⁻¹ = (r⁻¹ * r')⁻¹ * a :=
          ((Subgroup.mem_center_iff.mp ((Subgroup.center X).inv_mem hz)) a)
        calc a * r = a * (r' * (r⁻¹ * r')⁻¹) := by rw [← hr_eq]
          _ = (a * r') * (r⁻¹ * r')⁻¹ := by group
          _ = (r' * a) * (r⁻¹ * r')⁻¹ := by rw [h1]
          _ = r' * (a * (r⁻¹ * r')⁻¹) := by group
          _ = r' * ((r⁻¹ * r')⁻¹ * a) := by rw [h2]
          _ = (r' * (r⁻¹ * r')⁻¹) * a := by group
          _ = r * a := by rw [← hr_eq]
      · exact hc i j hij a ha r hr
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  simpa using (QuotientGroup.eq_one_iff r).mpr hrc

theorem oddCoreIn_centralizer_eq_bot_of_centralProduct {ι : Type} [Finite ι] (R : ι → Subgroup X)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ R i, ∀ b ∈ R j, a * b = b * a) (hgen : ⨆ i, R i = ⊤)
    (hO : oddCoreIn (⊤ : Subgroup X) = ⊥)
    (hR : ∀ i, OddCoreFreeInvolutions ((R i).map (QuotientGroup.mk' (Subgroup.center X))))
    (t : X) (ht : t * t = 1) : oddCoreIn (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  classical
  have := Fintype.ofFinite ι
  set π := QuotientGroup.mk' (Subgroup.center X) with hπ
  let R' : ι → Subgroup (X ⧸ Subgroup.center X) := fun i => (R i).map π
  have hc' : ∀ i j, i ≠ j → ∀ a ∈ R' i, ∀ b ∈ R' j, a * b = b * a := by
    rintro i j hij _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc i j hij a ha b hb]
  have hint : ∀ (j : ι) (s : Finset ι), j ∉ s → R' j ⊓ (⨆ i ∈ s, R' i) = ⊥ := by
    intro j s hj
    have hmap : (⨆ i ∈ s, R' i) = (⨆ i ∈ s, R i).map π := by
      simp only [R', Subgroup.map_iSup]
    rw [hmap]
    exact map_center_inf_iSup_eq_bot R hc hgen j s hj
  have hsup := oddCoreFreeInvolutions_iSup R' hc' hint hR Finset.univ
  have htop : (⨆ i ∈ (Finset.univ : Finset ι), R' i) = ⊤ := by
    simp only [Finset.mem_univ, iSup_pos]
    simp only [R', ← Subgroup.map_iSup, hgen]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [htop] at hsup
  have h1 := hsup (π t) (Subgroup.mem_top _) (by rw [← map_mul, ht, map_one])
  rw [top_inf_eq] at h1
  have h2 := oddCoreIn_centralizer_le_oddCoreIn_top_of_quotient (Subgroup.center X) le_rfl t h1
  rw [hO, le_bot_iff] at h2
  exact h2

end Product

end CFSG.ClassicalInvolution.Q3
