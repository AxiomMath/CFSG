module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallChar

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

private theorem card_le_two_mul_card_inf {G : Type*} [Group G] [Finite G] (H K : Subgroup G)
    (hHK : ∀ a ∈ H, ∀ b ∈ H, a ∉ K → b ∉ K → a⁻¹ * b ∈ K) :
    Nat.card H ≤ 2 * Nat.card (H ⊓ K : Subgroup G) := by
  classical
  by_cases hex : ∃ a₀ ∈ H, a₀ ∉ K
  · obtain ⟨a₀, ha₀, ha₀K⟩ := hex
    let F : H → (H ⊓ K : Subgroup G) ⊕ (H ⊓ K : Subgroup G) := fun s =>
      if hs : (s : G) ∈ K then Sum.inl ⟨s, mem_inf.mpr ⟨s.2, hs⟩⟩
      else Sum.inr ⟨a₀⁻¹ * s, mem_inf.mpr ⟨mul_mem (inv_mem ha₀) s.2,
        hHK a₀ ha₀ s s.2 ha₀K hs⟩⟩
    have hF : Function.Injective F := by
      intro s s' hss'
      by_cases hs : (s : G) ∈ K <;> by_cases hs' : (s' : G) ∈ K <;>
        simp only [F, hs, hs', dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq] at hss'
      · have h1 := congrArg (fun p : (H ⊓ K : Subgroup G) => (p : G)) hss'
        exact Subtype.ext (by simpa using h1)
      · have h1 : a₀⁻¹ * (s : G) = a₀⁻¹ * (s' : G) :=
          congrArg (fun p : (H ⊓ K : Subgroup G) => (p : G)) hss'
        exact Subtype.ext (mul_left_cancel h1)
    have h1 := Nat.card_le_card_of_injective F hF
    rwa [Nat.card_sum, ← two_mul] at h1
  · push Not at hex
    have hle : H ≤ H ⊓ K := le_inf le_rfl hex
    calc Nat.card H ≤ Nat.card (H ⊓ K : Subgroup G) := card_le_of_le hle
      _ ≤ 2 * Nat.card (H ⊓ K : Subgroup G) := by omega

private theorem two_mul_card_le_of_lt {G : Type*} [Group G] [Finite G] {A C : Subgroup G} {f : ℕ}
    (hA : Nat.card A = 2 ^ f) (hCA : C ≤ A) (hne : ∃ a ∈ A, a ∉ C) : 2 * Nat.card C ≤ 2 ^ f := by
  obtain ⟨k, hk, hkC⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hA ▸ card_dvd_of_le hCA)
  rcases hk.lt_or_eq with hlt | heq
  · rw [hkC, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) hlt
  · exfalso
    obtain ⟨a, ha, haC⟩ := hne
    have hCeq : C = A := eq_of_le_of_card_ge hCA (by rw [hA, hkC, heq])
    exact haC (hCeq ▸ ha)

private theorem two_mul_lt_two_pow {f : ℕ} (hf : 3 ≤ f) : 2 * f < 2 ^ f := by
  induction f, hf using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    omega

namespace U3R2

variable {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G} {f : ℕ}

theorem exists_eq_mul_t_of_not_mem (hR : U3R2 G L T₁ R₂ t f) {a : G} (ha : a ∈ szR T₁ R₂ t)
    (haH : a ∉ T₁ ⊔ R₂) : ∃ w ∈ T₁ ⊔ R₂, a = w * t := by
  have hzN : zpowers t ≤ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) :=
    zpowers_le.mpr hR.t_mem_normalizer_sup
  have ha' : a ∈ (((T₁ ⊔ R₂) ⊔ zpowers t : Subgroup G) : Set G) := ha
  rw [coe_mul_of_right_le_normalizer_left (T₁ ⊔ R₂) (zpowers t) hzN] at ha'
  obtain ⟨w, hw, z, hz, hwz'⟩ := ha'
  have hwz : w * z = a := hwz'
  rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with rfl | rfl
  · exact absurd (by rw [← hwz, mul_one]; exact hw) haH
  · exact ⟨w, hw, hwz.symm⟩

theorem inv_mul_mem_of_not_mem (hR : U3R2 G L T₁ R₂ t f) {a b : G} (ha : a ∈ szR T₁ R₂ t)
    (hb : b ∈ szR T₁ R₂ t) (haH : a ∉ T₁ ⊔ R₂) (hbH : b ∉ T₁ ⊔ R₂) : a⁻¹ * b ∈ T₁ ⊔ R₂ := by
  obtain ⟨w, hw, rfl⟩ := hR.exists_eq_mul_t_of_not_mem ha haH
  obtain ⟨w', hw', rfl⟩ := hR.exists_eq_mul_t_of_not_mem hb hbH
  have h1 := (mem_normalizer_iff.mp (inv_mem hR.t_mem_normalizer_sup) (w⁻¹ * w')).mp
    (mul_mem (inv_mem hw) hw')
  rw [inv_inv] at h1
  rw [show (w * t)⁻¹ * (w' * t) = t⁻¹ * (w⁻¹ * w') * t by group]
  exact h1

theorem mem_sup_zpowers_of_comm (hR : U3R2 G L T₁ R₂ t f) {x : G} (hx : x ∈ szR T₁ R₂ t)
    (hxt : x * t = t * x) : x ∈ T₁ ⊔ zpowers t := by
  have hzN : zpowers t ≤ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) :=
    zpowers_le.mpr hR.t_mem_normalizer_sup
  have hx' : x ∈ (((T₁ ⊔ R₂) ⊔ zpowers t : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left (T₁ ⊔ R₂) (zpowers t) hzN] at hx'
  obtain ⟨w, hw, z, hz, hwz'⟩ := hx'
  have hwz : w * z = x := hwz'
  subst hwz
  have hzt : z * t = t * z := (commute_of_mem_zpowers hz rfl).symm
  have hwt : w * t = t * w := by
    have h1 : w * z * t = t * (w * z) := hxt
    have h2 : w * t * z = t * w * z := by
      calc w * t * z = w * (t * z) := by group
        _ = w * (z * t) := by rw [hzt]
        _ = w * z * t := by group
        _ = t * (w * z) := h1
        _ = t * w * z := by group
    exact mul_right_cancel h2
  exact mul_mem (mem_sup_left (hR.mem_T₁_of_comm_t hw hwt)) (mem_sup_right hz)

theorem card_le_sq_of_comm_mul_t (hR : U3R2 G L T₁ R₂ t f)
    (hab : ∀ B : Subgroup G, B ≤ T₁ → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      Nat.card B ≤ (2 ^ f) ^ 2)
    (hA₁ : Nat.card (szA₁ T₁) = 2 ^ f) {B₀ : Subgroup G} (hB₀ : B₀ ≤ T₁ ⊔ R₂)
    (hB₀c : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x) {w : G} (hw : w ∈ T₁ ⊔ R₂)
    (hwc : ∀ s ∈ B₀, s * (w * t) = w * t * s) : Nat.card B₀ ≤ (2 ^ f) ^ 2 := by
  have hB₀R : B₀ ⊓ R₂ ≤ szA₁ T₁ := by
    intro s hs
    obtain ⟨hsB, hsR⟩ := mem_inf.mp hs
    refine hR.rho_ker s hsR ?_
    have h1 : s * (w * t) = w * t * s := hwc s hsB
    have h2 : s * w = w * s := hR.comm_of_mem_sup hsR hw
    have h3 : w * (s * t) = w * (t * s) := by
      calc w * (s * t) = (w * s) * t := by group
        _ = (s * w) * t := by rw [h2]
        _ = s * (w * t) := by group
        _ = w * t * s := h1
        _ = w * (t * s) := by group
    exact mul_left_cancel h3
  have hB₀card := hR.card_sup_le_of_comm hab hA₁ hB₀ hB₀c
  have hHC : T₁ ⊔ R₂ ≤ normalizer (R₂ : Set G) :=
    le_trans (fun x hx => mem_centralizer_iff.mpr fun r hr => hR.comm_of_mem_sup hr hx)
      (centralizer_le_normalizer _)
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer (hB₀.trans hHC)
  rw [hR.card] at hprod
  have h4 : Nat.card (B₀ ⊓ R₂ : Subgroup G) ≤ 2 ^ f := hA₁ ▸ card_le_of_le hB₀R
  have h6 : Nat.card B₀ * (2 ^ f) ^ 2 ≤ (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by
    rw [← hprod]
    calc Nat.card (B₀ ⊔ R₂ : Subgroup G) * Nat.card (B₀ ⊓ R₂ : Subgroup G) ≤
        (2 ^ f) ^ 3 * 2 ^ f := Nat.mul_le_mul hB₀card h4
      _ = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_right h6 (by positivity)

end U3R2

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem card_le_mul_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card T ≤ 2 * (2 ^ f) ^ 3 * (2 * f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, -⟩ := h.exists_outHom_of_card_sylow hS2
  obtain ⟨e, Q, hB, -, -⟩ := h.exists_bender_of_card_sylow hS2
  have : Finite (MulAut L) := finite_mulAut L
  obtain ⟨Dd, hDn, -, hDcard, -, hQcard⟩ := hB.outer_unitary
  have hout : Nat.card (Outer L) = Nat.gcd 3 (2 ^ f + 1) * (2 * f) := by
    rw [← hDcard, ← hQcard, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup Dd
  have hp : IsPGroup 2 φ.range :=
    h.isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdvd : Nat.card φ.range ∣ Nat.gcd 3 (2 ^ f + 1) * (2 * f) :=
    hout ▸ Subgroup.card_subgroup_dvd_card φ.range
  have hcop : Nat.Coprime (2 ^ k) (Nat.gcd 3 (2 ^ f + 1)) :=
    Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _) (by norm_num))
  have hdvd2 : Nat.card φ.range ∣ 2 * f := by
    rw [hk] at hdvd ⊢
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hrange : Nat.card φ.range ≤ 2 * f :=
    Nat.le_of_dvd (by have := h.two_le; omega) hdvd2
  have hle : szT₁ L T ⊔ zpowers t ≤ T := by
    obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
    exact sup_le (szT₁_le_left L T) (zpowers_le.mpr htT)
  have hker : φ.ker = (szT₁ L T ⊔ zpowers t).subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, hφ x, mem_subgroupOf]
  have hcard := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hker, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
    h.card_szT₁_sup_of_card_sylow hS2] at hcard
  rw [← hcard]
  exact Nat.mul_le_mul_left _ hrange

theorem le_sup_of_comm_of_normalizer (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hf3 : 3 ≤ f) (hTR₂ : T ≤ normalizer (R₂ : Set G))
    (hTR₁ : T ≤ normalizer (szR (szT₁ L T) R₂ t : Set G)) {B : Subgroup G} (hB : B ≤ T ⊔ R₂)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hcard : (2 ^ f) ^ 3 ≤ Nat.card B) :
    B ≤ szT₁ L T ⊔ R₂ := by
  classical
  by_contra hBH
  obtain ⟨E, _, _, _, σ, u, v, hS⟩ := h.exists_semilinearCoords_of_card_sylow hS2
  obtain ⟨htT, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  have hσσ : ∀ z, σ (σ z) = z := TraceForm.sigma_sigma hS.sigma hS.card
  have hab := fun B hB hBc => h.card_le_of_comm_of_card_sylow hS2 (B := B) hB hBc
  have hq8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  have hBR₁ : ¬ B ≤ szR (szT₁ L T) R₂ t := fun hle =>
    hBH (((h.char_of_card_sylow hS2 hR).2.1 B hle hBc).2 hcard)
  have hdec : ∀ s ∈ T ⊔ R₂, ∃ x ∈ T, ∃ r ∈ R₂, s = x * r := by
    intro s hs
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right T R₂ hTR₂] at hs
    obtain ⟨x, hx, r, hr, rfl⟩ := hs
    exact ⟨x, hx, r, hr, rfl⟩
  have hR₂R₁ : R₂ ≤ szR (szT₁ L T) R₂ t := le_szR_mid _ _ _
  have hHR₁ : szT₁ L T ⊔ R₂ ≤ szR (szT₁ L T) R₂ t := le_sup_left
  have hT₁tR₁ : szT₁ L T ⊔ zpowers t ≤ szR (szT₁ L T) R₂ t :=
    sup_le (le_szR_left _ _ _) (zpowers_le.mpr (mem_szR_right _ _ _))
  have hxt : ∀ x ∈ T, x * t = t * x := fun x hx => mem_centralizer_singleton_iff.mp (h.le hx)
  have hTR₁T : ∀ x ∈ T, x ∈ szR (szT₁ L T) R₂ t → x ∈ szT₁ L T ⊔ zpowers t :=
    fun x hxT hxR => hR.mem_sup_zpowers_of_comm hxR (hxt x hxT)
  have hmemR₁ : ∀ x ∈ T, ∀ r ∈ R₂,
      (x * r ∈ szR (szT₁ L T) R₂ t ↔ x ∈ szT₁ L T ⊔ zpowers t) := by
    intro x hx r hr
    refine ⟨fun h1 => hTR₁T x hx ?_, fun h1 => mul_mem (hT₁tR₁ h1) (hR₂R₁ hr)⟩
    have := mul_mem h1 (inv_mem (hR₂R₁ hr))
    rwa [mul_inv_cancel_right] at this
  have hsqR₁ : ∀ x ∈ T, ∀ r ∈ R₂,
      ((x * r) ^ 2 ∈ szR (szT₁ L T) R₂ t ↔ x ^ 2 ∈ szT₁ L T ⊔ zpowers t) := by
    intro x hx r hr
    have e : (x * r) ^ 2 = x ^ 2 * ((x⁻¹ * r * x) * r) := by rw [sq, sq]; group
    have hr' : (x⁻¹ * r * x) * r ∈ R₂ := by
      refine mul_mem ?_ hr
      have := (mem_normalizer_iff.mp (hTR₂ (inv_mem hx)) r).mp hr
      rwa [inv_inv] at this
    rw [e]
    refine ⟨fun h1 => hTR₁T _ (pow_mem hx 2) ?_, fun h1 => mul_mem (hT₁tR₁ h1) (hR₂R₁ hr')⟩
    have := mul_mem h1 (inv_mem (hR₂R₁ hr'))
    rwa [mul_inv_cancel_right] at this
  have hcomm : ∀ x ∈ T, ∀ r ∈ R₂, x * r ∈ B → ∀ w ∈ B ⊓ (szT₁ L T ⊔ R₂), x * w = w * x := by
    intro x hx r hr hb w hw
    obtain ⟨hwB, hwH⟩ := mem_inf.mp hw
    have h1 := hBc _ hb w hwB
    have h2 : r * w = w * r := hR.comm_of_mem_sup hr hwH
    have h3 : (x * w) * r = (w * x) * r := by
      calc (x * w) * r = x * (w * r) := by group
        _ = x * (r * w) := by rw [h2]
        _ = x * r * w := by group
        _ = w * (x * r) := h1
        _ = (w * x) * r := by group
    exact mul_right_cancel h3
  have hBH₁ : ∀ x ∈ T, ∀ r ∈ R₂, x * r ∈ B → x ∉ szT₁ L T ⊔ zpowers t →
      Nat.card (B ⊓ (szT₁ L T ⊔ R₂) : Subgroup G) ≤
        2 * Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 := by
    intro x hx r hr hb hxS
    have hle : B ⊓ (szT₁ L T ⊔ R₂) ≤ (szT₁ L T ⊔ R₂) ⊓ centralizer ({x} : Set G) := fun w hw =>
      mem_inf.mpr ⟨(mem_inf.mp hw).2,
        mem_centralizer_singleton_iff.mpr (hcomm x hx r hr hb w hw).symm⟩
    have h1 := hR.card_centralizer_sup_le (hxt x hx)
    have h2 := hS.card_centralizer_le h hS2 hx hxS
    calc Nat.card (B ⊓ (szT₁ L T ⊔ R₂) : Subgroup G) ≤
        Nat.card ((szT₁ L T ⊔ R₂) ⊓ centralizer ({x} : Set G) : Subgroup G) := card_le_of_le hle
      _ ≤ Nat.card (szT₁ L T ⊓ centralizer ({x} : Set G) : Subgroup G) *
          Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x} : Set G) : Subgroup G) := h1
      _ ≤ 2 * Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x} : Set G) : Subgroup G) *
          Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
        Nat.mul_le_mul_right _ h2
      _ = 2 * Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 := by
        ring
  have hBR₁H : Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G) ≤
      2 * Nat.card (B ⊓ (szT₁ L T ⊔ R₂) : Subgroup G) := by
    have h1 := card_le_two_mul_card_inf (B ⊓ szR (szT₁ L T) R₂ t) (szT₁ L T ⊔ R₂)
      fun a ha b hb haH hbH =>
        hR.inv_mul_mem_of_not_mem (mem_inf.mp ha).2 (mem_inf.mp hb).2 haH hbH
    rwa [inf_assoc, inf_eq_right.mpr hHR₁] at h1
  obtain ⟨b, hbB, hbR⟩ := Set.not_subset.mp hBR₁
  obtain ⟨x, hxT, r, hr, rfl⟩ := hdec b (hB hbB)
  have hxS : x ∉ szT₁ L T ⊔ zpowers t := fun h1 => hbR ((hmemR₁ x hxT r hr).mpr h1)
  by_cases hcase : ∃ b' ∈ B, b' ^ 2 ∉ szR (szT₁ L T) R₂ t
  ·
    obtain ⟨b', hb'B, hb'2⟩ := hcase
    obtain ⟨x', hx'T, r', hr', rfl⟩ := hdec b' (hB hb'B)
    have hx'2 : x' ^ 2 ∉ szT₁ L T ⊔ zpowers t := fun h1 => hb'2 ((hsqR₁ x' hx'T r' hr').mpr h1)
    have hx'S : x' ∉ szT₁ L T ⊔ zpowers t := fun h1 => hx'2 (pow_mem h1 2)
    obtain ⟨a, haA, hxa⟩ := hS.exists_not_comm_of_sq_not_mem h hS2 hx'T hx'2
    have hCA : 2 * Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x'} : Set G) : Subgroup G) ≤
        2 ^ f :=
      two_mul_card_le_of_lt hA₁card inf_le_left ⟨a, haA, fun h1 =>
        hxa (mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2).symm⟩
    have h1 := hBH₁ x' hx'T r' hr' hb'B hx'S
    have hBR₁q : Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G) ≤ (2 ^ f) ^ 2 := by
      calc Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G) ≤
          2 * Nat.card (B ⊓ (szT₁ L T ⊔ R₂) : Subgroup G) := hBR₁H
        _ ≤ 2 * (2 * Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x'} : Set G) : Subgroup G) ^ 2) :=
          Nat.mul_le_mul_left _ h1
        _ = (2 * Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x'} : Set G) : Subgroup G)) ^ 2 := by
          ring
        _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hCA 2
    have hBN : B ≤ normalizer (szR (szT₁ L T) R₂ t : Set G) :=
      hB.trans (sup_le hTR₁ (hR₂R₁.trans Subgroup.le_normalizer))
    have hp1 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hBN
    have hp2 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hTR₁
    have hTR₁eq : T ⊓ szR (szT₁ L T) R₂ t = szT₁ L T ⊔ zpowers t :=
      le_antisymm (fun y hy => hTR₁T y (mem_inf.mp hy).1 (mem_inf.mp hy).2)
        (le_inf (sup_le (szT₁_le_left L T) (zpowers_le.mpr htT)) hT₁tR₁)
    rw [hTR₁eq, h.card_szT₁_sup_of_card_sylow hS2] at hp2
    have hBT : B ⊔ szR (szT₁ L T) R₂ t ≤ T ⊔ szR (szT₁ L T) R₂ t :=
      sup_le (hB.trans (sup_le_sup_left hR₂R₁ T)) le_sup_right
    have h3 := card_le_of_le hBT
    have hT := h.card_le_mul_of_card_sylow hS2
    have hR₁pos : 0 < Nat.card (szR (szT₁ L T) R₂ t) := Nat.card_pos
    have key : Nat.card B * (Nat.card (szR (szT₁ L T) R₂ t) * (2 * (2 ^ f) ^ 3)) ≤
        (2 * f * Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G)) *
          (Nat.card (szR (szT₁ L T) R₂ t) * (2 * (2 ^ f) ^ 3)) := by
      calc Nat.card B * (Nat.card (szR (szT₁ L T) R₂ t) * (2 * (2 ^ f) ^ 3)) =
          (Nat.card B * Nat.card (szR (szT₁ L T) R₂ t)) * (2 * (2 ^ f) ^ 3) := by ring
        _ = (Nat.card (B ⊔ szR (szT₁ L T) R₂ t : Subgroup G) *
            Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G)) * (2 * (2 ^ f) ^ 3) := by rw [hp1]
        _ ≤ (Nat.card (T ⊔ szR (szT₁ L T) R₂ t : Subgroup G) *
            Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G)) * (2 * (2 ^ f) ^ 3) := by gcongr
        _ = (Nat.card (T ⊔ szR (szT₁ L T) R₂ t : Subgroup G) * (2 * (2 ^ f) ^ 3)) *
            Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G) := by ring
        _ = (Nat.card T * Nat.card (szR (szT₁ L T) R₂ t)) *
            Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G) := by rw [hp2]
        _ ≤ ((2 * (2 ^ f) ^ 3 * (2 * f)) * Nat.card (szR (szT₁ L T) R₂ t)) *
            Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G) := by gcongr
        _ = (2 * f * Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G)) *
            (Nat.card (szR (szT₁ L T) R₂ t) * (2 * (2 ^ f) ^ 3)) := by ring
    have hBf := Nat.le_of_mul_le_mul_right key (Nat.mul_pos hR₁pos (by positivity))
    have hlt := two_mul_lt_two_pow hf3
    have : (2 ^ f) ^ 3 < (2 ^ f) ^ 3 := by
      calc (2 ^ f) ^ 3 ≤ Nat.card B := hcard
        _ ≤ 2 * f * Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G) := hBf
        _ ≤ 2 * f * (2 ^ f) ^ 2 := Nat.mul_le_mul_left _ hBR₁q
        _ < 2 ^ f * (2 ^ f) ^ 2 := Nat.mul_lt_mul_of_pos_right hlt (by positivity)
        _ = (2 ^ f) ^ 3 := by ring
    exact lt_irrefl _ this
  ·
    push Not at hcase
    have hx2 : x ^ 2 ∈ szT₁ L T ⊔ zpowers t := (hsqR₁ x hxT r hr).mp (hcase _ hbB)
    have hB2 : Nat.card B ≤ 2 * Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G) := by
      refine card_le_two_mul_card_inf B _ fun b₁ hb₁ b₂ hb₂ hb₁R hb₂R => ?_
      obtain ⟨x₁, hx₁T, r₁, hr₁, rfl⟩ := hdec b₁ (hB hb₁)
      obtain ⟨x₂, hx₂T, r₂, hr₂, rfl⟩ := hdec b₂ (hB hb₂)
      have hx₁S : x₁ ∉ szT₁ L T ⊔ zpowers t := fun h1 => hb₁R ((hmemR₁ x₁ hx₁T r₁ hr₁).mpr h1)
      have hx₂S : x₂ ∉ szT₁ L T ⊔ zpowers t := fun h1 => hb₂R ((hmemR₁ x₂ hx₂T r₂ hr₂).mpr h1)
      have hx₁2 := (hsqR₁ x₁ hx₁T r₁ hr₁).mp (hcase _ hb₁)
      have hx₂2 := (hsqR₁ x₂ hx₂T r₂ hr₂).mp (hcase _ hb₂)
      obtain ⟨μ₁, -, τ₁, e₁, hd₁⟩ := hS.semilinear x₁ (h.le_normalizer hx₁T) (hTN₁ hx₁T)
      obtain ⟨μ₂, -, τ₂, e₂, hd₂⟩ := hS.semilinear x₂ (h.le_normalizer hx₂T) (hTN₁ hx₂T)
      obtain ⟨hτ₁, -⟩ := hS.sigma_of_sq_mem h hS2 hx₁T hx₁S hx₁2 hd₁
      obtain ⟨hτ₂, -⟩ := hS.sigma_of_sq_mem h hS2 hx₂T hx₂S hx₂2 hd₂
      have h12 : x₁ * x₂ ∈ szT₁ L T ⊔ zpowers t := by
        refine hS.mem_sup_of_u_conj_eq_mul h hS2 (mul_mem hx₁T hx₂T) (μ := μ₁ * σ μ₂)
          fun y hy => ?_
        have hy₂ : x₂ * y * x₂⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hx₂T) y).mp hy
        have e : x₁ * x₂ * y * (x₁ * x₂)⁻¹ = x₁ * (x₂ * y * x₂⁻¹) * x₁⁻¹ := by group
        rw [e, (hd₁ _ hy₂).1, (hd₂ y hy).1, hτ₁, hτ₂, map_mul, hσσ]
        ring
      have hx₁i : x₁⁻¹ * x₂ ∈ szT₁ L T ⊔ zpowers t := by
        have e : x₁⁻¹ * x₂ = (x₁ ^ 2)⁻¹ * (x₁ * x₂) := by rw [sq]; group
        rw [e]
        exact mul_mem (inv_mem hx₁2) h12
      have e : (x₁ * r₁)⁻¹ * (x₂ * r₂) = r₁⁻¹ * (x₁⁻¹ * x₂) * r₂ := by group
      rw [e]
      exact mul_mem (mul_mem (hR₂R₁ (inv_mem hr₁)) (hT₁tR₁ hx₁i)) (hR₂R₁ hr₂)
    have hBR₁q : Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G) ≤ 2 * (2 ^ f) ^ 2 := by
      by_cases hsub : B ⊓ szR (szT₁ L T) R₂ t ≤ szT₁ L T ⊔ R₂
      · have h1 : B ⊓ szR (szT₁ L T) R₂ t ≤ B ⊓ (szT₁ L T ⊔ R₂) := le_inf inf_le_left hsub
        have h2 := hBH₁ x hxT r hr hbB hxS
        have h3 : Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 2 ^ f :=
          hA₁card ▸ card_le_of_le inf_le_left
        calc Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G) ≤
            Nat.card (B ⊓ (szT₁ L T ⊔ R₂) : Subgroup G) := card_le_of_le h1
          _ ≤ 2 * Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 := h2
          _ ≤ 2 * (2 ^ f) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 2)
      · obtain ⟨s, hs, hsH⟩ := Set.not_subset.mp hsub
        obtain ⟨w, hw, hsw⟩ := hR.exists_eq_mul_t_of_not_mem (mem_inf.mp hs).2 hsH
        have h1 := hR.card_le_sq_of_comm_mul_t hab hA₁card (B₀ := B ⊓ (szT₁ L T ⊔ R₂))
          inf_le_right (fun a ha b hb => hBc a (mem_inf.mp ha).1 b (mem_inf.mp hb).1) hw
          (fun s' hs' => by rw [← hsw]; exact hBc s' (mem_inf.mp hs').1 s (mem_inf.mp hs).1)
        calc Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G) ≤
            2 * Nat.card (B ⊓ (szT₁ L T ⊔ R₂) : Subgroup G) := hBR₁H
          _ ≤ 2 * (2 ^ f) ^ 2 := Nat.mul_le_mul_left _ h1
    have : (2 ^ f) ^ 3 < (2 ^ f) ^ 3 := by
      calc (2 ^ f) ^ 3 ≤ Nat.card B := hcard
        _ ≤ 2 * Nat.card (B ⊓ szR (szT₁ L T) R₂ t : Subgroup G) := hB2
        _ ≤ 2 * (2 * (2 ^ f) ^ 2) := Nat.mul_le_mul_left _ hBR₁q
        _ = 4 * (2 ^ f) ^ 2 := by ring
        _ < 2 ^ f * (2 ^ f) ^ 2 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ = (2 ^ f) ^ 3 := by ring
    exact lt_irrefl _ this

end U3Start

section Certificates


theorem u3CharInputThree_holds : U3CharInputThree := by
  intro G _ _ L f t T R₂ h hS2 hR hf3 B hB hBc hcard
  obtain ⟨-, -, -, hNR₁, hNR₂, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  exact h.le_sup_of_comm_of_normalizer hS2 hR hf3 (hTA.trans hNR₂) (hTA.trans hNR₁) hB hBc hcard

end Certificates

end CFSG.SeitzReduction.RankOne
