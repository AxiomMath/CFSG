module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterLevelTorus
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1RegularMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterDataCartan
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterStepLevel
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpStep

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem outerData_le_of_complement {G : Type*} [Group G] [Finite G] {U H X₁ X₂ : Subgroup G}
    {t d : G} (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ H) (hdt : d * t = t * d)
    (htU : t ∈ U)
    (hfix : ∀ w ∈ U, w⁻¹ * (d⁻¹ * w * d) ∈ H → w ∈ H ∨ t⁻¹ * w ∈ H)
    (hX₁U : X₁ ≤ U) (htX₁ : t ∉ X₁) (hdX₁ : d ∈ normalizer (X₁ : Set G)) (hHX₁ : H ≤ X₁)
    (hHX₂ : H ≤ X₂) (hX₂U : X₂ ≤ U) (hsup₂ : X₂ ⊔ zpowers t = U)
    (hdX₂ : d ∈ normalizer (X₂ : Set G)) : X₁ ≤ X₂ := by
  classical
  have hX₂n : ∀ u ∈ U, ∀ x ∈ X₂, u * x * u⁻¹ ∈ X₂ := fun u hu x hx => by
    rw [show u * x * u⁻¹ = (u * x * u⁻¹ * x⁻¹) * x by group]
    exact mul_mem (hHX₂ (hcomm u hu x (hX₂U hx))) hx
  have htX₂ : zpowers t ≤ normalizer (X₂ : Set G) := zpowers_le.mpr
    (mem_normalizer_iff.mpr fun x => ⟨fun hx => hX₂n t htU x hx, fun hx => by
      have := hX₂n t⁻¹ (inv_mem htU) _ hx
      rwa [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at this⟩)
  have hψX₂ : ∀ w ∈ U, w⁻¹ * (d⁻¹ * w * d) ∈ X₂ := by
    intro w hw
    rw [← hsup₂, sup_comm] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := ncyc_exists_mul_of_mem_sup htX₂ hw
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    have hdtn : d⁻¹ * t ^ n * d = t ^ n := by
      have hc : Commute d (t ^ n) := (Commute.zpow_right hdt n)
      rw [mul_assoc, ← hc.eq, inv_mul_cancel_left]
    have hb' : d⁻¹ * b * d ∈ X₂ := (mem_normalizer_iff''.mp hdX₂ b).mp hb
    have e : (t ^ n * b)⁻¹ * (d⁻¹ * (t ^ n * b) * d) =
        (t ^ n)⁻¹ * (t ^ n * (b⁻¹ * (d⁻¹ * b * d)) * (t ^ n)⁻¹) * t ^ n := by
      rw [show d⁻¹ * (t ^ n * b) * d = (d⁻¹ * t ^ n * d) * (d⁻¹ * b * d) by group, hdtn]
      group
    rw [e]
    have h1 : t ^ n * (b⁻¹ * (d⁻¹ * b * d)) * (t ^ n)⁻¹ ∈ X₂ :=
      hX₂n _ (zpow_mem htU n) _ (mul_mem (inv_mem hb) hb')
    have h2 := hX₂n _ (inv_mem (zpow_mem htU n)) _ h1
    rwa [inv_inv] at h2
  have hψX₁ : ∀ w ∈ X₁, w⁻¹ * (d⁻¹ * w * d) ∈ X₁ := fun w hw =>
    mul_mem (inv_mem hw) ((mem_normalizer_iff''.mp hdX₁ w).mp hw)
  have hinj : ∀ w ∈ X₁, ∀ w' ∈ X₁,
      (w⁻¹ * (d⁻¹ * w * d))⁻¹ * (w'⁻¹ * (d⁻¹ * w' * d)) ∈ H → w⁻¹ * w' ∈ H := by
    intro w hw w' hw' hH
    have hwU := hX₁U hw
    have hw'U := hX₁U hw'
    have hdw : d⁻¹ * w * d ∈ U := hX₁U ((mem_normalizer_iff''.mp hdX₁ w).mp hw)
    have hz : (w⁻¹ * w')⁻¹ * (d⁻¹ * (w⁻¹ * w') * d) ∈ H := by
      have e : (w⁻¹ * w')⁻¹ * (d⁻¹ * (w⁻¹ * w') * d) =
          (w'⁻¹ * (w * (d⁻¹ * w * d)⁻¹) * w'⁻¹⁻¹ * (w * (d⁻¹ * w * d)⁻¹)⁻¹) *
            (w * (d⁻¹ * w * d)⁻¹ * w⁻¹ * (d⁻¹ * w * d)⁻¹⁻¹) *
            ((w⁻¹ * (d⁻¹ * w * d))⁻¹ * (w'⁻¹ * (d⁻¹ * w' * d))) := by
        group
      rw [e]
      exact mul_mem (mul_mem (hcomm _ (inv_mem hw'U) _ (mul_mem hwU (inv_mem hdw)))
        (hcomm _ hwU _ (inv_mem hdw))) hH
    rcases hfix _ (mul_mem (inv_mem hwU) hw'U) hz with h1 | h1
    · exact h1
    · exfalso
      apply htX₁
      have h2 : w⁻¹ * w' ∈ X₁ := mul_mem (inv_mem hw) hw'
      rw [show t = (w⁻¹ * w') * (t⁻¹ * (w⁻¹ * w'))⁻¹ by group]
      exact mul_mem h2 (inv_mem (hHX₁ h1))
  let Ψ : X₁ → X₁ := fun w => ⟨(w : G)⁻¹ * (d⁻¹ * w * d), hψX₁ w w.2⟩
  let F : X₁ ⧸ H.subgroupOf X₁ → X₁ ⧸ H.subgroupOf X₁ := fun c =>
    ((Ψ (Quotient.out c) : X₁) : X₁ ⧸ H.subgroupOf X₁)
  have hFinj : Function.Injective F := by
    intro c c' hcc
    have h1 := QuotientGroup.eq.mp hcc
    rw [mem_subgroupOf] at h1
    have h2 := hinj _ (Quotient.out c).2 _ (Quotient.out c').2 h1
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
    exact QuotientGroup.eq.mpr (mem_subgroupOf.mpr h2)
  have hFsurj : Function.Surjective F := Finite.injective_iff_surjective.mp hFinj
  intro x hx
  obtain ⟨c, hc⟩ := hFsurj ((⟨x, hx⟩ : X₁) : X₁ ⧸ H.subgroupOf X₁)
  have h1 := QuotientGroup.eq.mp hc
  rw [mem_subgroupOf] at h1
  have h2 : (((Quotient.out c : X₁) : G)⁻¹ * (d⁻¹ * ((Quotient.out c : X₁) : G) * d))⁻¹ * x ∈ H :=
    h1
  rw [show x = (((Quotient.out c : X₁) : G)⁻¹ * (d⁻¹ * ((Quotient.out c : X₁) : G) * d)) *
    ((((Quotient.out c : X₁) : G)⁻¹ * (d⁻¹ * ((Quotient.out c : X₁) : G) * d))⁻¹ * x) by group]
  exact mul_mem (hψX₂ _ (hX₁U (Quotient.out c).2)) (hHX₂ h2)

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem outerData_eq_one_of_conj_eq (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {d : G}
    (htr : ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), b ≠ 1 → b' ≠ 1 →
      ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b') {b : G} (hb : b ∈ szA₁ (szT₁ L T))
    (hbd : d⁻¹ * b * d = b) : b = 1 := by
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  by_contra hb1
  have h2 : 2 < Nat.card (szA₁ (szT₁ L T)) := by
    rw [hA₁card]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  obtain ⟨b₁, hb₁, b₂, hb₂, h1, h2', h12⟩ := exists_two_ne_one h2
  obtain ⟨b', hb', hb'1, hbb'⟩ : ∃ b' ∈ szA₁ (szT₁ L T), b' ≠ 1 ∧ b' ≠ b := by
    by_cases hb₁b : b₁ = b
    · exact ⟨b₂, hb₂, h2', fun e => h12 (hb₁b.trans e.symm)⟩
    · exact ⟨b₁, hb₁, h1, hb₁b⟩
  obtain ⟨n, hn⟩ := htr b hb b' hb' hb1 hb'1
  have hc : Commute d b := by
    show d * b = b * d
    calc d * b = d * (d⁻¹ * b * d) := by rw [hbd]
      _ = b * d := by group
  have hfix : (d ^ n)⁻¹ * b * d ^ n = b := by
    rw [mul_assoc, ← (hc.pow_left n).eq, inv_mul_cancel_left]
  exact hbb' (hn.symm.trans hfix)

section Certificates



theorem outerData_isSylowOf (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) (hTR : T ≤ normalizer (R₂ : Set G))
    (htr : ∀ r ∈ R₂, ∃ x ∈ u3C1U L T R₂ t, x * t * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (u3C1U L T R₂ t ⊔ T)
      (normalizer (szR (szT₁ L T) R₂ t : Set G)) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hsyl⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  obtain ⟨hYT, hYA⟩ := h.normalizer_szR_le_normalizer_szT₁_of_inv hS2 hR hinv hne
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  have hcard := h.card_u3C1U_of_transitive hS2 hR hinv htr
  have hTY : T ≤ normalizer (szR (szT₁ L T) R₂ t : Set G) := fun s hs =>
    mem_normalizer_szR_of (hTN₁ hs) (hTR hs) (mem_centralizer_singleton_iff.mp (h.le hs))
  have hYU := le_normalizer_u3C1U hYT hYA
  have hU2 : IsPGroup 2 (u3C1U L T R₂ t) :=
    IsPGroup.of_card (n := 1 + f * 5) (by rw [hcard, pow_add, pow_mul, pow_one])
  have hTU2 : IsPGroup 2 (T ⊔ u3C1U L T R₂ t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' h.isPGroup hU2 (hTY.trans hYU)
  rw [sup_comm] at hTU2
  obtain ⟨P, hP, hUTP⟩ := exists_isSylowOf_le_of_isPGroup (sup_le u3C1U_le_normalizer hTY) hTU2
  have hPA2 : IsPGroup 2 (P ⊓ normalizer (szA L T t : Set G) : Subgroup G) :=
    hP.isPGroup.to_le inf_le_left
  obtain ⟨a, -, ha⟩ := exists_conj_mem_of_isSylowOf hsyl inf_le_right hPA2
  have hPAcard : Nat.card (P ⊓ normalizer (szA L T t : Set G) : Subgroup G) ≤
      Nat.card (T ⊔ R₂ : Subgroup G) := by
    have hle : (P ⊓ normalizer (szA L T t : Set G)).map (MulAut.conj a⁻¹).toMonoidHom ≤
        T ⊔ R₂ := by
      rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using ha x hx
    have h1 := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective] at h1
  have hPcard := (h.card_le_mul_card_inf_normalizer_szA hS2 hR hinv (H := P) hP.le
    (hP.le.trans hYA)).1
  have hab := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hTR
  have hce := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer (hTY.trans hYU)
  rw [hR.card] at hab
  rw [hcard] at hce
  have hb : 2 ^ f ≤ Nat.card (T ⊓ R₂ : Subgroup G) := by
    rw [← hA₁card]
    exact Subgroup.card_le_of_le (le_inf ((szA₁_le _).trans (szT₁_le_left L T)) hR.le)
  have he : Nat.card (T ⊓ u3C1U L T R₂ t : Subgroup G) ≤ 2 * (2 ^ f) ^ 3 := by
    have hle : T ⊓ u3C1U L T R₂ t ≤ szT₁ L T ⊔ zpowers t := by
      rw [← h.u3C1U_inf_centralizer hS2 hR]
      exact fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, h.le (mem_inf.mp hx).1⟩
    have htN : zpowers t ≤ normalizer (szT₁ L T : Set G) :=
      zpowers_le.mpr (centralizer_le_normalizer _ h.mem_centralizer_szT₁)
    have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer htN
    have ht2 : Nat.card (zpowers t) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h.sq_eq_one)
    have hpos : 0 < Nat.card (zpowers t ⊓ szT₁ L T : Subgroup G) := Nat.card_pos
    calc Nat.card (T ⊓ u3C1U L T R₂ t : Subgroup G) ≤ Nat.card (szT₁ L T ⊔ zpowers t : Subgroup G) :=
          Subgroup.card_le_of_le hle
      _ = Nat.card (zpowers t ⊔ szT₁ L T : Subgroup G) := by rw [sup_comm]
      _ ≤ Nat.card (zpowers t ⊔ szT₁ L T : Subgroup G) *
          Nat.card (zpowers t ⊓ szT₁ L T : Subgroup G) := Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card (zpowers t) * Nat.card (szT₁ L T) := hprod
      _ ≤ 2 * (2 ^ f) ^ 3 := by rw [hT₁card]; exact Nat.mul_le_mul_right _ ht2
  have hbpos : 0 < Nat.card (T ⊓ R₂ : Subgroup G) := Nat.card_pos
  have hepos : 0 < Nat.card (T ⊓ u3C1U L T R₂ t : Subgroup G) := Nat.card_pos
  set q := 2 ^ f with hq
  set b := Nat.card (T ⊓ R₂ : Subgroup G) with hbdef
  set e := Nat.card (T ⊓ u3C1U L T R₂ t : Subgroup G) with hedef
  have hle : Nat.card P * (b * e) ≤ Nat.card (u3C1U L T R₂ t ⊔ T : Subgroup G) * (b * e) := by
    calc Nat.card P * (b * e) ≤
          (q * Nat.card (T ⊔ R₂ : Subgroup G)) * (b * e) :=
          Nat.mul_le_mul_right _ (hPcard.trans (Nat.mul_le_mul_left _ hPAcard))
      _ = q * (Nat.card (T ⊔ R₂ : Subgroup G) * b) * e := by ring
      _ = q * (Nat.card T * q ^ 2) * e := by rw [hab]
      _ ≤ q * (Nat.card T * q ^ 2) * (2 * q ^ 3) := Nat.mul_le_mul_left _ he
      _ = 2 * q ^ 5 * Nat.card T * q := by ring
      _ ≤ 2 * q ^ 5 * Nat.card T * b := Nat.mul_le_mul_left _ hb
      _ = (Nat.card (T ⊔ u3C1U L T R₂ t : Subgroup G) * e) * b := by rw [hce]; ring
      _ = Nat.card (u3C1U L T R₂ t ⊔ T : Subgroup G) * (b * e) := by rw [sup_comm]; ring
  have hle' := Nat.le_of_mul_le_mul_right hle (Nat.mul_pos hbpos hepos)
  have heq : u3C1U L T R₂ t ⊔ T = P := Subgroup.eq_of_le_of_card_ge hUTP hle'
  rw [heq]
  exact hP

theorem outerData_fix (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {d : G}
    (hdY : d ∈ normalizer (szR (szT₁ L T) R₂ t : Set G)) (hdt : d * t = t * d)
    (hdfix : ∀ r ∈ R₂, r⁻¹ * (d⁻¹ * r * d) ∈ szA₁ (szT₁ L T) → r ∈ szA₁ (szT₁ L T)) :
    ∀ w ∈ u3C1U L T R₂ t, w⁻¹ * (d⁻¹ * w * d) ∈ szT₁ L T ⊔ R₂ →
      w ∈ szT₁ L T ⊔ R₂ ∨ t⁻¹ * w ∈ szT₁ L T ⊔ R₂ := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  have hR₁U := h.szR_le_u3C1U hS2 hR
  have hdtd : d * t * d⁻¹ = t := by rw [hdt, mul_inv_cancel_right]
  have hσ : ∀ z ∈ u3C1U L T R₂ t, z * t * z⁻¹ * t⁻¹ ∈ R₂ := fun z hz => by
    obtain ⟨r, hr, hrt⟩ := h.exists_conj_t_eq_of_inv hS2 hR hinv hz.1
    rw [hrt, mul_inv_cancel_right]; exact hr
  intro w hw hwd
  have hzR₁ : w⁻¹ * (d⁻¹ * w * d) ∈ szR (szT₁ L T) R₂ t := sup_le_szR _ _ _ hwd
  have hzU := hR₁U hzR₁
  have hzA : w⁻¹ * (d⁻¹ * w * d) ∈ normalizer (szA L T t : Set G) := by
    rw [← h.u3C1U_inf_normalizer_szA hS2 hR] at hzR₁; exact (mem_inf.mp hzR₁).2
  have hσz := h.exists_conj_t_eq_of_mem_szA hS2 hR hinv hzU.1
    ((mem_normalizer_iff.mp hzA t).mp (mem_sup_right (mem_zpowers t)))
  have h1 := U3C1.mul_conj_t_mem hR.le hR.comm (hR.le hσz)
    (fun s hs => h.conj_R₂_mem_u3C1U hS2 hR hinv hw hs) (fun a ha => conj_szA₁_of_mem_u3C1U hw ha)
    (conj_t_mem_self w) (conj_t_mem_self (w⁻¹ * (d⁻¹ * w * d)))
  set r := w * t * w⁻¹ * t⁻¹ with hrdef
  set c := w⁻¹ * (d⁻¹ * w * d) * t * (w⁻¹ * (d⁻¹ * w * d))⁻¹ * t⁻¹ with hcdef
  have hrR : r ∈ R₂ := hσ w hw
  have e : w * (w⁻¹ * (d⁻¹ * w * d)) * t * (w * (w⁻¹ * (d⁻¹ * w * d)))⁻¹ * (c * r * t)⁻¹ =
      (d⁻¹ * r * d) * (c * r)⁻¹ := by
    have e1 : w * (w⁻¹ * (d⁻¹ * w * d)) = d⁻¹ * w * d := by group
    rw [e1]
    calc d⁻¹ * w * d * t * (d⁻¹ * w * d)⁻¹ * (c * r * t)⁻¹ =
        d⁻¹ * w * (d * t * d⁻¹) * w⁻¹ * d * t⁻¹ * (c * r)⁻¹ := by group
      _ = d⁻¹ * (w * t * w⁻¹ * t⁻¹) * (t * d * t⁻¹) * (c * r)⁻¹ := by rw [hdtd]; group
      _ = (d⁻¹ * r * d) * (c * r)⁻¹ := by
          rw [← hrdef, show t * d * t⁻¹ = d by rw [← hdt, mul_inv_cancel_right]]
  rw [e] at h1
  have hdr : d⁻¹ * r * d ∈ R₂ := (mem_normalizer_iff''.mp (hNR₁ hdY).2 r).mp hrR
  have hrA : r ∈ szA₁ (szT₁ L T) := by
    refine hdfix r hrR ?_
    have e2 : r⁻¹ * (d⁻¹ * r * d) = (d⁻¹ * r * d) * (c * r)⁻¹ * c := by
      rw [hR.comm _ (inv_mem hrR) _ hdr]; group
    rw [e2]
    exact mul_mem h1 hσz
  have hwR := h.mem_szR_of_conj_t_mem_u3C1U hS2 hR hw hrA
  obtain ⟨w', hw', z', hz', rfl⟩ := exists_mul_of_mem_szR hR hwR
  rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz' with hz1 | hz1
  · left; rw [hz1, mul_one]; exact hw'
  · right
    rw [hz1, show t⁻¹ * (w' * t) = t⁻¹ * w' * t⁻¹⁻¹ by group]
    exact (mem_normalizer_iff.mp (inv_mem hR.t_mem_normalizer_sup) w').mp hw'

theorem outerData_one {R₂ D V : Subgroup G} {d : G}
    (H : U3C1OuterStepHyp G L f t T R₂ D d V 1) (hC : U3C1CartanFpf L T D d) :
    ∃ U U₁ : Subgroup G, U3C1OuterLevelData G L f t T D V U U₁ 1 := by
  obtain ⟨h, hS2, hR, hinv, hne, -, -, hc, -, hmove⟩ := H
  have hV := hc.eq_of_one hR
  rw [hV] at hc hmove ⊢
  obtain ⟨hYT, hYA⟩ := h.normalizer_szR_le_normalizer_szT₁_of_inv hS2 hR hinv hne
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨y₀, hy₀, r₀, hr₀, hr₀sq, hy₀t⟩ := hmove
  have hr₀A : r₀ ∉ szA₁ (szT₁ L T) := fun hA => by
    obtain ⟨x, hx, hxr⟩ := hR.exists_sq_eq_of_inv hinv hA
    exact hr₀sq x hx hxr
  obtain ⟨d₀, hd₀t, hd₀R, hd₀T, hd₀tr⟩ := hR.torus
  have htrY := exists_conj_t_of_move hR hinv hy₀ hr₀ hr₀A hy₀t
    (mem_normalizer_szR_of hd₀T hd₀R hd₀t) hd₀t hd₀R hd₀tr
  have htrE : ∀ r ∈ R₂, ∃ x ∈ normalizer (szR (szT₁ L T) R₂ t : Set G) ⊓
      centralizer (szA₁ (szT₁ L T) : Set G), x * t * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T) := by
    by_cases hf : f = 3
    · exact h.exists_conj_t_of_eight hS2 hR hinv hne hf htrY
    · exact h.exists_conj_t_of_ne_three hS2 hR hinv hne hf htrY
  obtain ⟨E, hEY, hEn, -, hEA, -, htr⟩ := h.exists_regular_of_transitive hS2 hR hinv hne htrE
  have htrU := h.exists_u3C1U_conj_of_transitive hS2 hR hinv hne hEY hEn hEA htr
  have hdD := hC.mem
  have hdL : d ∈ L := hC.le hdD
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  have hdR : d ∈ normalizer (R₂ : Set G) := hc.D_le hdD
  have hdT : d ∈ normalizer (szT₁ L T : Set G) := hC.le_normalizer hdD
  have hdY := mem_normalizer_szR_of hdT hdR hdt
  have hdodd : Odd (orderOf d) := Odd.of_dvd_nat hC.odd (Subgroup.orderOf_dvd_natCard D hdD)
  have hdfix : ∀ r ∈ R₂, r⁻¹ * (d⁻¹ * r * d) ∈ szA₁ (szT₁ L T) → r ∈ szA₁ (szT₁ L T) := by
    intro r hr ha
    refine hR.mem_szA₁_of_sq_eq_one_of_inv hinv hr ?_
    refine h.outerData_eq_one_of_conj_eq hS2 hC.trans (hR.sq_mem r hr) ?_
    set a := r⁻¹ * (d⁻¹ * r * d) with hadef
    have e1 : d⁻¹ * r * d = r * a := by rw [hadef]; group
    have hra : r * a = a * r := hR.comm r hr a (hR.le ha)
    calc d⁻¹ * r ^ 2 * d = (d⁻¹ * r * d) ^ 2 := by rw [sq, sq]; group
      _ = (r * a) ^ 2 := by rw [e1]
      _ = r ^ 2 * a ^ 2 := (Commute.mul_pow hra 2)
      _ = r ^ 2 := by rw [hR.sq_A₁ a ha, mul_one]
  obtain ⟨U₁, hHU₁, hU₁U, hUU₁, htU₁, hsupU₁, hdU₁, hinf⟩ :=
    h.exists_u3C1U₁ hS2 hR hinv hne hdY hdodd hdt hdfix
  have hDU₁ : D ≤ normalizer (U₁ : Set G) := fun x hx => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp (hC.le_zpowers hx)
    exact zpow_mem hdU₁ n
  have hfix := h.outerData_fix hS2 hR hinv hdY hdt hdfix
  have hR₁U := h.szR_le_u3C1U hS2 hR
  have htU : t ∈ u3C1U L T R₂ t := hR₁U (mem_szR_right _ _ _)
  have hUN := le_normalizer_u3C1U hYT hYA
  have hTY : T ≤ normalizer (szR (szT₁ L T) R₂ t : Set G) := fun s hs =>
    mem_normalizer_szR_of (hTN₁ hs) (hc.T_le hs) (mem_centralizer_singleton_iff.mp (h.le hs))
  have hmN : ∀ m ∈ T, (∀ x ∈ D, m * x * m⁻¹ ∈ D) → m ∈ normalizer (U₁ : Set G) := by
    intro m hmT hmD
    have hmY := hTY hmT
    have hmt : m * t = t * m := mem_centralizer_singleton_iff.mp (h.le hmT)
    set X := U₁.comap (MulAut.conj m).toMonoidHom with hXdef
    have hmemX : ∀ y, y ∈ X ↔ m * y * m⁻¹ ∈ U₁ := fun y => by
      rw [hXdef, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hXU : X ≤ u3C1U L T R₂ t := fun y hy => by
      have h1 := hU₁U ((hmemX y).mp hy)
      have h2 := (mem_normalizer_iff''.mp (hUN hmY) _).mp h1
      rwa [show m⁻¹ * (m * y * m⁻¹) * m = y by group] at h2
    have htX : t ∉ X := fun ht => htU₁ (by
      have := (hmemX t).mp ht
      rwa [show m * t * m⁻¹ = t by rw [hmt, mul_inv_cancel_right]] at this)
    have hdX : d ∈ normalizer (X : Set G) := by
      refine mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => (hmemX _).mpr ?_
      have hmd : m * d * m⁻¹ ∈ normalizer (U₁ : Set G) := hDU₁ (hmD d hdD)
      have h1 := (mem_normalizer_iff''.mp hmd _).mp ((hmemX y).mp hy)
      rwa [show (m * d * m⁻¹)⁻¹ * (m * y * m⁻¹) * (m * d * m⁻¹) = m * (d⁻¹ * y * d) * m⁻¹ by
        group] at h1
    have hHX : szT₁ L T ⊔ R₂ ≤ X := fun z hz => (hmemX z).mpr
      (hHU₁ ((mem_normalizer_iff.mp (mem_inf.mp (hNR₁ hmY)).1 z).mp hz))
    have hle := outerData_le_of_complement (fun x hx y hy => h.comm_mem_sup_of_u3C1U hS2 hR hinv
      hne hx hy) hdt htU hfix hXU htX hdX hHX hHU₁ hU₁U hsupU₁ hdU₁
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => hle ((hmemX _).mpr ?_)
    rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group]
  have hTU₁ : T ≤ normalizer (U₁ : Set G) := by
    intro s hs
    obtain ⟨n, hnT₁, hnD⟩ := hC.conj s hs
    have hm := hmN (n⁻¹ * s) (mul_mem (inv_mem (szT₁_le_left L T hnT₁)) hs) hnD
    have hn : n ∈ normalizer (U₁ : Set G) :=
      Subgroup.le_normalizer (hHU₁ (mem_sup_left hnT₁))
    rw [show s = n * (n⁻¹ * s) by group]
    exact mul_mem hn hm
  obtain ⟨e, heD, heA, hefpf⟩ := hC.fpf
  refine ⟨u3C1U L T R₂ t, U₁,
    { U_le := u3C1U_le_normalizer
      U_normal := hUN
      isSylowOf := h.outerData_isSylowOf hS2 hR hinv hne hc.T_le htrU
      card_U := by rw [h.card_u3C1U_of_transitive hS2 hR hinv htrU]
      szR_le := hR₁U
      conj_t_not_mem := fun u hu huR => h.conj_t_not_mem_u3C1U hS2 hR hinv hu huR
      conj_szA₁ := fun u hu b hb => U3Start.conj_szA₁_of_mem_u3C1U hu hb
      conj_T₁ := fun u hu y hy => hu.2.2.2 y hy
      conj_V₁ := fun u hu r hr => h.conj_R₂_mem_u3C1U hS2 hR hinv (hU₁U hu) hr
      inf_centralizer := h.u3C1U_inf_centralizer hS2 hR
      U₁_le := hU₁U
      U₁_normal := hUU₁
      sup_eq := hsupU₁
      t_not_mem := htU₁
      inf_eq := hinf
      D_le := hDU₁
      T_le := hTU₁
      torus := hc.torus_of_mem h hC.toU3C1Cartan hDU₁ heD heA hefpf }⟩

end Certificates


end U3Start

end CFSG.SeitzReduction.RankOne
