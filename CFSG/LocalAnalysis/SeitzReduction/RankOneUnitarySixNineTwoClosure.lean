module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineTwo

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def U3SixNineNormInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → U3U1Data G L f t T R₂ U₁ →
    (¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) →
    (∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T) →
    (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁ →
    ¬ ∀ v ∈ T, v ^ 2 = 1 → v ∉ szT₁ L T ⊔ zpowers t →
      ∃ g ∈ normalizer (szA₁ (szT₁ L T) : Set G) ⊓ normalizer (R₂ : Set G), g⁻¹ * t * g = v

namespace U3R2

variable {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G} {f : ℕ}

theorem comm_mem_szA₁ (hR : U3R2 G L T₁ R₂ t f) {v : G} (hvt : v * t = t * v)
    (hvR : v ∈ normalizer (R₂ : Set G)) (hvA : ∀ a ∈ szA₁ T₁, v * a = a * v) {r : G}
    (hr : r ∈ R₂) : r * v * r⁻¹ * v⁻¹ ∈ szA₁ T₁ := by
  have hvr : v * r * v⁻¹ ∈ R₂ := (mem_normalizer_iff.mp hvR r).mp hr
  have h1 : v⁻¹ * t = t * v⁻¹ := by
    calc v⁻¹ * t = v⁻¹ * (t * v) * v⁻¹ := by group
      _ = v⁻¹ * (v * t) * v⁻¹ := by rw [hvt]
      _ = t * v⁻¹ := by group
  have hρ : r * t * r⁻¹ * t = v * r * v⁻¹ * t * (v * r * v⁻¹)⁻¹ * t := by
    have := U3R2.rho_conj (D := v⁻¹) (u := r) h1
    simp only [inv_inv] at this
    rw [this, hvA _ (hR.rho_mem r hr), mul_inv_cancel_right]
  have h2 := hR.inv_mul_mem_of_rho_eq_rho hr hvr hρ
  have h3 : (r⁻¹ * (v * r * v⁻¹))⁻¹ ∈ szA₁ T₁ := inv_mem h2
  have e : r * v * r⁻¹ * v⁻¹ = r * (r⁻¹ * (v * r * v⁻¹))⁻¹ * r⁻¹ := by group
  rw [e, hR.comm r hr _ (hR.le h3), mul_inv_cancel_right]
  exact h3

end U3R2

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem mul_outer_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {v : G} (hvT : v ∈ T)
    (hv2 : v ^ 2 = 1) (hvS : v ∉ szT₁ L T ⊔ zpowers t) :
    t * v ∈ T ∧ (t * v) ^ 2 = 1 ∧ t * v ∉ szT₁ L T ⊔ zpowers t := by
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  refine ⟨mul_mem htT hvT, ?_, fun hm => hvS ?_⟩
  · have e : t * v * (t * v) = (t * t) * (v * v) := by
      calc t * v * (t * v) = t * (v * t) * v := by group
        _ = t * (t * v) * v := by rw [hvt]
        _ = (t * t) * (v * v) := by group
    rw [sq, e, ← sq, ← sq, h.sq_eq_one, hv2, one_mul]
  · have := mul_mem (inv_mem (mem_sup_right (mem_zpowers t))) hm
    rwa [inv_mul_cancel_left] at this

end U3Start

theorem mem_normalizer_szA_of_conj_mem {G : Type} [Group G] [Finite G] {L T : Subgroup G} {t b : G}
    (hbA : b ∈ normalizer (szA₁ (szT₁ L T) : Set G)) (hbt : b * t * b⁻¹ ∈ szA L T t) :
    b ∈ normalizer (szA L T t : Set G) := by
  have hle : szA L T t ≤ (szA L T t).comap (MulAut.conj b).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (zpowers_le.mpr ?_)
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_left ((mem_normalizer_iff.mp hbA a).mp ha)
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hbt
  refine mem_normalizer_of_forall_inv_mul_mul_mem (d := b⁻¹) (fun x hx => ?_) |> fun h1 => by
    simpa using inv_mem h1
  have := hle hx
  simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  simpa using this

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

section Certificates


theorem mem_of_conj_mem_sup_of_card_sylow (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) (hC : (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁)
    (hfus : ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t → ∃ c : G, c⁻¹ * t * c = w)
    {r x : G} (hr : r ∈ R₂) (hx : x⁻¹ * r * x ∈ T ⊔ R₂) : x⁻¹ * r * x ∈ R₂ := by
  obtain ⟨-, -, -, -, hNR, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  obtain ⟨-, -, -, -, hinvT₁, -, -⟩ := h.facts_of_card_sylow hS2
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  have hTR : T ≤ normalizer (R₂ : Set G) := fun s hs => hNR (hTA hs)
  have hy2 : (x⁻¹ * r * x) ^ 2 = 1 := by
    rw [show (x⁻¹ * r * x) ^ 2 = x⁻¹ * r ^ 2 * x by rw [sq, sq]; group, hU.sq_R₂ r hr, mul_one,
      inv_mul_cancel]
  have hyS : x⁻¹ * r * x ∈ U₁ ⊔ T :=
    (sup_le le_sup_right ((le_sup_right.trans hU.le).trans le_sup_left) : T ⊔ R₂ ≤ U₁ ⊔ T) hx
  by_cases hyU : x⁻¹ * r * x ∈ U₁
  · rw [sup_comm] at hx
    obtain ⟨r', hr', s, hs, hrs⟩ := exists_mul_eq_of_mem_sup_of_le_normalizer hTR hx
    have hsU : s ∈ U₁ := by
      have := mul_mem (inv_mem (hU.le (mem_sup_right hr'))) hyU
      rwa [← hrs, inv_mul_cancel_left] at this
    have hsT₁ : s ∈ szT₁ L T := by rw [← hU.inf_eq h hR]; exact mem_inf.mpr ⟨hsU, hs⟩
    have hs2 : s ^ 2 = 1 := by
      have hc : r' * s = s * r' := (hR.commT₁ s hsT₁ r' hr').symm
      rw [← hrs, (Commute.mul_pow hc 2), hU.sq_R₂ r' hr', one_mul] at hy2
      exact hy2
    rw [← hrs]
    exact mul_mem hr' (hR.le (hinvT₁ s hsT₁ hs2))
  · exfalso
    obtain ⟨w, hw, h1 | h1 | h1⟩ :=
      hU.exists_conj_of_sq_eq_one_of_card_sylow h hS2 hR hvT hv2 hvS hC hyS hy2 hyU
    · apply hU.conj_not_mem (x * w)
      rw [show x * w * t * (x * w)⁻¹ = x * (w * t * w⁻¹) * x⁻¹ by group, h1,
        show x * (x⁻¹ * r * x) * x⁻¹ = r by group]
      exact hU.le (mem_sup_right hr)
    · obtain ⟨c, hc⟩ := hfus v hvT hv2 hvS
      apply hU.conj_not_mem (x * w * c⁻¹)
      rw [show x * w * c⁻¹ * t * (x * w * c⁻¹)⁻¹ = x * (w * (c⁻¹ * t * c) * w⁻¹) * x⁻¹ by group,
        hc, h1, show x * (x⁻¹ * r * x) * x⁻¹ = r by group]
      exact hU.le (mem_sup_right hr)
    · obtain ⟨htvT, htv2, htvS⟩ := h.mul_outer_of_card_sylow hS2 hvT hv2 hvS
      obtain ⟨c, hc⟩ := hfus (t * v) htvT htv2 htvS
      apply hU.conj_not_mem (x * w * c⁻¹)
      rw [show x * w * c⁻¹ * t * (x * w * c⁻¹)⁻¹ = x * (w * (c⁻¹ * t * c) * w⁻¹) * x⁻¹ by group,
        hc, h1, show x * (x⁻¹ * r * x) * x⁻¹ = r by group]
      exact hU.le (mem_sup_right hr)

theorem mem_normalizer_of_conj_of_card_sylow (hU : U3U1Data G L f t T R₂ U₁)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) (hC : (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁)
    (hfus : ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t → ∃ c : G, c⁻¹ * t * c = w)
    {g v' : G} (hgA : g ∈ normalizer (szA₁ (szT₁ L T) : Set G)) (hv'T : v' ∈ T)
    (hv'2 : v' ^ 2 = 1) (hv'S : v' ∉ szT₁ L T ⊔ zpowers t) (hg : g⁻¹ * t * g = v') :
    g ∈ normalizer (R₂ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, hNR, hSyl⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  obtain ⟨-, hv'A, -, -⟩ := h.outer_facts_of_card_sylow hS2 hv'T hv'2 hv'S
  have hv't : v' * t = t * v' := mem_centralizer_singleton_iff.mp (h.le hv'T)
  have hv'R : v' ∈ normalizer (R₂ : Set G) := hNR (hTA hv'T)
  have hgt : g * v' * g⁻¹ = t := by rw [← hg]; group
  have hP : R₂.map (MulAut.conj g).toMonoidHom ≤ normalizer (szA L T t : Set G) := by
    rintro _ ⟨r, hr, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hrA : r ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun a ha =>
        (hR.comm a (hR.le ha) r hr))
    refine mem_normalizer_szA_of_conj_mem (mul_mem (mul_mem hgA hrA) (inv_mem hgA)) ?_
    have hc := hR.comm_mem_szA₁ hv't hv'R hv'A hr
    have e : g * r * g⁻¹ * t * (g * r * g⁻¹)⁻¹ =
        (g * (r * v' * r⁻¹ * v'⁻¹) * g⁻¹) * (g * v' * g⁻¹) := by
      rw [← hgt]; group
    rw [e, hgt]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp hgA _).mp hc))
      (mem_sup_right (mem_zpowers t))
  have hR2 : IsPGroup 2 R₂ := IsPGroup.of_card (n := 2 * f) (by rw [hR.card, ← pow_mul, mul_comm])
  obtain ⟨a, haN, ha⟩ := exists_conj_mem_of_isSylowOf hSyl hP (hR2.map _)
  have hcl : ∀ r ∈ R₂, (g⁻¹ * a)⁻¹ * r * (g⁻¹ * a) ∈ R₂ := by
    intro r hr
    refine hU.mem_of_conj_mem_sup_of_card_sylow h hS2 hR hvT hv2 hvS hC hfus hr ?_
    have := ha _ ⟨r, hr, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [show (g⁻¹ * a)⁻¹ * r * (g⁻¹ * a) = a⁻¹ * (g * r * g⁻¹) * a by group]
    exact this
  have hga : g⁻¹ * a ∈ normalizer (R₂ : Set G) := mem_normalizer_of_forall_inv_mul_mul_mem hcl
  rw [show g = a * (g⁻¹ * a)⁻¹ by group]
  exact mul_mem (hNR haN) (inv_mem hga)

end Certificates

end U3U1Data

section Certificates


theorem u3SixNineConjInput_of_norm (hnorm : U3SixNineNormInput) : U3SixNineConjInput := by
  intro G _ _ L f t T R₂ U₁ h hS2 hR hU hncyc hS hC
  by_contra hno
  push Not at hno
  apply hnorm G L f t T R₂ U₁ h hS2 hR hU hncyc hS hC
  intro v hvT hv2 hvS
  obtain ⟨g, hgA, hg⟩ := hno v hvT hv2 hvS
  have hfus : ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t → ∃ c : G, c⁻¹ * t * c = w :=
    fun w hwT hw2 hwS => by
      obtain ⟨c, -, hc⟩ := hno w hwT hw2 hwS
      exact ⟨c, hc⟩
  exact ⟨g, mem_inf.mpr ⟨hgA, hU.mem_normalizer_of_conj_of_card_sylow h hS2 hR hvT hv2 hvS hC
    hfus hgA hvT hv2 hvS hg⟩, hg⟩

theorem u3SixNineInput_of_norm (hnorm : U3SixNineNormInput) : U3SixNineInput :=
  u3SixNineInput_of_conj (u3SixNineConjInput_of_norm hnorm)

end Certificates

end CFSG.SeitzReduction.RankOne
