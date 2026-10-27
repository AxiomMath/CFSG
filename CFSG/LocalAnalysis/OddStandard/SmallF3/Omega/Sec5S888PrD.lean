module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PrA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888F2A

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private lemma sec5b_sq_of_pow4_of_iso {K : Subgroup G} (e : ↥K ≃* SL23) {z u : G}
    (hz : z ∈ K) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hu : u ∈ K) (hu4 : u ^ 4 = 1)
    (hu1 : u ≠ 1) (huz : u ≠ z) : u * u = z := by
  have hζ2 : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    apply Subtype.ext
    simpa using hz2
  have hζ1 : e ⟨z, hz⟩ ≠ 1 := by
    intro hc
    have hsub : (⟨z, hz⟩ : ↥K) = 1 := e.injective (by rw [hc, map_one])
    exact hz1 (congrArg Subtype.val hsub)
  have hu4' : (e ⟨u, hu⟩) ^ 4 = 1 := by
    rw [← map_pow, ← map_one e]
    congr 1
    apply Subtype.ext
    simpa using hu4
  have hprod : (e ⟨u, hu⟩ * e ⟨u, hu⟩) * (e ⟨u, hu⟩ * e ⟨u, hu⟩) = 1 := by
    have h4 : (e ⟨u, hu⟩) ^ 4 =
        ((e ⟨u, hu⟩) * e ⟨u, hu⟩) * (e ⟨u, hu⟩ * e ⟨u, hu⟩) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [h4] at hu4'
    exact hu4'
  rcases sec5b_sl23_eq_of_sq_eq_one hζ2 hζ1 hprod with h1 | h1
  · rcases sec5b_sl23_eq_of_sq_eq_one hζ2 hζ1 h1 with h2 | h2
    · have h2' : (⟨u, hu⟩ : ↥K) = 1 := by
        apply e.injective
        simpa [h2]
      exact absurd (congrArg Subtype.val h2') hu1
    · exact absurd (congrArg Subtype.val (e.injective h2)) huz
  · have hsub : (⟨u, hu⟩ * ⟨u, hu⟩ : ↥K) = ⟨z, hz⟩ := by
      apply e.injective
      rw [map_mul]
      exact h1
    simpa using congrArg Subtype.val hsub

private lemma sec5_sq_of_card_eq_two {H : Subgroup G} (hcard : Nat.card ↥H = 2) :
    ∀ x ∈ H, x * x = 1 := by
  intro x hx
  have hdvd : orderOf x ∣ Nat.card ↥H := Subgroup.orderOf_dvd_natCard H hx
  rw [hcard] at hdvd
  have h2 : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by simpa using hdvd)
  simpa [pow_two] using h2

private lemma sec5_proj_card_inf [Finite G] {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z)
    {P : Subgroup G} (hP : P ≤ K₁ ⊔ K₂) (eP : ↥P ≃* SL23)
    (hb : ∀ b ∈ K₂, ∃ a ∈ K₁, a * b ∈ P) : Nat.card ↥(P ⊓ K₁) = 2 := by
  have hK₂norm : K₂ ≤ Subgroup.normalizer K₁ := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb₂ a ha₁
    rw [← h.comm a ha₁ b hb₂, mul_assoc, mul_inv_cancel, mul_one]
    exact ha₁
  have hMnorm : K₁ ⊔ K₂ ≤ Subgroup.normalizer K₁ :=
    sup_le Subgroup.le_normalizer hK₂norm
  have hN₁ : (K₁.subgroupOf (K₁ ⊔ K₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hMnorm
  haveI : (K₁.subgroupOf (K₁ ⊔ K₂)).Normal := hN₁
  let ψ : ↥P →* (↥(K₁ ⊔ K₂) ⧸ (K₁.subgroupOf (K₁ ⊔ K₂))) :=
    (QuotientGroup.mk' (K₁.subgroupOf (K₁ ⊔ K₂))).comp (Subgroup.inclusion hP)
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (K₁.subgroupOf (K₁ ⊔ K₂)) x
    obtain ⟨a, ha, b, hb₂, hm⟩ := sec5b_mem_sup_of_comm h.comm m.2
    obtain ⟨a', ha', hp'⟩ := hb b hb₂
    have hm_eq : m = (⟨a, Subgroup.mem_sup_left ha⟩ : ↥(K₁ ⊔ K₂)) *
        ⟨b, Subgroup.mem_sup_right hb₂⟩ := Subtype.ext (by simpa using hm)
    have ha1 : QuotientGroup.mk' (K₁.subgroupOf (K₁ ⊔ K₂))
        (⟨a, Subgroup.mem_sup_left ha⟩ : ↥(K₁ ⊔ K₂)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ha)
    have ha'1 : QuotientGroup.mk' (K₁.subgroupOf (K₁ ⊔ K₂))
        (⟨a', Subgroup.mem_sup_left ha'⟩ : ↥(K₁ ⊔ K₂)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ha')
    have hincl : (Subgroup.inclusion hP ⟨a' * b, hp'⟩ : ↥(K₁ ⊔ K₂)) =
        (⟨a', Subgroup.mem_sup_left ha'⟩ : ↥(K₁ ⊔ K₂)) *
          ⟨b, Subgroup.mem_sup_right hb₂⟩ := by
      apply Subtype.ext
      simp [Subgroup.coe_inclusion]
    refine ⟨⟨a' * b, hp'⟩, ?_⟩
    change (QuotientGroup.mk' (K₁.subgroupOf (K₁ ⊔ K₂)))
        (Subgroup.inclusion hP ⟨a' * b, hp'⟩) =
      QuotientGroup.mk' (K₁.subgroupOf (K₁ ⊔ K₂)) m
    rw [hm_eq, map_mul, hincl, map_mul, ha'1, one_mul, ha1, one_mul]
  have hcardSL : Nat.card SL23 = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hcardM : Nat.card ↥(K₁ ⊔ K₂) = 288 := Sec5Pair.card_sup h
  have hcardK₁ : Nat.card ↥K₁ = 24 := by
    obtain ⟨e₁⟩ := h.iso₁
    exact (Nat.card_congr e₁.toEquiv).trans hcardSL
  have hcardN₁ : Nat.card ↥(K₁.subgroupOf (K₁ ⊔ K₂)) = 24 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv]
    exact hcardK₁
  have hquot : Nat.card (↥(K₁ ⊔ K₂) ⧸ (K₁.subgroupOf (K₁ ⊔ K₂))) = 12 := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (K₁.subgroupOf (K₁ ⊔ K₂))
    rw [hcardM, hcardN₁] at hcard
    omega
  have hcardP : Nat.card ↥P = 24 := (Nat.card_congr eP.toEquiv).trans hcardSL
  have hquotker : Nat.card (↥P ⧸ MonoidHom.ker ψ) = 12 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    rw [MonoidHom.range_eq_top.mpr hψ, Subgroup.card_top]
    exact hquot
  have hker : Nat.card ↥(MonoidHom.ker ψ) = 2 := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker ψ)
    rw [hcardP, hquotker] at hcard
    omega
  have hker_eq : MonoidHom.ker ψ = (P ⊓ K₁).subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk' (K₁.subgroupOf (K₁ ⊔ K₂)))
        (Subgroup.inclusion hP p) = 1 ↔ p ∈ (P ⊓ K₁).subgroupOf P
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_inclusion, Subgroup.mem_inf, p.2, true_and]
  have hker_eq_card : Nat.card ↥(MonoidHom.ker ψ) = Nat.card ↥(P ⊓ K₁) := by
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hker_eq_card]
  exact hker

theorem Sec5Pair.case_odd {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z) {P : Subgroup G}
    (hP : P ≤ K₁ ⊔ K₂) (eP : ↥P ≃* SL23)
    (hb : ∀ b ∈ K₂, (∃ a ∈ K₁, a * b ∈ P) → b ^ 4 = 1) : P ≤ K₁ := by
  apply sec5_le_of_odd eP
  intro x hxP hxodd
  obtain ⟨a, ha, b, hb₂, hx_eq⟩ := sec5b_mem_sup_of_comm h.comm (hP hxP)
  have hb4 : b ^ 4 = 1 := hb b hb₂ ⟨a, ha, by rw [← hx_eq]; exact hxP⟩
  have hxodd' : Odd (orderOf (a * b)) := by
    rw [← hx_eq]
    exact hxodd
  rcases Sec5Pair.odd_elt h ha hb₂ hb4 hxodd' with hb1 | hbz
  · rw [hx_eq, hb1, mul_one]
    exact ha
  · rw [hx_eq, hbz]
    exact K₁.mul_mem ha h.z_mem₁

theorem Sec5Pair.case_full [Finite G] {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z)
    {P : Subgroup G} (hP : P ≤ K₁ ⊔ K₂) (eP : ↥P ≃* SL23)
    (hb : ∀ b ∈ K₂, ∃ a ∈ K₁, a * b ∈ P) (ha : ∀ a ∈ K₁, ∃ b ∈ K₂, a * b ∈ P) : False := by
  obtain ⟨e₁⟩ := h.iso₁
  obtain ⟨e₂⟩ := h.iso₂
  have hcardA : Nat.card ↥(P ⊓ K₁) = 2 := sec5_proj_card_inf h hP eP hb
  have hP21 : P ≤ K₂ ⊔ K₁ := hP.trans (le_of_eq (sup_comm K₁ K₂))
  have ha' : ∀ b ∈ K₁, ∃ a ∈ K₂, a * b ∈ P := by
    intro b hb'
    obtain ⟨c, hc, hpc⟩ := ha b hb'
    exact ⟨c, hc, by rwa [h.comm b hb' c hc] at hpc⟩
  have hcardB : Nat.card ↥(P ⊓ K₂) = 2 := sec5_proj_card_inf h.symm hP21 eP ha'
  have hsqA : ∀ x ∈ P ⊓ K₁, x * x = 1 := sec5_sq_of_card_eq_two hcardA
  have hsqB : ∀ x ∈ P ⊓ K₂, x * x = 1 := sec5_sq_of_card_eq_two hcardB
  obtain ⟨s, hs4, hss⟩ := (by decide +kernel : ∃ s : SL23, s ^ 4 = 1 ∧ s * s ≠ 1)
  let p : ↥P := eP.symm s
  have hp_apply : eP p = s := eP.apply_symm_apply s
  have hp4 : (p : G) ^ 4 = 1 := by
    have hsub : p ^ 4 = 1 := by
      apply eP.injective
      rw [map_pow, map_one, hp_apply, hs4]
    simpa using congrArg Subtype.val hsub
  have hpp_ne : (p : G) * p ≠ 1 := by
    intro hcon
    apply hss
    have h1 : p * p = 1 := Subtype.ext (by simpa using hcon)
    have h2 : eP p * eP p = 1 := by rw [← map_mul, h1, map_one]
    rwa [hp_apply] at h2
  obtain ⟨a, ha_mem, b, hb_mem, hp_eq, ha4, hb4⟩ := Sec5Pair.two_elt h (hP p.2) hp4
  have ha_cases : a = 1 ∨ a = z ∨ a * a = z := by
    by_cases h1 : a = 1
    · exact Or.inl h1
    · by_cases h2 : a = z
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr
          (sec5b_sq_of_pow4_of_iso e₁ h.z_mem₁ h.z_sq h.z_ne ha_mem ha4 h1 h2))
  have hb_cases : b = 1 ∨ b = z ∨ b * b = z := by
    by_cases h1 : b = 1
    · exact Or.inl h1
    · by_cases h2 : b = z
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr
          (sec5b_sq_of_pow4_of_iso e₂ h.z_mem₂ h.z_sq h.z_ne hb_mem hb4 h1 h2))
  rcases ha_cases with ha1 | haz | hass
  · exact hpp_ne (hsqB (p : G) ⟨p.2, by rw [hp_eq, ha1, one_mul]; exact hb_mem⟩)
  · exact hpp_ne (hsqB (p : G)
      ⟨p.2, by rw [hp_eq, haz]; exact K₂.mul_mem h.z_mem₂ hb_mem⟩)
  · rcases hb_cases with hb1 | hbz | hbss
    · exact hpp_ne (hsqA (p : G) ⟨p.2, by rw [hp_eq, hb1, mul_one]; exact ha_mem⟩)
    · exact hpp_ne (hsqA (p : G)
        ⟨p.2, by rw [hp_eq, hbz]; exact K₁.mul_mem ha_mem h.z_mem₁⟩)
    · have hprod : (a * b) * (a * b) = (a * a) * (b * b) := by
        rw [mul_assoc a b (a * b), ← mul_assoc b a b, ← h.comm a ha_mem b hb_mem,
          mul_assoc a b b, ← mul_assoc a a (b * b)]
      exact hpp_ne (by rw [hp_eq, hprod, hass, hbss, h.z_sq])

end CFSG.OddStandard.SmallF3.Omega
