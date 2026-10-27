
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryTransfer

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

theorem commutator_eq_of_simple {X : Type*} [Group X] {C : Subgroup X} [IsSimpleGroup C]
    (hne : ∃ a b : C, a * b ≠ b * a) : ⁅C, C⁆ = C := by
  have h1 : commutator ↥C = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥C) with h | h
    · obtain ⟨a, b, hab⟩ := hne
      have hm : ⁅a, b⁆ ∈ commutator ↥C := by
        rw [_root_.commutator_def]
        exact commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact absurd hm hab
    · exact h
  have h2 := map_commutator (⊤ : Subgroup ↥C) ⊤ C.subtype
  rw [← _root_.commutator_def, h1, ← MonoidHom.range_eq_map, range_subtype] at h2
  exact h2.symm

theorem not_isPGroup_quot_of_range {M X : Type*} [Group M] [Finite M] [Group X] (φ : M →* X)
    {C : Subgroup X} [IsSimpleGroup C] (hφ : φ.range = C) (h2 : 2 ∣ Nat.card C)
    (hp : ∀ n, Nat.card C ≠ 2 ^ n) : ¬ IsPGroup 2 (M ⧸ pPrimeCore 2 M) := by
  intro hM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup φ.range := (MulEquiv.subgroupCongr hφ).isSimpleGroup
  have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have hN : (pPrimeCore 2 M).Normal := pPrimeCore_normal
  have hN' := hN.map φ.rangeRestrict φ.rangeRestrict_surjective
  have hcard : Nat.card φ.range = Nat.card C := by rw [hφ]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pPrimeCore 2 M).map φ.rangeRestrict) with
    h | h
  · have hle : pPrimeCore 2 M ≤ φ.rangeRestrict.ker := by
      rw [← Subgroup.map_eq_bot_iff]
      exact h
    have hs := QuotientGroup.lift_surjective_of_surjective (pPrimeCore 2 M) φ.rangeRestrict
      φ.rangeRestrict_surjective hle
    have hpR : IsPGroup 2 φ.range := hM.of_surjective _ hs
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := φ.range)).1 hpR
    exact hp n (hcard ▸ hn)
  · have hd : Nat.card φ.range ∣ Nat.card (pPrimeCore 2 M) := by
      have := Subgroup.card_map_dvd (pPrimeCore 2 M) φ.rangeRestrict
      rwa [h, Subgroup.card_top] at this
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 M)) := pPrimeCore_coprime_card
    have h2' : 2 ∣ Nat.card (pPrimeCore 2 M) := (hcard ▸ h2).trans hd
    exact absurd (hcop.eq_one_of_dvd h2') (by norm_num)

variable {G : Type} [Group G]

@[expose] noncomputable def phiC (J : Subgroup G) (x : G) (q : Jhat J →* Equiv.Perm (Fin 42)) :
    ↥(J ⊓ centralizer ({x} : Set G)) →* Equiv.Perm (Fin 42) :=
  (q.comp (jq J)).comp (Subgroup.inclusion inf_le_left)

theorem range_le_of_realization {J : Subgroup G} {x : G} (hxN : x ∈ normalizer (J : Set G))
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S) {ρ : Equiv.Perm (Fin 42)}
    (hβ : ∀ e, q (betaHat J hxN e) = ρ * q e * ρ⁻¹) :
    (phiC J x q).range ≤ centralizer {ρ} ⊓ S := by
  rintro _ ⟨m, rfl⟩
  refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, hqS _⟩
  have hfix : betaHat J hxN (jq J ⟨m, m.2.1⟩) = jq J ⟨m, m.2.1⟩ := by
    rw [betaHat_mk]
    congr 1
    exact Subtype.ext (conj_eq_of_mem_centralizer m.2.2)
  have h1 := hβ (jq J ⟨m, m.2.1⟩)
  rw [hfix] at h1
  show q (jq J ⟨m, m.2.1⟩) * ρ = ρ * q (jq J ⟨m, m.2.1⟩)
  calc q (jq J ⟨m, m.2.1⟩) * ρ = ρ * q (jq J ⟨m, m.2.1⟩) * ρ⁻¹ * ρ := by rw [← h1]
    _ = ρ * q (jq J ⟨m, m.2.1⟩) := by group

variable [Finite G]

theorem exists_outer_realization {J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J)) {x : G}
    (hxN : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1) (hxK : x ∉ withKernel J) :
    ∃ q : Jhat J →* Equiv.Perm (Fin 42), (∀ e, q e ∈ S) ∧ (∀ s ∈ S, ∃ e, q e = s) ∧
      q.ker = center (Jhat J) ∧ (∀ e ∈ q.ker, e ^ 3 = 1 → e = 1) ∧
      ∃ ρ : Equiv.Perm (Fin 42), (ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) ∧
        ∀ e, q (betaHat J hxN e) = ρ * q e * ρ⁻¹ := by
  obtain ⟨q, hqS, hqsurj, hqker, h3⟩ := exists_jq hL
  obtain ⟨r, hrR, hr⟩ := exists_realization q hqS hqsurj (betaHat J hxN) (fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e)
  have hr2 : r * r = 1 := by
    have hc : r * r ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_, R.mul_mem hrR hrR⟩
      obtain ⟨e, rfl⟩ := hqsurj s hs
      have h1 := hr (betaHat J hxN e)
      rw [betaHat_betaHat J hxN hx2, hr e] at h1
      calc q e * (r * r) = r * (r * q e * r⁻¹) * r⁻¹ * (r * r) := by rw [← h1]
        _ = r * r * q e := by group
    rw [centralizer_S_inf_R] at hc
    exact (mem_bot.mp hc)
  have hrS : r ∉ S := by
    intro hrS
    obtain ⟨e₀, he₀⟩ := hqsurj r hrS
    exact hxK (mem_withKernel_of_realization hJ hxN hqker (e₀ := e₀) fun e => by
      rw [hr e, he₀])
  have hord : orderOf (⟨r, hrR⟩ : R) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => hrS ?_
    · simp only [OneMemClass.coe_one, pow_two]
      exact hr2
    · have h' : r = 1 := congrArg Subtype.val h
      rw [h']
      exact S.one_mem
  have hconj : ∃ ρ : Equiv.Perm (Fin 42), (ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) ∧
      ∃ c ∈ R, r = c * ρ * c⁻¹ := by
    rcases (PSL3Four.orderOf_eq_two_iff _).1 hord with h | h | h | h
    · exact absurd (mem_S_of_isConj₁ h) hrS
    · exact ⟨r₂, Or.inl rfl, eq_conj_of_isConj h⟩
    · exact ⟨r₃, Or.inr (Or.inl rfl), eq_conj_of_isConj h⟩
    · exact ⟨r₄, Or.inr (Or.inr rfl), eq_conj_of_isConj h⟩
  obtain ⟨ρ, hρ, c, hcR, hc⟩ := hconj
  obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj (R.inv_mem hcR)
  refine ⟨(MulAut.conj c⁻¹).toMonoidHom.comp q, hS', hsurj', by rw [hker', hqker],
    by rw [hker']; exact h3, ρ, hρ, fun e => ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hr e, hc]
  group

theorem le_range_of_perfect {J : Subgroup G} {x : G} (hxN : x ∈ normalizer (J : Set G))
    (hx2 : x * x = 1) {q : Jhat J →* Equiv.Perm (Fin 42)} (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hqker : q.ker = center (Jhat J)) {ρ : Equiv.Perm (Fin 42)}
    (hβ : ∀ e, q (betaHat J hxN e) = ρ * q e * ρ⁻¹)
    (hperf : ⁅centralizer {ρ} ⊓ S, centralizer {ρ} ⊓ S⁆ = centralizer {ρ} ⊓ S) :
    centralizer {ρ} ⊓ S ≤ (phiC J x q).range := by
  have hlift : ∀ a ∈ centralizer {ρ} ⊓ S, ∃ e : Jhat J, q e = a ∧
      e⁻¹ * betaHat J hxN e ∈ center (Jhat J) := by
    intro a ha
    obtain ⟨hac, haS⟩ := mem_inf.mp ha
    obtain ⟨e, rfl⟩ := hqsurj _ haS
    refine ⟨e, rfl, ?_⟩
    rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, hβ,
      ← mem_centralizer_singleton_iff.mp hac, mul_inv_cancel_right, inv_mul_cancel]
  rw [← hperf, commutator_le]
  intro a ha b hb
  obtain ⟨e, rfl, he⟩ := hlift a ha
  obtain ⟨f, rfl, hf⟩ := hlift b hb
  have hfix : betaHat J hxN ⁅e, f⁆ = ⁅e, f⁆ := by
    rw [map_commutatorElement, show betaHat J hxN e = e * (e⁻¹ * betaHat J hxN e) by group,
      show betaHat J hxN f = f * (f⁻¹ * betaHat J hxN f) by group,
      CFSG.SectionRank.commutatorElement_mul_mem_center _ _ he hf]
  obtain ⟨j, hj, hjx⟩ := exists_fixed_lift hxN hx2 hfix
  have hjc : (j : G) ∈ centralizer {x} := by
    apply mem_centralizer_of_conj_eq
    have := congrArg Subtype.val hjx
    rwa [coe_conjJ] at this
  refine ⟨⟨j, j.2, hjc⟩, ?_⟩
  show q (jq J j) = _
  rw [hj, map_commutatorElement]

private theorem ne_pow_168 : ∀ n, (168 : ℕ) ≠ 2 ^ n := fun n h => by
  have h3 : 3 ∣ 2 ^ n := h ▸ (by norm_num : 3 ∣ 168)
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

private theorem ne_pow_60 : ∀ n, (60 : ℕ) ≠ 2 ^ n := fun n h => by
  have h3 : 3 ∣ 2 ^ n := h ▸ (by norm_num : 3 ∣ 60)
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

theorem not_isPGroup_of_field_graph {J : Subgroup G} {x : G}
    (hxN : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1) {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hqker : q.ker = center (Jhat J))
    {ρ : Equiv.Perm (Fin 42)} (hρ : ρ = r₂ ∨ ρ = r₃)
    (hβ : ∀ e, q (betaHat J hxN e) = ρ * q e * ρ⁻¹) :
    ¬ IsPGroup 2 (↥(J ⊓ centralizer ({x} : Set G)) ⧸
      pPrimeCore 2 ↥(J ⊓ centralizer ({x} : Set G))) := by
  rcases hρ with rfl | rfl
  · have : IsSimpleGroup C₂ := isSimpleGroup_C₂
    have hperf : ⁅C₂, C₂⁆ = C₂ := commutator_eq_of_simple exists_mul_ne_C₂
    have hr := le_antisymm (range_le_of_realization hxN hqS hβ)
      (le_range_of_perfect hxN hx2 hqsurj hqker hβ hperf)
    refine not_isPGroup_quot_of_range (phiC J x q) (C := C₂) hr ?_ ?_
    · rw [card_C₂]
      norm_num
    · rw [card_C₂]
      exact ne_pow_168
  · have : IsSimpleGroup C₃ := isSimpleGroup_C₃
    have hperf : ⁅C₃, C₃⁆ = C₃ := commutator_eq_of_simple exists_mul_ne_C₃
    have hr := le_antisymm (range_le_of_realization hxN hqS hβ)
      (le_range_of_perfect hxN hx2 hqsurj hqker hβ hperf)
    refine not_isPGroup_quot_of_range (phiC J x q) (C := C₃) hr ?_ ?_
    · rw [card_C₃]
      norm_num
    · rw [card_C₃]
      exact ne_pow_60

end CFSG.ComponentClassification.GrSLit.L34Facts
