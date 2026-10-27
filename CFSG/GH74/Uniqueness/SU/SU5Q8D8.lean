module

public import CFSG.GH74.Uniqueness.SU.SU5Map

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup

theorem q8_sq : ∀ x : QuaternionGroup 2, x * x = 1 ∨ x * x = QuaternionGroup.a 2 := by
  decide +kernel

theorem q8_comm : ∀ x y : QuaternionGroup 2,
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = QuaternionGroup.a 2 := by decide +kernel

theorem q8_center : ∀ x : QuaternionGroup 2, (∀ y, x * y = y * x) →
    x = 1 ∨ x = QuaternionGroup.a 2 := by decide +kernel

theorem q8_ne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide +kernel

theorem d8_sq : ∀ x : DihedralGroup 4, x * x = 1 ∨ x * x = DihedralGroup.r 2 := by decide +kernel

theorem d8_comm : ∀ x y : DihedralGroup 4,
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = DihedralGroup.r 2 := by decide +kernel

theorem d8_center : ∀ x : DihedralGroup 4, (∀ y, x * y = y * x) →
    x = 1 ∨ x = DihedralGroup.r 2 := by decide +kernel

theorem d8_ne : (DihedralGroup.r 2 : DihedralGroup 4) ≠ 1 := by decide +kernel

theorem card_q8 : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem card_d8 : Nat.card (DihedralGroup 4) = 8 := by
  rw [Nat.card_eq_fintype_card, DihedralGroup.card]

section Generic

variable {G K : Type*} [Group G] [Group K]

theorem exists_zeta {Q : Subgroup G} (e : Q ≃* K) (ζk : K) (hne : ζk ≠ 1)
    (hsq : ∀ x : K, x * x = 1 ∨ x * x = ζk)
    (hcomm : ∀ x y : K, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = ζk)
    (hcen : ∀ x : K, (∀ y, x * y = y * x) → x = 1 ∨ x = ζk) :
    ∃ ζ : G, ζ ∈ Q ∧ ζ ≠ 1 ∧ (∀ q ∈ Q, q * q = 1 ∨ q * q = ζ) ∧
      (∀ q ∈ Q, ∀ q' ∈ Q, q * q' * q⁻¹ * q'⁻¹ = 1 ∨ q * q' * q⁻¹ * q'⁻¹ = ζ) ∧
      (∀ q ∈ Q, (∀ q' ∈ Q, q * q' = q' * q) → q = 1 ∨ q = ζ) := by
  refine ⟨(e.symm ζk : G), (e.symm ζk).2, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : e.symm ζk = 1 := Subtype.ext h
    exact hne ((MulEquiv.map_eq_one_iff e.symm).1 h1)
  · intro q hq
    rcases hsq (e ⟨q, hq⟩) with h | h
    · left
      have : (⟨q, hq⟩ : Q) * ⟨q, hq⟩ = 1 := e.injective (by rw [map_mul, h, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨q, hq⟩ : Q) * ⟨q, hq⟩ = e.symm ζk :=
        e.injective (by rw [map_mul, h, e.apply_symm_apply])
      exact congrArg Subtype.val this
  · intro q hq q' hq'
    rcases hcomm (e ⟨q, hq⟩) (e ⟨q', hq'⟩) with h | h
    · left
      have : (⟨q, hq⟩ : Q) * ⟨q', hq'⟩ * (⟨q, hq⟩ : Q)⁻¹ * (⟨q', hq'⟩ : Q)⁻¹ = 1 :=
        e.injective (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, h, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨q, hq⟩ : Q) * ⟨q', hq'⟩ * (⟨q, hq⟩ : Q)⁻¹ * (⟨q', hq'⟩ : Q)⁻¹ = e.symm ζk :=
        e.injective (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, h, e.apply_symm_apply])
      exact congrArg Subtype.val this
  · intro q hq hc
    have hc' : ∀ y : K, e ⟨q, hq⟩ * y = y * e ⟨q, hq⟩ := by
      intro y
      have h1 := hc (e.symm y : G) (e.symm y).2
      have h2 : (⟨q, hq⟩ : Q) * e.symm y = e.symm y * ⟨q, hq⟩ := Subtype.ext h1
      have h3 := congrArg e h2
      rwa [map_mul, map_mul, e.apply_symm_apply] at h3
    rcases hcen (e ⟨q, hq⟩) hc' with h | h
    · left
      have : (⟨q, hq⟩ : Q) = 1 := (MulEquiv.map_eq_one_iff e).1 h
      exact congrArg Subtype.val this
    · right
      have : (⟨q, hq⟩ : Q) = e.symm ζk := by rw [← h, e.symm_apply_apply]
      exact congrArg Subtype.val this

theorem mem_sup_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  have hle : A ≤ Subgroup.normalizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have : a * b * a⁻¹ = b := by rw [hAB a ha b hb]; group
      rw [this]; exact hb
    · intro hb
      have h1 : a⁻¹ * (a * b * a⁻¹) = (a * b * a⁻¹) * a⁻¹ := (hAB a⁻¹ (A.inv_mem ha) _ hb)
      have : b = a * b * a⁻¹ := by
        calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
          _ = (a * b * a⁻¹) * a⁻¹ * a := by rw [h1]
          _ = a * b * a⁻¹ := by group
      rw [this]; exact hb
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hle
  have hg' : g ∈ ((A ⊔ B : Subgroup G) : Set G) := hg
  rw [hset] at hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg'
  exact ⟨a, ha, b, hb, rfl⟩

end Generic

section CentralProduct

variable {G : Type*} [Group G]

@[expose] def IsQ8D8 (N : Subgroup G) : Prop :=
  ∃ Q D : Subgroup G, Nonempty (Q ≃* QuaternionGroup 2) ∧ Nonempty (D ≃* DihedralGroup 4) ∧
    (∀ q ∈ Q, ∀ d ∈ D, q * d = d * q) ∧ Q ⊔ D = N ∧ Nat.card ↥(Q ⊓ D) = 2

theorem IsQ8D8.facts [Finite G] {N : Subgroup G} (h : IsQ8D8 N) :
    Nat.card N = 32 ∧ ∃ ζ : G, ζ ∈ N ∧ ζ ≠ 1 ∧
      (∀ n ∈ N, (∀ m ∈ N, n * m = m * n) ↔ (n = 1 ∨ n = ζ)) ∧
      (∀ n ∈ N, n * n = 1 ∨ n * n = ζ) := by
  obtain ⟨Q, D, ⟨eQ⟩, ⟨eD⟩, hcomm, hsup, hcard⟩ := h
  obtain ⟨ζq, hζqQ, hζq1, hQsq, -, hQcen⟩ :=
    exists_zeta eQ (QuaternionGroup.a 2) q8_ne q8_sq q8_comm q8_center
  obtain ⟨ζd, hζdD, hζd1, hDsq, -, hDcen⟩ :=
    exists_zeta eD (DihedralGroup.r 2) d8_ne d8_sq d8_comm d8_center
  have hQD1 : ∀ g ∈ Q ⊓ D, g = 1 ∨ g = ζq := fun g hg =>
    hQcen g hg.1 (fun q' hq' => (hcomm q' hq' g hg.2).symm)
  have hQD2 : ∀ g ∈ Q ⊓ D, g = 1 ∨ g = ζd := fun g hg =>
    hDcen g hg.2 (fun d' hd' => hcomm g hg.1 d' hd')
  have hne : Q ⊓ D ≠ ⊥ := by
    intro h0
    rw [h0] at hcard
    simp at hcard
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hgq : g = ζq := (hQD1 g hg).resolve_left hg1'
  have hgd : g = ζd := (hQD2 g hg).resolve_left hg1'
  have hζ : ζd = ζq := hgd.symm.trans hgq
  rw [hζ] at hDsq hDcen hζdD hζd1
  have hζQD : ζq ∈ Q ⊓ D := hgq ▸ hg
  have hζsq : ζq * ζq = 1 := by
    rcases hQsq ζq hζQD.1 with h | h
    · exact h
    · exact absurd (mul_eq_right.1 h) hζq1
  have hfac : ∀ n ∈ N, ∃ q ∈ Q, ∃ d ∈ D, q * d = n := fun n hn =>
    mem_sup_of_commute hcomm (hsup ▸ hn)
  refine ⟨?_, ζq, hsup ▸ (Subgroup.mem_sup_left hζQD.1), hζq1, ?_, ?_⟩
  · have h1 := card_sup_mul_card_inf_of_commute Q D hcomm
    rw [hsup, hcard, Nat.card_congr eQ.toEquiv, Nat.card_congr eD.toEquiv, card_q8, card_d8] at h1
    omega
  · intro n hn
    constructor
    · intro hc
      obtain ⟨q, hq, d, hd, rfl⟩ := hfac n hn
      have hqc : ∀ q' ∈ Q, q * q' = q' * q := by
        intro q' hq'
        have h1 := hc q' (hsup ▸ Subgroup.mem_sup_left hq')
        have h2 : q * d * q' = q * q' * d := by
          rw [mul_assoc, ← hcomm q' hq' d hd, ← mul_assoc]
        have h3 : q' * (q * d) = q' * q * d := by rw [mul_assoc]
        rw [h2, h3] at h1
        exact mul_right_cancel h1
      have hdc : ∀ d' ∈ D, d * d' = d' * d := by
        intro d' hd'
        have h1 := hc d' (hsup ▸ Subgroup.mem_sup_right hd')
        have h2 : q * d * d' = q * (d * d') := by rw [mul_assoc]
        have h3 : d' * (q * d) = q * (d' * d) := by
          rw [← mul_assoc, ← hcomm q hq d' hd', mul_assoc]
        rw [h2, h3] at h1
        exact mul_left_cancel h1
      rcases hQcen q hq hqc with hq1 | hq1 <;> rcases hDcen d hd hdc with hd1 | hd1
      · left; rw [hq1, hd1]; simp
      · right; rw [hq1, hd1]; simp
      · right; rw [hq1, hd1]; simp
      · left; rw [hq1, hd1]; exact hζsq
    · intro hn1 m hm
      obtain ⟨q, hq, d, hd, rfl⟩ := hfac m hm
      rcases hn1 with h | h
      · rw [h]; simp
      · rw [h]
        have h1 : q * ζq = ζq * q := hcomm q hq ζq hζQD.2
        have h2 : ζq * d = d * ζq := hcomm ζq hζQD.1 d hd
        calc ζq * (q * d) = (ζq * q) * d := by rw [mul_assoc]
          _ = (q * ζq) * d := by rw [h1]
          _ = q * (ζq * d) := by rw [mul_assoc]
          _ = q * (d * ζq) := by rw [h2]
          _ = q * d * ζq := by rw [mul_assoc]
  · intro n hn
    obtain ⟨q, hq, d, hd, rfl⟩ := hfac n hn
    have hcm : q * d * (q * d) = (q * q) * (d * d) := by
      calc q * d * (q * d) = q * (d * q) * d := by group
        _ = q * (q * d) * d := by rw [hcomm q hq d hd]
        _ = (q * q) * (d * d) := by group
    rw [hcm]
    rcases hQsq q hq with h1 | h1 <;> rcases hDsq d hd with h2 | h2 <;> rw [h1, h2]
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
    · exact Or.inr (by simp)
    · exact Or.inl hζsq

theorem isQ8D8_map_iff {M : Type*} [Group M] {f : M →* G} (hf : Function.Injective f)
    {X : Subgroup M} : IsQ8D8 (X.map f) ↔ IsQ8D8 X := by
  constructor
  · rintro ⟨Q, D, ⟨eQ⟩, ⟨eD⟩, hcomm, hsup, hcard⟩
    have hQle : Q ≤ f.range := (le_sup_left.trans hsup.le).trans (Subgroup.map_le_range f X)
    have hDle : D ≤ f.range := (le_sup_right.trans hsup.le).trans (Subgroup.map_le_range f X)
    obtain ⟨Q₀, rfl⟩ := exists_eq_map_of_le_range hQle
    obtain ⟨D₀, rfl⟩ := exists_eq_map_of_le_range hDle
    refine ⟨Q₀, D₀, ⟨(Subgroup.equivMapOfInjective Q₀ f hf).trans eQ⟩,
      ⟨(Subgroup.equivMapOfInjective D₀ f hf).trans eD⟩, ?_, ?_, ?_⟩
    · intro q hq d hd
      have h1 := hcomm (f q) (Subgroup.mem_map_of_mem f hq) (f d) (Subgroup.mem_map_of_mem f hd)
      exact hf (by rw [map_mul, map_mul]; exact h1)
    · apply Subgroup.map_injective hf
      rw [Subgroup.map_sup, hsup]
    · rw [← Subgroup.card_map_of_injective hf, Subgroup.map_inf_eq _ _ f hf]
      exact hcard
  · rintro ⟨Q, D, ⟨eQ⟩, ⟨eD⟩, hcomm, hsup, hcard⟩
    refine ⟨Q.map f, D.map f, ⟨(Subgroup.equivMapOfInjective Q f hf).symm.trans eQ⟩,
      ⟨(Subgroup.equivMapOfInjective D f hf).symm.trans eD⟩, ?_, ?_, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩ _ ⟨d, hd, rfl⟩
      rw [← map_mul, ← map_mul, hcomm q hq d hd]
    · rw [← Subgroup.map_sup, hsup]
    · rw [← Subgroup.map_inf_eq _ _ f hf, Subgroup.card_map_of_injective hf]
      exact hcard

end CentralProduct

end CFSG.GH74.Uniqueness.SU.SU5
