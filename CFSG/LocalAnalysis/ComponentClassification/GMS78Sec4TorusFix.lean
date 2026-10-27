module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push28U
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Base

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

namespace TorusFix

variable {A : Type*} [Group A] {δ : MulAut A}

theorem eq_one_of_commute (htr : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ π ∈ zpowers δ, π a = b)
    {τ : MulAut A} (hτ : Commute τ δ) {a : A} (ha : a ≠ 1) (h : τ a = a) : τ = 1 := by
  refine MulEquiv.ext fun b => ?_
  by_cases hb : b = 1
  · rw [hb, map_one, map_one]
  obtain ⟨π, hπ, rfl⟩ := htr a b ha hb
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hπ
  calc τ ((δ ^ i) a) = (τ * δ ^ i) a := rfl
    _ = (δ ^ i * τ) a := by rw [(hτ.zpow_right i).eq]
    _ = (δ ^ i) (τ a) := rfl
    _ = (1 : MulAut A) ((δ ^ i) a) := by rw [h]; rfl

theorem eq_one_of_apply_eq (htr : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ π ∈ zpowers δ, π a = b)
    {π : MulAut A} (hπ : π ∈ zpowers δ) {a : A} (ha : a ≠ 1) (h : π a = a) : π = 1 := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hπ
  exact eq_one_of_commute htr (Commute.zpow_left (Commute.refl δ) i) ha h

theorem mem_zpowers_of_commute (htr : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ π ∈ zpowers δ, π a = b)
    {σ : MulAut A} (hσ : Commute σ δ) : σ ∈ zpowers δ := by
  by_cases hA : ∃ a : A, a ≠ 1
  · obtain ⟨a, ha⟩ := hA
    have hσa : σ a ≠ 1 := fun h1 => ha (by simpa using congrArg σ.symm h1)
    obtain ⟨π, hπ, hπa⟩ := htr a (σ a) ha hσa
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hπ
    have h1 : (δ ^ i)⁻¹ * σ = 1 := by
      refine eq_one_of_commute htr ((Commute.zpow_left (Commute.refl δ) i).inv_left.mul_left hσ)
        ha ?_
      calc ((δ ^ i)⁻¹ * σ) a = (δ ^ i)⁻¹ (σ a) := rfl
        _ = (δ ^ i)⁻¹ ((δ ^ i) a) := by rw [hπa]
        _ = a := by rw [← MulAut.mul_apply, inv_mul_cancel]; rfl
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    exact zpow_mem_zpowers δ i
  · push Not at hA
    have : σ = 1 := MulEquiv.ext fun b => by rw [hA b, map_one, map_one]
    rw [this]
    exact one_mem _

theorem conj_mem_zpowers {σ : MulAut A} (hσ : σ * δ * σ⁻¹ ∈ zpowers δ) {π : MulAut A}
    (hπ : π ∈ zpowers δ) : σ * π * σ⁻¹ ∈ zpowers δ := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hπ
  have : σ * δ ^ i * σ⁻¹ = (σ * δ * σ⁻¹) ^ i := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  rw [this]
  exact zpow_mem hσ i

theorem card_inf_centralizer_add_one [Finite A]
    (htr : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ π ∈ zpowers δ, π a = b) {σ : MulAut A}
    (hσ : σ * δ * σ⁻¹ ∈ zpowers δ) {a₀ : A} (ha₀ : a₀ ≠ 1) (hσa₀ : σ a₀ = a₀) :
    Nat.card (zpowers δ ⊓ centralizer {σ} : Subgroup (MulAut A)) + 1 =
      Nat.card {a : A // σ a = a} := by
  have hfix : ∀ π : MulAut A, π ∈ zpowers δ ⊓ centralizer {σ} → σ (π a₀) = π a₀ := by
    intro π hπ
    have hπσ : π * σ = σ * π := mem_centralizer_singleton_iff.mp (mem_inf.mp hπ).2
    calc σ (π a₀) = (σ * π) a₀ := rfl
      _ = (π * σ) a₀ := by rw [hπσ]
      _ = π (σ a₀) := rfl
      _ = π a₀ := by rw [hσa₀]
  let φ : Option (zpowers δ ⊓ centralizer {σ} : Subgroup (MulAut A)) → {a : A // σ a = a} :=
    fun o => o.elim ⟨1, map_one σ⟩ fun π => ⟨(π : MulAut A) a₀, hfix π π.2⟩
  have hinj : Function.Injective φ := by
    have hne : ∀ π : MulAut A, π a₀ ≠ 1 := fun π h1 =>
      ha₀ (by simpa using congrArg π.symm h1)
    rintro (_ | π₁) (_ | π₂) h12
    · rfl
    · exact absurd (congrArg Subtype.val h12).symm (hne _)
    · exact absurd (congrArg Subtype.val h12) (hne _)
    · have h : (π₁ : MulAut A) a₀ = (π₂ : MulAut A) a₀ := congrArg Subtype.val h12
      have hm : (π₂ : MulAut A)⁻¹ * π₁ ∈ zpowers δ :=
        mul_mem (inv_mem (mem_inf.mp π₂.2).1) (mem_inf.mp π₁.2).1
      have h1 := eq_one_of_apply_eq htr hm ha₀ (by
        rw [MulAut.mul_apply, h, ← MulAut.mul_apply, inv_mul_cancel]; rfl)
      rw [inv_mul_eq_one] at h1
      exact congrArg some (Subtype.ext h1.symm)
  have hsurj : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    by_cases hb1 : b = 1
    · exact ⟨none, Subtype.ext hb1.symm⟩
    obtain ⟨π, hπ, hπb⟩ := htr a₀ b ha₀ hb1
    have hσπ : σ * π * σ⁻¹ = π := by
      have hm : π⁻¹ * (σ * π * σ⁻¹) ∈ zpowers δ := mul_mem (inv_mem hπ) (conj_mem_zpowers hσ hπ)
      have hσ' : σ⁻¹ a₀ = a₀ := by
        conv_lhs => rw [← hσa₀]
        rw [← MulAut.mul_apply, inv_mul_cancel]; rfl
      have h1 := eq_one_of_apply_eq htr hm ha₀ (by
        simp only [MulAut.mul_apply, hσ', hπb, hb]
        rw [← hπb, ← MulAut.mul_apply, inv_mul_cancel]; rfl)
      rwa [inv_mul_eq_one, eq_comm] at h1
    have hc : π ∈ centralizer {σ} := by
      rw [mem_centralizer_singleton_iff]
      calc π * σ = σ * π * σ⁻¹ * σ := by rw [hσπ]
        _ = σ * π := by group
    exact ⟨some ⟨π, mem_inf.mpr ⟨hπ, hc⟩⟩, Subtype.ext hπb⟩
  rw [← Finite.card_option, Nat.card_eq_of_bijective φ ⟨hinj, hsurj⟩]

theorem card_zpowers_add_one [Finite A]
    (htr : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ π ∈ zpowers δ, π a = b) {a₀ : A} (ha₀ : a₀ ≠ 1) :
    Nat.card (zpowers δ) + 1 = Nat.card A := by
  have h := card_inf_centralizer_add_one (σ := 1) htr (by simp) ha₀ rfl
  have h1 : (zpowers δ ⊓ centralizer {(1 : MulAut A)} : Subgroup (MulAut A)) = zpowers δ :=
    inf_eq_left.mpr fun π _ => mem_centralizer_singleton_iff.mpr (by rw [mul_one, one_mul])
  rw [h1] at h
  rw [h]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun a => rfl)

theorem card_sub_one_dvd [Finite A]
    (htr : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ π ∈ zpowers δ, π a = b) {σ : MulAut A}
    (hσ : σ * δ * σ⁻¹ ∈ zpowers δ) {a₀ : A} (ha₀ : a₀ ≠ 1) (hσa₀ : σ a₀ = a₀) :
    Nat.card {a : A // σ a = a} - 1 ∣ Nat.card A - 1 := by
  rw [← card_inf_centralizer_add_one htr hσ ha₀ hσa₀, ← card_zpowers_add_one htr ha₀,
    Nat.add_sub_cancel, Nat.add_sub_cancel]
  exact card_dvd_of_le inf_le_left

private theorem eq_one_of_pow_three_of_pow_five {M : Type*} [Group M] {g : M} (h3 : g ^ 3 = 1)
    (h5 : g ^ 5 = 1) : g = 1 := by
  have : g = (g ^ 3) ^ 2 * (g ^ 5)⁻¹ := by group
  rw [this, h3, h5]
  simp

theorem commute_mul_of_card_eq_four [Finite A] (hA : Nat.card A = 16)
    (htr : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ π ∈ zpowers δ, π a = b) {σ₁ σ₂ : MulAut A}
    (h₁ : σ₁ * δ * σ₁⁻¹ ∈ zpowers δ) (h₂ : σ₂ * δ * σ₂⁻¹ ∈ zpowers δ)
    (h₁₁ : σ₁ * σ₁ = 1) (h₂₂ : σ₂ * σ₂ = 1) {a₁ a₂ : A} (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1)
    (hσa₁ : σ₁ a₁ = a₁) (hσa₂ : σ₂ a₂ = a₂) (hc₁ : Nat.card {a : A // σ₁ a = a} = 4)
    (hc₂ : Nat.card {a : A // σ₂ a = a} = 4) : Commute (σ₁ * σ₂) δ := by
  have hord : orderOf δ = 15 := by
    have := card_zpowers_add_one htr ha₁
    rw [Nat.card_zpowers, hA] at this
    omega
  have h15 : δ ^ (15 : ℕ) = 1 := by rw [← hord]; exact pow_orderOf_eq_one δ
  have key : ∀ σ : MulAut A, σ * δ * σ⁻¹ ∈ zpowers δ → σ * σ = 1 → ∀ a : A, a ≠ 1 → σ a = a →
      Nat.card {a : A // σ a = a} = 4 →
      Commute σ (δ ^ (5 : ℕ)) ∧ σ * δ ^ (3 : ℕ) * σ⁻¹ = (δ ^ (3 : ℕ))⁻¹ := by
    intro σ hσ hσσ a ha hσa hc
    set C := (zpowers δ ⊓ centralizer {σ} : Subgroup (MulAut A)) with hCdef
    have hC : Nat.card C = 3 := by
      have h0 := card_inf_centralizer_add_one htr hσ ha hσa
      rw [← hCdef] at h0
      omega
    have hC3 : ∀ c ∈ C, c ^ 3 = 1 := by
      intro c hc'
      have := pow_card_eq_one' (G := C) (x := ⟨c, hc'⟩)
      rw [hC] at this
      exact congrArg Subtype.val this
    have hmemC : ∀ c : MulAut A, c ∈ zpowers δ → Commute σ c → c ∈ C := fun c hc' hcσ =>
      mem_inf.mpr ⟨hc', mem_centralizer_singleton_iff.mpr hcσ.eq.symm⟩
    have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
    refine ⟨?_, ?_⟩
    ·
      obtain ⟨c, hcC, hc1⟩ : ∃ c ∈ C, c ≠ 1 := by
        by_contra hne
        push Not at hne
        have := (eq_bot_iff_forall C).mpr hne
        rw [this, card_bot] at hC
        omega
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (mem_inf.mp hcC).1
      have h3k : (15 : ℤ) ∣ k * 3 := by
        have := hC3 _ hcC
        rw [← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hord] at this
        exact_mod_cast this
      obtain ⟨j, rfl⟩ : (5 : ℤ) ∣ k := by omega
      have hj : ¬ (3 : ℤ) ∣ j := by
        intro h3
        apply hc1
        rw [← orderOf_dvd_iff_zpow_eq_one, hord]
        obtain ⟨t, rfl⟩ := h3
        exact ⟨t, by push_cast; ring⟩
      have hjj : (5 : ℤ) * (j * j) ≡ 5 [ZMOD ((orderOf δ : ℕ) : ℤ)] := by
        rw [hord]
        have : j % 3 = 1 ∨ j % 3 = 2 := by omega
        have hm : (j * j) % 3 = 1 := by
          rcases this with h | h <;> simp [Int.mul_emod, h]
        show (5 * (j * j)) % ((15 : ℕ) : ℤ) = 5 % ((15 : ℕ) : ℤ)
        push_cast
        omega
      have hcj : (δ ^ (5 * j)) ^ j = δ ^ (5 : ℕ) := by
        rw [← zpow_mul, mul_assoc, zpow_eq_zpow_iff_modEq.mpr hjj]
        rfl
      have : δ ^ (5 : ℕ) ∈ C := by
        rw [← hcj]
        exact zpow_mem hcC j
      exact (mem_centralizer_singleton_iff.mp (mem_inf.mp this).2).symm
    ·
      set x := σ * δ ^ (3 : ℕ) * σ⁻¹ with hxdef
      have hx : x ∈ zpowers δ := conj_mem_zpowers hσ (pow_mem (mem_zpowers δ) 3)
      have hcomm : Commute (δ ^ (3 : ℕ)) x := by
        obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hx
        rw [← hi, ← zpow_natCast]
        exact Commute.zpow_zpow_self δ _ _
      have hσx : σ * x * σ⁻¹ = δ ^ (3 : ℕ) := by
        rw [hxdef, hσinv]
        calc σ * (σ * δ ^ (3 : ℕ) * σ) * σ = (σ * σ) * δ ^ (3 : ℕ) * (σ * σ) := by group
          _ = δ ^ (3 : ℕ) := by rw [hσσ]; group
      have hfix : Commute σ (δ ^ (3 : ℕ) * x) := by
        show σ * (δ ^ (3 : ℕ) * x) = δ ^ (3 : ℕ) * x * σ
        calc σ * (δ ^ (3 : ℕ) * x) = (σ * δ ^ (3 : ℕ) * σ⁻¹) * (σ * x * σ⁻¹) * σ := by group
          _ = x * δ ^ (3 : ℕ) * σ := by rw [← hxdef, hσx]
          _ = δ ^ (3 : ℕ) * x * σ := by rw [hcomm.eq]
      have hmem : δ ^ (3 : ℕ) * x ∈ C :=
        hmemC _ (mul_mem (pow_mem (mem_zpowers δ) 3) hx) hfix
      have hx5 : x ^ 5 = 1 := by
        rw [hxdef, ← MulAut.conj_apply, ← map_pow, ← pow_mul]
        norm_num [h15]
      have h5 : (δ ^ (3 : ℕ) * x) ^ 5 = 1 := by
        rw [hcomm.mul_pow, hx5, ← pow_mul]
        norm_num [h15]
      have h1 := eq_one_of_pow_three_of_pow_five (hC3 _ hmem) h5
      rw [hxdef] at h1 ⊢
      exact (eq_inv_of_mul_eq_one_right h1)
  obtain ⟨c₁, i₁⟩ := key σ₁ h₁ h₁₁ a₁ ha₁ hσa₁ hc₁
  obtain ⟨c₂, i₂⟩ := key σ₂ h₂ h₂₂ a₂ ha₂ hσa₂ hc₂
  have h3 : Commute (σ₁ * σ₂) (δ ^ (3 : ℕ)) := by
    show σ₁ * σ₂ * δ ^ (3 : ℕ) = δ ^ (3 : ℕ) * (σ₁ * σ₂)
    have e₂ : σ₂ * δ ^ (3 : ℕ) = (δ ^ (3 : ℕ))⁻¹ * σ₂ := by
      rw [← i₂]; group
    have e₁ : σ₁ * (δ ^ (3 : ℕ))⁻¹ = δ ^ (3 : ℕ) * σ₁ := by
      have : σ₁ * (δ ^ (3 : ℕ))⁻¹ * σ₁⁻¹ = δ ^ (3 : ℕ) := by
        rw [show σ₁ * (δ ^ (3 : ℕ))⁻¹ * σ₁⁻¹ = (σ₁ * δ ^ (3 : ℕ) * σ₁⁻¹)⁻¹ by group, i₁, inv_inv]
      calc σ₁ * (δ ^ (3 : ℕ))⁻¹ = σ₁ * (δ ^ (3 : ℕ))⁻¹ * σ₁⁻¹ * σ₁ := by group
        _ = δ ^ (3 : ℕ) * σ₁ := by rw [this]
    calc σ₁ * σ₂ * δ ^ (3 : ℕ) = σ₁ * (σ₂ * δ ^ (3 : ℕ)) := by group
      _ = σ₁ * (δ ^ (3 : ℕ))⁻¹ * σ₂ := by rw [e₂]; group
      _ = δ ^ (3 : ℕ) * σ₁ * σ₂ := by rw [e₁]
      _ = δ ^ (3 : ℕ) * (σ₁ * σ₂) := by group
  have h5 : Commute (σ₁ * σ₂) (δ ^ (5 : ℕ)) := c₁.mul_left c₂
  have hδ : δ = (δ ^ (3 : ℕ)) ^ 2 * (δ ^ (5 : ℕ))⁻¹ := by group
  rw [hδ]
  exact (h3.pow_right 2).mul_right h5.inv_right

end TorusFix

variable {G : Type} [Group G]

private theorem commutator_mul_left_eq_of_commute {v u β : G} (h : Commute β u) :
    v * β * u * (v * β)⁻¹ * u⁻¹ = v * u * v⁻¹ * u⁻¹ := by
  calc v * β * u * (v * β)⁻¹ * u⁻¹ = v * (β * u) * β⁻¹ * v⁻¹ * u⁻¹ := by group
    _ = v * (u * β) * β⁻¹ * v⁻¹ * u⁻¹ := by rw [h.eq]
    _ = v * u * v⁻¹ * u⁻¹ := by group

private theorem commutator_mul_right_eq_of_commute {v u β : G} (h : Commute β v) :
    v * (u * β) * v⁻¹ * (u * β)⁻¹ = v * u * v⁻¹ * u⁻¹ := by
  calc v * (u * β) * v⁻¹ * (u * β)⁻¹ = v * u * (β * v⁻¹) * β⁻¹ * u⁻¹ := by group
    _ = v * u * (v⁻¹ * β) * β⁻¹ * u⁻¹ := by rw [h.inv_right.eq]
    _ = v * u * v⁻¹ * u⁻¹ := by group

theorem commute_of_mem_gmsA_of_mem_V {L T : Subgroup G} {β v : G} (hβ : β ∈ gmsA L T)
    (hv : v ∈ gmsV L T) : Commute β v := by
  obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_eq_of_mem_V hv
  have h1 : Commute β a := (mem_centralizer_iff.mp (mem_inf.mp hβ).2 a (mem_inf.mp ha).1).symm
  have h2 : Commute β t :=
    mem_centralizer_iff.mp (mem_inf.mp ht).2 β (mem_inf.mp (mem_inf.mp hβ).1).2
  exact h1.mul_right h2

namespace Sec4Base

variable [Finite G] {L T U₁ : Subgroup G}

theorem exists_comm_eq (hE : Sec4Base L T U₁)
    (hcard : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = Nat.card (gmsA L T))
    {u₀ : G} (hu₀ : u₀ ∈ U₁) (hu₀A : u₀ ∉ gmsA L T) {a : G} (ha : a ∈ gmsA L T) :
    ∃ t ∈ T ⊓ centralizer (L : Set G), t * u₀ * t⁻¹ * u₀⁻¹ = a := by
  let φ : (T ⊓ centralizer (L : Set G) : Subgroup G) → gmsA L T := fun t =>
    ⟨t * u₀ * (t : G)⁻¹ * u₀⁻¹, hE.comm_mem t t.2 u₀ hu₀⟩
  have hinj : Function.Injective φ := by
    intro t t' htt'
    have h1 : (t : G) * u₀ * (t : G)⁻¹ * u₀⁻¹ = t' * u₀ * (t' : G)⁻¹ * u₀⁻¹ :=
      congrArg Subtype.val htt'
    have h2 : ((t' : G)⁻¹ * t) * u₀ * ((t' : G)⁻¹ * t)⁻¹ = u₀ := by
      have h3 : (t : G) * u₀ * (t : G)⁻¹ = t' * u₀ * (t' : G)⁻¹ := by simpa using h1
      calc ((t' : G)⁻¹ * t) * u₀ * ((t' : G)⁻¹ * t)⁻¹ =
            (t' : G)⁻¹ * (t * u₀ * (t : G)⁻¹) * t' := by group
        _ = (t' : G)⁻¹ * (t' * u₀ * (t' : G)⁻¹) * t' := by rw [h3]
        _ = u₀ := by group
    have hmem : (t' : G)⁻¹ * t ∈ T ⊓ centralizer (L : Set G) := mul_mem (inv_mem t'.2) t.2
    by_contra hne
    have hne' : (t' : G)⁻¹ * t ≠ 1 := fun h0 => hne (Subtype.ext (by
      have := congrArg (fun z => (t' : G) * z) h0
      simpa using this))
    apply hu₀A
    rw [← hE.centralizer_eq _ hmem hne']
    refine mem_inf.mpr ⟨hu₀, mem_centralizer_singleton_iff.mpr ?_⟩
    calc u₀ * ((t' : G)⁻¹ * t) =
          ((t' : G)⁻¹ * t) * u₀ * ((t' : G)⁻¹ * t)⁻¹ * ((t' : G)⁻¹ * t) := by rw [h2]
      _ = ((t' : G)⁻¹ * t) * u₀ := by group
  obtain ⟨t, ht⟩ := ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩).2 ⟨a, ha⟩
  exact ⟨t, t.2, congrArg Subtype.val ht⟩

end Sec4Base

namespace Push28Out

variable {L T U₁ : Subgroup G} {q : ℕ} {y d : G}

theorem exists_conj_eq_mul_of_mem_V (hO : Push28Out L T U₁ q y d) (hy : Sec3.IsTorus L T y)
    {v : G} (hv : v ∈ gmsV L T) : ∃ β ∈ gmsA L T, d * v * d⁻¹ = v * β := by
  obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_eq_of_mem_V hv
  have hda : d * a * d⁻¹ ∈ gmsA L T := by
    rw [hO.conj_A a ha]
    exact (mem_normalizer_iff.mp hy.mem_normalizer_gmsA a).mp ha
  have hβ : a⁻¹ * (d * a * d⁻¹) ∈ gmsA L T := mul_mem (inv_mem ha) hda
  refine ⟨a⁻¹ * (d * a * d⁻¹), hβ, ?_⟩
  have hcomm : Commute (a⁻¹ * (d * a * d⁻¹)) t :=
    mem_centralizer_iff.mp (mem_inf.mp ht).2 _ (mem_inf.mp (mem_inf.mp hβ).1).2
  calc d * (a * t) * d⁻¹ = d * a * d⁻¹ * (d * t * d⁻¹) := by group
    _ = d * a * d⁻¹ * t := by rw [hO.conj_T₀ t ht]
    _ = a * ((a⁻¹ * (d * a * d⁻¹)) * t) := by group
    _ = a * (t * (a⁻¹ * (d * a * d⁻¹))) := by rw [hcomm.eq]
    _ = a * t * (a⁻¹ * (d * a * d⁻¹)) := by group

variable [Finite G]

theorem mem_normalizer_gmsA (hO : Push28Out L T U₁ q y d) (hy : Sec3.IsTorus L T y) :
    d ∈ normalizer (gmsA L T : Set G) :=
  mem_normalizer_of_conj_mem_of_finite' fun a ha => by
    rw [hO.conj_A a ha]
    exact (mem_normalizer_iff.mp hy.mem_normalizer_gmsA a).mp ha

omit [Finite G] in
theorem pow_conj_eq (hO : Push28Out L T U₁ q y d) (hy : Sec3.IsTorus L T y) (k : ℕ) :
    ∀ a ∈ gmsA L T, d ^ k * a * (d ^ k)⁻¹ = y ^ k * a * (y ^ k)⁻¹ := by
  induction k with
  | zero => intro a _; simp
  | succ k ih =>
    intro a ha
    have hya : y ^ k * a * (y ^ k)⁻¹ ∈ gmsA L T :=
      (mem_normalizer_iff.mp (pow_mem hy.mem_normalizer_gmsA k) a).mp ha
    calc d ^ (k + 1) * a * (d ^ (k + 1))⁻¹ = d * (d ^ k * a * (d ^ k)⁻¹) * d⁻¹ := by group
      _ = d * (y ^ k * a * (y ^ k)⁻¹) * d⁻¹ := by rw [ih a ha]
      _ = y * (y ^ k * a * (y ^ k)⁻¹) * y⁻¹ := hO.conj_A _ hya
      _ = y ^ (k + 1) * a * (y ^ (k + 1))⁻¹ := by group

theorem exists_apply_eq (hO : Push28Out L T U₁ q y d) (hy : Sec3.IsTorus L T y)
    (a b : gmsA L T) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ π ∈ zpowers ((gmsA L T).normalizerMonoidHom ⟨d, hO.mem_normalizer_gmsA hy⟩), π a = b := by
  have ha' : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  have hb' : (b : G) ≠ 1 := fun h => hb (Subtype.ext h)
  obtain ⟨m, hm⟩ := hy.trans a a.2 b b.2 ha' hb'
  refine ⟨((gmsA L T).normalizerMonoidHom ⟨d, hO.mem_normalizer_gmsA hy⟩ ^ m)⁻¹,
    inv_mem (pow_mem (mem_zpowers _) m), Subtype.ext ?_⟩
  rw [← map_pow, ← map_inv, normalizerMonoidHom_apply_apply_coe]
  have hc : (y ^ m)⁻¹ * a * y ^ m ∈ gmsA L T := by rw [hm]; exact b.2
  have h1 := hO.pow_conj_eq hy m _ hc
  rw [show y ^ m * ((y ^ m)⁻¹ * a * y ^ m) * (y ^ m)⁻¹ = a by group] at h1
  simp only [InvMemClass.coe_inv, SubmonoidClass.coe_pow, inv_inv]
  rw [← hm]
  calc (d ^ m)⁻¹ * a * d ^ m =
        (d ^ m)⁻¹ * (d ^ m * ((y ^ m)⁻¹ * a * y ^ m) * (d ^ m)⁻¹) * d ^ m := by
        rw [h1]
    _ = (y ^ m)⁻¹ * a * y ^ m := by group

theorem normalizerMonoidHom_y (hO : Push28Out L T U₁ q y d) (hy : Sec3.IsTorus L T y) :
    (gmsA L T).normalizerMonoidHom ⟨y, hy.mem_normalizer_gmsA⟩ =
      (gmsA L T).normalizerMonoidHom ⟨d, hO.mem_normalizer_gmsA hy⟩ :=
  MulEquiv.ext fun a => Subtype.ext (by
    rw [normalizerMonoidHom_apply_apply_coe, normalizerMonoidHom_apply_apply_coe]
    exact (hO.conj_A a a.2).symm)

theorem conj_mem_zpowers_of_mem_T (hO : Push28Out L T U₁ q y d) (hy : Sec3.IsTorus L T y)
    (h : Sec3 G L T) {t : G} (ht : t ∈ T) :
    (gmsA L T).normalizerMonoidHom ⟨t, h.le_normalizer_gmsA ht⟩ *
        (gmsA L T).normalizerMonoidHom ⟨d, hO.mem_normalizer_gmsA hy⟩ *
        ((gmsA L T).normalizerMonoidHom ⟨t, h.le_normalizer_gmsA ht⟩)⁻¹ ∈
      zpowers ((gmsA L T).normalizerMonoidHom ⟨d, hO.mem_normalizer_gmsA hy⟩) := by
  set ρ := (gmsA L T).normalizerMonoidHom
  set δ := ρ ⟨d, hO.mem_normalizer_gmsA hy⟩
  set M : Subgroup G := ((zpowers δ).comap ρ).map (normalizer (gmsA L T : Set G)).subtype
  have hyM : y ∈ M := mem_map.mpr ⟨⟨y, hy.mem_normalizer_gmsA⟩,
    mem_comap.mpr (by rw [hO.normalizerMonoidHom_y hy]; exact mem_zpowers δ), rfl⟩
  have hCM : centralizer (gmsV L T : Set G) ≤ M := by
    intro c hc
    have hcA : ∀ a ∈ gmsA L T, c * a * c⁻¹ = a := fun a ha => by
      rw [← mem_centralizer_iff.mp hc a (mem_sup_left ha), mul_inv_cancel_right]
    have hcN : c ∈ normalizer (gmsA L T : Set G) :=
      mem_normalizer_of_conj_mem_of_finite' fun a ha => by rw [hcA a ha]; exact ha
    refine mem_map.mpr ⟨⟨c, hcN⟩, mem_comap.mpr ?_, rfl⟩
    have : ρ ⟨c, hcN⟩ = 1 := MulEquiv.ext fun a => Subtype.ext (by
      rw [normalizerMonoidHom_apply_apply_coe]
      exact hcA a a.2)
    rw [this]
    exact one_mem _
  have htN : t⁻¹ ∈ normalizer (L : Set G) ⊓ normalizer (gmsV L T : Set G) :=
    mem_inf.mpr ⟨h.sylow.le (inv_mem ht), h.le_normalizer_gmsV (inv_mem ht)⟩
  have hty := hy.conj t⁻¹ htN
  rw [inv_inv] at hty
  obtain ⟨⟨g, hgN⟩, hg, hgeq⟩ := mem_map.mp ((sup_le (zpowers_le.mpr hyM) hCM) hty)
  have hg' : (⟨g, hgN⟩ : normalizer (gmsA L T : Set G)) =
      ⟨t, h.le_normalizer_gmsA ht⟩ * ⟨y, hy.mem_normalizer_gmsA⟩ *
        (⟨t, h.le_normalizer_gmsA ht⟩ : normalizer (gmsA L T : Set G))⁻¹ :=
    Subtype.ext hgeq
  have := mem_comap.mp hg
  rw [hg', map_mul, map_mul, map_inv, hO.normalizerMonoidHom_y hy] at this
  exact this

theorem conj_mem_zpowers_of_swap (hO : Push28Out L T U₁ q y d) (hy : Sec3.IsTorus L T y)
    (hE : Sec4Base L T U₁)
    (hcard : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = Nat.card (gmsA L T))
    (hlt : gmsA L T < U₁) {e : G} (heA : e ∈ normalizer (gmsA L T : Set G))
    (heV : rightConjugate (gmsV L T) e = U₁) (heU : rightConjugate U₁ e = gmsV L T) :
    (gmsA L T).normalizerMonoidHom ⟨e, heA⟩ *
        (gmsA L T).normalizerMonoidHom ⟨d, hO.mem_normalizer_gmsA hy⟩ *
        ((gmsA L T).normalizerMonoidHom ⟨e, heA⟩)⁻¹ ∈
      zpowers ((gmsA L T).normalizerMonoidHom ⟨d, hO.mem_normalizer_gmsA hy⟩) := by
  set ρ := (gmsA L T).normalizerMonoidHom
  have hUV : ∀ u ∈ U₁, e * u * e⁻¹ ∈ gmsV L T := fun u hu =>
    (mem_rightConjugate_iff _ _ _).mp (by rw [heV]; exact hu)
  have hVU' : ∀ v ∈ gmsV L T, e⁻¹ * v * e ∈ U₁ := fun v hv => by
    rw [← heV, mem_rightConjugate_iff, show e * (e⁻¹ * v * e) * e⁻¹ = v by group]
    exact hv
  have hUV' : ∀ u ∈ U₁, e⁻¹ * u * e ∈ gmsV L T := fun u hu => by
    rw [← heU, mem_rightConjugate_iff, show e * (e⁻¹ * u * e) * e⁻¹ = u by group]
    exact hu
  have hdU : ∀ u ∈ U₁, d * u * d⁻¹ ∈ U₁ := fun u hu =>
    (mem_normalizer_iff.mp hO.mem_normalizer u).mp hu
  set e' := e * d * e⁻¹ with he'
  have he'T : ∀ t ∈ T ⊓ centralizer (L : Set G), e' * t * e'⁻¹ ∈ gmsV L T := by
    intro t ht
    rw [show e' * t * e'⁻¹ = e * (d * (e⁻¹ * t * e) * d⁻¹) * e⁻¹ by rw [he']; group]
    exact hUV _ (hdU _ (hVU' t (mem_sup_right ht)))
  have he'U : ∀ u ∈ U₁, ∃ β ∈ gmsA L T, e' * u * e'⁻¹ = u * β := by
    intro u hu
    obtain ⟨β, hβ, hβeq⟩ := hO.exists_conj_eq_mul_of_mem_V hy (hUV' u hu)
    refine ⟨e * β * e⁻¹, (mem_normalizer_iff.mp heA β).mp hβ, ?_⟩
    calc e' * u * e'⁻¹ = e * (d * (e⁻¹ * u * e) * d⁻¹) * e⁻¹ := by rw [he']; group
      _ = e * (e⁻¹ * u * e * β) * e⁻¹ := by rw [hβeq]
      _ = u * (e * β * e⁻¹) := by group
  obtain ⟨u₀, hu₀, hu₀A⟩ := IsConcreteLE.exists_of_lt hlt
  have hkey : ∀ a ∈ gmsA L T, e' * (d * a * d⁻¹) * e'⁻¹ = d * (e' * a * e'⁻¹) * d⁻¹ := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := hE.exists_comm_eq hcard hu₀ hu₀A ha
    set u₁ := d * u₀ * d⁻¹ with hu₁def
    have hu₁ : u₁ ∈ U₁ := hdU u₀ hu₀
    set v' := e' * t * e'⁻¹ with hv'def
    have hv' : v' ∈ gmsV L T := he'T t ht
    obtain ⟨β₁, hβ₁, hβ₁eq⟩ := he'U u₁ hu₁
    obtain ⟨β₀, hβ₀, hβ₀eq⟩ := he'U u₀ hu₀
    obtain ⟨β₂, hβ₂, hβ₂eq⟩ := hO.exists_conj_eq_mul_of_mem_V hy hv'
    have hdt : d * t * d⁻¹ = t := hO.conj_T₀ t ht
    calc e' * (d * (t * u₀ * t⁻¹ * u₀⁻¹) * d⁻¹) * e'⁻¹
        = e' * (d * t * d⁻¹) * e'⁻¹ * (e' * u₁ * e'⁻¹) * (e' * (d * t * d⁻¹) * e'⁻¹)⁻¹ *
            (e' * u₁ * e'⁻¹)⁻¹ := by rw [hu₁def]; group
      _ = v' * (u₁ * β₁) * v'⁻¹ * (u₁ * β₁)⁻¹ := by rw [hdt, ← hv'def, hβ₁eq]
      _ = v' * u₁ * v'⁻¹ * u₁⁻¹ :=
        commutator_mul_right_eq_of_commute (commute_of_mem_gmsA_of_mem_V hβ₁ hv')
      _ = v' * β₂ * u₁ * (v' * β₂)⁻¹ * u₁⁻¹ :=
        (commutator_mul_left_eq_of_commute (hE.comm (hE.A_le hβ₂) hu₁)).symm
      _ = d * v' * d⁻¹ * (d * u₀ * d⁻¹) * (d * v' * d⁻¹)⁻¹ * (d * u₀ * d⁻¹)⁻¹ := by
        rw [hβ₂eq, ← hu₁def]
      _ = d * (v' * u₀ * v'⁻¹ * u₀⁻¹) * d⁻¹ := by group
      _ = d * (v' * (u₀ * β₀) * v'⁻¹ * (u₀ * β₀)⁻¹) * d⁻¹ := by
        rw [commutator_mul_right_eq_of_commute (commute_of_mem_gmsA_of_mem_V hβ₀ hv')]
      _ = d * (e' * t * e'⁻¹ * (e' * u₀ * e'⁻¹) * (e' * t * e'⁻¹)⁻¹ * (e' * u₀ * e'⁻¹)⁻¹) *
            d⁻¹ := by rw [← hβ₀eq, hv'def]
      _ = d * (e' * (t * u₀ * t⁻¹ * u₀⁻¹) * e'⁻¹) * d⁻¹ := by group
  have he'N : e' ∈ normalizer (gmsA L T : Set G) :=
    mul_mem (mul_mem heA (hO.mem_normalizer_gmsA hy)) (inv_mem heA)
  have hcomm : Commute (ρ ⟨e', he'N⟩) (ρ ⟨d, hO.mem_normalizer_gmsA hy⟩) :=
    MulEquiv.ext fun a => Subtype.ext (by
      simp only [MulAut.mul_apply]
      exact hkey a a.2)
  have hmem := TorusFix.mem_zpowers_of_commute (hO.exists_apply_eq hy) hcomm
  have heq : (⟨e', he'N⟩ : normalizer (gmsA L T : Set G)) =
      ⟨e, heA⟩ * ⟨d, hO.mem_normalizer_gmsA hy⟩ * (⟨e, heA⟩ : normalizer (gmsA L T : Set G))⁻¹ :=
    Subtype.ext rfl
  rw [heq, map_mul, map_mul, map_inv] at hmem
  exact hmem

end Push28Out

end CFSG.ComponentClassification.GMS78
