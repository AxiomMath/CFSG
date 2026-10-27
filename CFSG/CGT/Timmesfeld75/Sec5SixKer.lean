module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.CGT.Timmesfeld75.Sec3TwelveIrr

public section

namespace CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G]

@[expose] def trivActing (X M : Subgroup G) (hMX : M ≤ X) : Subgroup G where
  carrier := {s | (∀ z ∈ X, s * z * s⁻¹ ∈ X ∧ s⁻¹ * z * s ∈ X) ∧
    ∀ z ∈ X, z⁻¹ * (s * z * s⁻¹) ∈ M}
  one_mem' := by
    refine ⟨fun z hz => ⟨by simpa using hz, by simpa using hz⟩, fun z hz => ?_⟩
    simp
  mul_mem' := by
    rintro s₁ s₂ ⟨hX₁, hM₁⟩ ⟨hX₂, hM₂⟩
    refine ⟨fun z hz => ⟨?_, ?_⟩, fun z hz => ?_⟩
    · have h1 := (hX₁ _ (hX₂ z hz).1).1
      have e : s₁ * (s₂ * z * s₂⁻¹) * s₁⁻¹ = s₁ * s₂ * z * (s₁ * s₂)⁻¹ := by group
      rwa [e] at h1
    · have h1 := (hX₂ _ (hX₁ z hz).2).2
      have e : s₂⁻¹ * (s₁⁻¹ * z * s₁) * s₂ = (s₁ * s₂)⁻¹ * z * (s₁ * s₂) := by group
      rwa [e] at h1
    · have hw := (hX₂ z hz).1
      have hm₂ := hM₂ z hz
      have hm₁ := hM₁ z hz
      have hn : s₁ * (z⁻¹ * (s₂ * z * s₂⁻¹)) * s₁⁻¹ ∈ M := by
        have h2 := hM₁ _ (hMX hm₂)
        have h3 := M.mul_mem hm₂ h2
        simpa [mul_assoc] using h3
      have e : z⁻¹ * (s₁ * s₂ * z * (s₁ * s₂)⁻¹) =
          (z⁻¹ * (s₁ * z * s₁⁻¹)) * (s₁ * (z⁻¹ * (s₂ * z * s₂⁻¹)) * s₁⁻¹) := by group
      rw [e]
      exact M.mul_mem hm₁ hn
  inv_mem' := by
    rintro s ⟨hX, hM⟩
    refine ⟨fun z hz => ⟨?_, ?_⟩, fun z hz => ?_⟩
    · simpa using (hX z hz).2
    · simpa using (hX z hz).1
    · have hz' := (hX z hz).2
      have h1 := hM _ hz'
      have e : (s⁻¹ * z * s)⁻¹ * (s * (s⁻¹ * z * s) * s⁻¹) = (z⁻¹ * (s⁻¹ * z * s))⁻¹ := by
        group
      rw [e] at h1
      have h2 := M.inv_mem h1
      simpa using h2

theorem le_trivActing {X M : Subgroup G} (hMX : M ≤ X) (hMn : ∀ x ∈ X, ∀ m ∈ M, x * m * x⁻¹ ∈ M) :
    M ≤ trivActing X M hMX := by
  intro m hm
  have hmX : m ∈ X := hMX hm
  refine ⟨fun z hz => ⟨X.mul_mem (X.mul_mem hmX hz) (X.inv_mem hmX),
    X.mul_mem (X.mul_mem (X.inv_mem hmX) hz) hmX⟩, fun z hz => ?_⟩
  have h1 := hMn z⁻¹ (X.inv_mem hz) m hm
  have h2 := M.mul_mem h1 (M.inv_mem hm)
  have e : z⁻¹ * m * z⁻¹⁻¹ * m⁻¹ = z⁻¹ * (m * z * m⁻¹) := by group
  rwa [e] at h2

theorem X_le_normalizer_trivActing {X M : Subgroup G} (hMX : M ≤ X)
    (hMn : ∀ x ∈ X, ∀ m ∈ M, x * m * x⁻¹ ∈ M) :
    X ≤ Subgroup.normalizer (trivActing X M hMX : Set G) := by
  have key : ∀ x ∈ X, ∀ s ∈ trivActing X M hMX, x * s * x⁻¹ ∈ trivActing X M hMX := by
    intro x hx s hs
    obtain ⟨hsX, hsM⟩ := hs
    refine ⟨fun z hz => ⟨?_, ?_⟩, fun z hz => ?_⟩
    · have h1 := X.mul_mem (X.mul_mem hx ((hsX (x⁻¹ * z * x) (by
        exact X.mul_mem (X.mul_mem (X.inv_mem hx) hz) hx)).1)) (X.inv_mem hx)
      have e : x * (s * (x⁻¹ * z * x) * s⁻¹) * x⁻¹ = x * s * x⁻¹ * z * (x * s * x⁻¹)⁻¹ := by
        group
      rw [e] at h1
      exact h1
    · have hz' : x⁻¹ * z * x ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hx) hz) hx
      have h1 := X.mul_mem (X.mul_mem hx ((hsX _ hz').2)) (X.inv_mem hx)
      have e : x * (s⁻¹ * (x⁻¹ * z * x) * s) * x⁻¹ = (x * s * x⁻¹)⁻¹ * z * (x * s * x⁻¹) := by
        group
      rw [e] at h1
      exact h1
    · have hz' : x⁻¹ * z * x ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hx) hz) hx
      have h1 := hsM _ hz'
      have h2 := hMn x hx _ h1
      have e : x * ((x⁻¹ * z * x)⁻¹ * (s * (x⁻¹ * z * x) * s⁻¹)) * x⁻¹ =
          z⁻¹ * (x * s * x⁻¹ * z * (x * s * x⁻¹)⁻¹) := by group
      rwa [e] at h2
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact fun hs => key x hx s hs
  · intro hs
    have h1 := key x⁻¹ (X.inv_mem hx) _ hs
    simpa [mul_assoc] using h1

variable [Finite G]

theorem exists_ne_one_mem_of_card_lt {B T Z : Subgroup G}
    (hTZ : T ≤ Subgroup.normalizer (Z : Set G)) (h : ∀ y ∈ B, ∃ t ∈ T, y * t ∈ Z)
    (hcard : Nat.card T < Nat.card B * Nat.card ↥(T ⊓ Z)) : ∃ y ∈ B, y ≠ 1 ∧ y ∈ Z := by
  classical
  choose! τ hτT hτZ using h
  let H : Subgroup ↥T := (T ⊓ Z).subgroupOf T
  let f : ↥B → ↥T ⧸ H := fun y => QuotientGroup.mk ⟨(τ y)⁻¹, T.inv_mem (hτT y y.2)⟩
  have hcardq : Nat.card (↥T ⧸ H) < Nat.card B := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup H
    have h2 : Nat.card H = Nat.card ↥(T ⊓ Z) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h2] at h1
    have hc : 0 < Nat.card ↥(T ⊓ Z) := Nat.card_pos
    by_contra hge
    push Not at hge
    have h3 : Nat.card B * Nat.card ↥(T ⊓ Z) ≤ Nat.card T := by
      rw [h1]
      exact Nat.mul_le_mul_right _ hge
    omega
  have hnotinj : ¬ Function.Injective f := fun hinj =>
    absurd (Nat.card_le_card_of_injective f hinj) (not_le.2 hcardq)
  obtain ⟨y₁, y₂, hfeq, hne⟩ : ∃ y₁ y₂, f y₁ = f y₂ ∧ y₁ ≠ y₂ := by
    unfold Function.Injective at hnotinj
    push Not at hnotinj
    exact hnotinj
  have hcls := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hfeq)
  have hcls' : τ y₁ * (τ y₂)⁻¹ ∈ Z := by
    have := hcls.2
    simpa using this
  set t₁ := τ y₁ with ht₁
  set t₂ := τ y₂ with ht₂
  have hs₁ : (y₁ : G) * t₁ ∈ Z := hτZ y₁ y₁.2
  have hs₂ : (y₂ : G) * t₂ ∈ Z := hτZ y₂ y₂.2
  have hT₁ : t₁ ∈ T := hτT y₁ y₁.2
  have hconj : t₁ * ((y₁ : G) * t₁)⁻¹ * ((y₂ : G) * t₂) * t₁⁻¹ ∈ Z := by
    have h1 := Z.mul_mem (Z.inv_mem hs₁) hs₂
    have h2 := (Subgroup.mem_normalizer_iff.1 (hTZ hT₁) _).1 h1
    have e : t₁ * (((y₁ : G) * t₁)⁻¹ * ((y₂ : G) * t₂)) * t₁⁻¹ =
        t₁ * ((y₁ : G) * t₁)⁻¹ * ((y₂ : G) * t₂) * t₁⁻¹ := by group
    rwa [e] at h2
  refine ⟨(y₁ : G)⁻¹ * y₂, B.mul_mem (B.inv_mem y₁.2) y₂.2, ?_, ?_⟩
  · intro h1
    exact hne (Subtype.ext (inv_mul_eq_one.1 h1))
  · have h3 := Z.mul_mem hconj hcls'
    have e : t₁ * ((y₁ : G) * t₁)⁻¹ * ((y₂ : G) * t₂) * t₁⁻¹ * (t₁ * t₂⁻¹) =
        (y₁ : G)⁻¹ * y₂ := by group
    rwa [e] at h3

end CFSG.CGT.Timmesfeld75
