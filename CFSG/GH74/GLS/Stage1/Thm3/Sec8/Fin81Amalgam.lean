module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

open Subgroup

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

theorem amalgam_mulEquiv {X X' : Type*} [Group X] [Group X'] (K T : Subgroup X)
    (K' T' : Subgroup X') (hTK : T ≤ normalizer (K : Set X)) (hTK' : T' ≤ normalizer (K' : Set X'))
    (φ : ↥K ≃* ↥K') (α : ↥T ≃* ↥T')
    (hφα : ∀ (k : ↥K) (t : ↥T), (k : X) = (t : X) → ((φ k : ↥K') : X') = ((α t : ↥T') : X'))
    (hinj : ∀ k : ↥K, ((φ k : ↥K') : X') ∈ T' → (k : X) ∈ T)
    (hact : ∀ (t : ↥T) (k : ↥K) (hk : (t : X) * (k : X) * (t : X)⁻¹ ∈ K),
      ((φ ⟨(t : X) * (k : X) * (t : X)⁻¹, hk⟩ : ↥K') : X') =
        ((α t : ↥T') : X') * ((φ k : ↥K') : X') * ((α t : ↥T') : X')⁻¹) :
    ∃ Ψ : ↥(K ⊔ T) ≃* ↥(K' ⊔ T'),
      (∀ k : ↥K, ((Ψ ⟨(k : X), Subgroup.mem_sup_left k.2⟩ : ↥(K' ⊔ T')) : X') = ((φ k : ↥K') : X')) ∧
      (∀ t : ↥T, ((Ψ ⟨(t : X), Subgroup.mem_sup_right t.2⟩ : ↥(K' ⊔ T')) : X') = ((α t : ↥T') : X')) := by
  classical
  have hdec : ∀ x : ↥(K ⊔ T), ∃ (k : ↥K) (t : ↥T), (k : X) * (t : X) = (x : X) := by
    intro x
    have hx : (x : X) ∈ (↑(K ⊔ T) : Set X) := x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K T hTK] at hx
    obtain ⟨k, hk, t, ht, h⟩ := hx
    exact ⟨⟨k, hk⟩, ⟨t, ht⟩, h⟩
  have hdec' : ∀ x : ↥(K' ⊔ T'), ∃ (k : ↥K') (t : ↥T'), (k : X') * (t : X') = (x : X') := by
    intro x
    have hx : (x : X') ∈ (↑(K' ⊔ T') : Set X') := x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K' T' hTK'] at hx
    obtain ⟨k, hk, t, ht, h⟩ := hx
    exact ⟨⟨k, hk⟩, ⟨t, ht⟩, h⟩
  have key : ∀ (k₁ k₂ : ↥K) (t₁ t₂ : ↥T), (k₁ : X) * (t₁ : X) = (k₂ : X) * (t₂ : X) →
      ((φ k₁ : ↥K') : X') * ((α t₁ : ↥T') : X') = ((φ k₂ : ↥K') : X') * ((α t₂ : ↥T') : X') := by
    intro k₁ k₂ t₁ t₂ h
    have hp : ((k₂⁻¹ * k₁ : ↥K) : X) = ((t₂ * t₁⁻¹ : ↥T) : X) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (k₂ : X)⁻¹ * k₁ = (k₂ : X)⁻¹ * ((k₁ : X) * (t₁ : X)) * (t₁ : X)⁻¹ := by group
        _ = (k₂ : X)⁻¹ * ((k₂ : X) * (t₂ : X)) * (t₁ : X)⁻¹ := by rw [h]
        _ = (t₂ : X) * (t₁ : X)⁻¹ := by group
    have h1 := hφα _ _ hp
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc ((φ k₁ : ↥K') : X') * ((α t₁ : ↥T') : X')
        = ((φ k₂ : ↥K') : X') * (((φ k₂ : ↥K') : X')⁻¹ * ((φ k₁ : ↥K') : X')) * ((α t₁ : ↥T') : X') := by group
      _ = ((φ k₂ : ↥K') : X') * (((α t₂ : ↥T') : X') * ((α t₁ : ↥T') : X')⁻¹) * ((α t₁ : ↥T') : X') := by rw [h1]
      _ = ((φ k₂ : ↥K') : X') * ((α t₂ : ↥T') : X') := by group
  choose kf tf hkt using hdec
  let f : ↥(K ⊔ T) → ↥(K' ⊔ T') := fun x => ⟨((φ (kf x) : ↥K') : X') * ((α (tf x) : ↥T') : X'),
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (φ (kf x)).2) (Subgroup.mem_sup_right (α (tf x)).2)⟩
  have hf_dec : ∀ (k : ↥K) (t : ↥T) (hx : (k : X) * (t : X) ∈ K ⊔ T),
      ((f ⟨(k : X) * (t : X), hx⟩ : ↥(K' ⊔ T')) : X') = ((φ k : ↥K') : X') * ((α t : ↥T') : X') := by
    intro k t hx
    exact key _ _ _ _ (hkt ⟨(k : X) * (t : X), hx⟩)
  have hmul : ∀ x y : ↥(K ⊔ T), f (x * y) = f x * f y := by
    intro x y
    apply Subtype.ext
    have hxy : (tf x : X) * (kf y : X) * (tf x : X)⁻¹ ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (hTK (tf x).2) (kf y)).1 (kf y).2
      exact this
    have e : ((x * y : ↥(K ⊔ T)) : X) = ((kf x : X) * ((tf x : X) * (kf y : X) * (tf x : X)⁻¹)) * ((tf x : X) * (tf y : X)) := by
      have hx := hkt x
      have hy := hkt y
      calc ((x : X)) * (y : X) = ((kf x : X) * (tf x : X)) * ((kf y : X) * (tf y : X)) := by rw [hx, hy]
        _ = _ := by group
    have hmemz : (((kf x * (⟨(tf x : X) * (kf y : X) * (tf x : X)⁻¹, hxy⟩ : ↥K) : ↥K) : X)) *
        ((tf x * tf y : ↥T) : X) ∈ K ⊔ T :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (kf x * (⟨(tf x : X) * (kf y : X) * (tf x : X)⁻¹, hxy⟩ : ↥K) : ↥K).2)
        (Subgroup.mem_sup_right (tf x * tf y).2)
    have e2 : x * y = ⟨_, hmemz⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      simp only [Subgroup.coe_mul] at e
      exact e
    rw [e2, hf_dec]
    have h2 := hact (tf x) (kf y) hxy
    simp only [map_mul, Subgroup.coe_mul]
    rw [h2]
    show _ = (((φ (kf x) : ↥K') : X') * ((α (tf x) : ↥T') : X')) * (((φ (kf y) : ↥K') : X') * ((α (tf y) : ↥T') : X'))
    group
  let F : ↥(K ⊔ T) →* ↥(K' ⊔ T') := MonoidHom.mk' f hmul
  have hF : ∀ (k : ↥K) (t : ↥T) (hx : (k : X) * (t : X) ∈ K ⊔ T),
      ((F ⟨(k : X) * (t : X), hx⟩ : ↥(K' ⊔ T')) : X') = ((φ k : ↥K') : X') * ((α t : ↥T') : X') := hf_dec
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨k, t, hkt'⟩ : ∃ (k : ↥K) (t : ↥T), (k : X) * (t : X) = (x : X) := ⟨kf x, tf x, hkt x⟩
    have hxe : x = ⟨(k : X) * (t : X), by rw [hkt']; exact x.2⟩ := Subtype.ext hkt'.symm
    have hx' : ((F x : ↥(K' ⊔ T')) : X') = 1 := by rw [hx]; rfl
    rw [hxe, hF] at hx'
    have h1 : ((φ k : ↥K') : X') = (((α t : ↥T') : X'))⁻¹ := eq_inv_of_mul_eq_one_left hx'
    have h2 : ((φ k : ↥K') : X') ∈ T' := by rw [h1]; exact T'.inv_mem (α t).2
    have h3 : (k : X) ∈ T := hinj k h2
    have h4 := hφα k ⟨(k : X), h3⟩ rfl
    have h5 : α ⟨(k : X), h3⟩ = (α t)⁻¹ := by
      apply Subtype.ext
      rw [← h4, h1]
      simp
    have h6 : (⟨(k : X), h3⟩ : ↥T) = t⁻¹ := by
      apply α.injective
      rw [h5, map_inv]
    have h7 : (k : X) = ((t⁻¹ : ↥T) : X) := congrArg Subtype.val h6
    apply Subtype.ext
    rw [hxe]
    simp only [Subgroup.coe_one]
    rw [h7]
    simp
  have hFsurj : Function.Surjective F := by
    intro x'
    obtain ⟨k', t', hk't'⟩ := hdec' x'
    have hmem : ((φ.symm k' : ↥K) : X) * ((α.symm t' : ↥T) : X) ∈ K ⊔ T :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (φ.symm k').2) (Subgroup.mem_sup_right (α.symm t').2)
    refine ⟨⟨((φ.symm k' : ↥K) : X) * ((α.symm t' : ↥T) : X), hmem⟩, ?_⟩
    apply Subtype.ext
    rw [hF]
    simp [hk't']
  refine ⟨MulEquiv.ofBijective F ⟨hFinj, hFsurj⟩, fun k => ?_, fun t => ?_⟩
  · have hk : (k : X) * ((1 : ↥T) : X) ∈ K ⊔ T := by
      simpa using Subgroup.mem_sup_left k.2
    have e : (⟨(k : X), Subgroup.mem_sup_left k.2⟩ : ↥(K ⊔ T)) = ⟨(k : X) * ((1 : ↥T) : X), hk⟩ :=
      Subtype.ext (by simp)
    show ((F ⟨(k : X), Subgroup.mem_sup_left k.2⟩ : ↥(K' ⊔ T')) : X') = _
    rw [e, hF]
    simp
  · have ht : ((1 : ↥K) : X) * (t : X) ∈ K ⊔ T := by
      simpa using Subgroup.mem_sup_right t.2
    have e : (⟨(t : X), Subgroup.mem_sup_right t.2⟩ : ↥(K ⊔ T)) = ⟨((1 : ↥K) : X) * (t : X), ht⟩ :=
      Subtype.ext (by simp)
    show ((F ⟨(t : X), Subgroup.mem_sup_right t.2⟩ : ↥(K' ⊔ T')) : X') = _
    rw [e, hF]
    simp

theorem mem_sup_of_commute_aux {X : Type*} [Group X] {A₁ A₂ : Subgroup X}
    (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) {x : X} (hx : x ∈ A₁ ⊔ A₂) :
    ∃ (a : ↥A₁) (b : ↥A₂), (a : X) * (b : X) = x := by
  let P : Subgroup X :=
    { carrier := {x | ∃ (a : ↥A₁) (b : ↥A₂), (a : X) * (b : X) = x}
      mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
        refine ⟨a * a', b * b', ?_⟩
        have h := hc a' a'.2 b b.2
        simp only [Subgroup.coe_mul]
        calc (a : X) * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [h]
          _ = a * b * (a' * b') := by group
      one_mem' := ⟨1, 1, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        refine ⟨a⁻¹, b⁻¹, ?_⟩
        have h := hc a a.2 b b.2
        simp only [Subgroup.coe_inv, mul_inv_rev]
        have h' : (b : X)⁻¹ * (a : X)⁻¹ = (a : X)⁻¹ * (b : X)⁻¹ := by
          calc (b : X)⁻¹ * (a : X)⁻¹ = ((a : X) * b)⁻¹ := by group
            _ = ((b : X) * a)⁻¹ := by rw [h]
            _ = (a : X)⁻¹ * (b : X)⁻¹ := by group
        exact h'.symm }
  have hle : A₁ ⊔ A₂ ≤ P := by
    refine sup_le (fun a ha => ⟨⟨a, ha⟩, 1, by simp⟩) (fun b hb => ⟨1, ⟨b, hb⟩, by simp⟩)
  exact hle hx

theorem centralProduct_mulEquiv {X X' : Type*} [Group X] [Group X'] (A₁ A₂ : Subgroup X)
    (A₁' A₂' : Subgroup X') (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hc' : ∀ a ∈ A₁', ∀ b ∈ A₂', a * b = b * a)
    (φ₁ : ↥A₁ ≃* ↥A₁') (φ₂ : ↥A₂ ≃* ↥A₂')
    (hZ : ∀ (a : ↥A₁) (b : ↥A₂), (a : X) = (b : X) → ((φ₁ a : ↥A₁') : X') = ((φ₂ b : ↥A₂') : X'))
    (hZ' : ∀ (a : ↥A₁) (b : ↥A₂), ((φ₁ a : ↥A₁') : X') = ((φ₂ b : ↥A₂') : X') → (a : X) = (b : X)) :
    ∃ φ : ↥(A₁ ⊔ A₂) ≃* ↥(A₁' ⊔ A₂'),
      (∀ a : ↥A₁, ((φ ⟨(a : X), Subgroup.mem_sup_left a.2⟩ : ↥(A₁' ⊔ A₂')) : X') = ((φ₁ a : ↥A₁') : X')) ∧
      (∀ b : ↥A₂, ((φ ⟨(b : X), Subgroup.mem_sup_right b.2⟩ : ↥(A₁' ⊔ A₂')) : X') = ((φ₂ b : ↥A₂') : X')) := by
  classical
  have hdec : ∀ x : ↥(A₁ ⊔ A₂), ∃ (a : ↥A₁) (b : ↥A₂), (a : X) * (b : X) = (x : X) :=
    fun x => mem_sup_of_commute_aux hc x.2
  have hdec' : ∀ x : ↥(A₁' ⊔ A₂'), ∃ (a : ↥A₁') (b : ↥A₂'), (a : X') * (b : X') = (x : X') :=
    fun x => mem_sup_of_commute_aux hc' x.2
  have key : ∀ (a₁ a₂ : ↥A₁) (b₁ b₂ : ↥A₂), (a₁ : X) * (b₁ : X) = (a₂ : X) * (b₂ : X) →
      ((φ₁ a₁ : ↥A₁') : X') * ((φ₂ b₁ : ↥A₂') : X') = ((φ₁ a₂ : ↥A₁') : X') * ((φ₂ b₂ : ↥A₂') : X') := by
    intro a₁ a₂ b₁ b₂ h
    have hp : ((a₂⁻¹ * a₁ : ↥A₁) : X) = ((b₂ * b₁⁻¹ : ↥A₂) : X) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (a₂ : X)⁻¹ * a₁ = (a₂ : X)⁻¹ * ((a₁ : X) * (b₁ : X)) * (b₁ : X)⁻¹ := by group
        _ = (a₂ : X)⁻¹ * ((a₂ : X) * (b₂ : X)) * (b₁ : X)⁻¹ := by rw [h]
        _ = (b₂ : X) * (b₁ : X)⁻¹ := by group
    have h1 := hZ _ _ hp
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc ((φ₁ a₁ : ↥A₁') : X') * ((φ₂ b₁ : ↥A₂') : X')
        = ((φ₁ a₂ : ↥A₁') : X') * (((φ₁ a₂ : ↥A₁') : X')⁻¹ * ((φ₁ a₁ : ↥A₁') : X')) * ((φ₂ b₁ : ↥A₂') : X') := by group
      _ = ((φ₁ a₂ : ↥A₁') : X') * (((φ₂ b₂ : ↥A₂') : X') * ((φ₂ b₁ : ↥A₂') : X')⁻¹) * ((φ₂ b₁ : ↥A₂') : X') := by rw [h1]
      _ = ((φ₁ a₂ : ↥A₁') : X') * ((φ₂ b₂ : ↥A₂') : X') := by group
  choose af bf hab using hdec
  let f : ↥(A₁ ⊔ A₂) → ↥(A₁' ⊔ A₂') := fun x => ⟨((φ₁ (af x) : ↥A₁') : X') * ((φ₂ (bf x) : ↥A₂') : X'),
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (φ₁ (af x)).2) (Subgroup.mem_sup_right (φ₂ (bf x)).2)⟩
  have hf_dec : ∀ (a : ↥A₁) (b : ↥A₂) (hx : (a : X) * (b : X) ∈ A₁ ⊔ A₂),
      ((f ⟨(a : X) * (b : X), hx⟩ : ↥(A₁' ⊔ A₂')) : X') = ((φ₁ a : ↥A₁') : X') * ((φ₂ b : ↥A₂') : X') := by
    intro a b hx
    exact key _ _ _ _ (hab ⟨(a : X) * (b : X), hx⟩)
  have hmul : ∀ x y : ↥(A₁ ⊔ A₂), f (x * y) = f x * f y := by
    intro x y
    apply Subtype.ext
    have e : ((x * y : ↥(A₁ ⊔ A₂)) : X) = ((af x * af y : ↥A₁) : X) * ((bf x * bf y : ↥A₂) : X) := by
      have hx := hab x
      have hy := hab y
      have h := hc (af y) (af y).2 (bf x) (bf x).2
      simp only [Subgroup.coe_mul]
      calc ((x : X)) * (y : X) = ((af x : X) * (bf x : X)) * ((af y : X) * (bf y : X)) := by rw [hx, hy]
        _ = (af x : X) * ((af y : X) * (bf x : X)) * (bf y : X) := by
              calc _ = (af x : X) * ((bf x : X) * (af y : X)) * (bf y : X) := by group
                _ = _ := by rw [← h]
        _ = ((af x : X) * (af y : X)) * ((bf x : X) * (bf y : X)) := by group
    have e2 : x * y = (⟨((af x * af y : ↥A₁) : X) * ((bf x * bf y : ↥A₂) : X), by rw [← e]; exact (x * y).2⟩ : ↥(A₁ ⊔ A₂)) :=
      Subtype.ext e
    rw [e2, hf_dec]
    have h' := hc' (φ₁ (af y)).1 (φ₁ (af y)).2 (φ₂ (bf x)).1 (φ₂ (bf x)).2
    simp only [map_mul, Subgroup.coe_mul]
    show _ = (((φ₁ (af x) : ↥A₁') : X') * ((φ₂ (bf x) : ↥A₂') : X')) * (((φ₁ (af y) : ↥A₁') : X') * ((φ₂ (bf y) : ↥A₂') : X'))
    calc ((φ₁ (af x) : ↥A₁') : X') * (φ₁ (af y) : X') * ((φ₂ (bf x) : X') * (φ₂ (bf y) : X'))
        = (φ₁ (af x) : X') * ((φ₁ (af y) : X') * (φ₂ (bf x) : X')) * (φ₂ (bf y) : X') := by group
      _ = (φ₁ (af x) : X') * ((φ₂ (bf x) : X') * (φ₁ (af y) : X')) * (φ₂ (bf y) : X') := by rw [h']
      _ = _ := by group
  let F : ↥(A₁ ⊔ A₂) →* ↥(A₁' ⊔ A₂') := MonoidHom.mk' f hmul
  have hF : ∀ (a : ↥A₁) (b : ↥A₂) (hx : (a : X) * (b : X) ∈ A₁ ⊔ A₂),
      ((F ⟨(a : X) * (b : X), hx⟩ : ↥(A₁' ⊔ A₂')) : X') = ((φ₁ a : ↥A₁') : X') * ((φ₂ b : ↥A₂') : X') := hf_dec
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨a, b, hab'⟩ : ∃ (a : ↥A₁) (b : ↥A₂), (a : X) * (b : X) = (x : X) := ⟨af x, bf x, hab x⟩
    have hx' : ((F x : ↥(A₁' ⊔ A₂')) : X') = 1 := by rw [hx]; rfl
    have hxe : x = ⟨(a : X) * (b : X), by rw [hab']; exact x.2⟩ := Subtype.ext hab'.symm
    rw [hxe, hF] at hx'
    have h1 : ((φ₁ a : ↥A₁') : X') = (((φ₂ b : ↥A₂') : X'))⁻¹ := eq_inv_of_mul_eq_one_left hx'
    have h2 : ((φ₁ a : ↥A₁') : X') = ((φ₂ b⁻¹ : ↥A₂') : X') := by rw [h1]; simp
    have h3 := hZ' a b⁻¹ h2
    apply Subtype.ext
    rw [← hab']
    simp only [Subgroup.coe_inv] at h3
    rw [h3]
    simp
  have hFsurj : Function.Surjective F := by
    intro x'
    obtain ⟨a', b', hab''⟩ := hdec' x'
    refine ⟨⟨((φ₁.symm a' : ↥A₁) : X) * ((φ₂.symm b' : ↥A₂) : X),
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (φ₁.symm a').2) (Subgroup.mem_sup_right (φ₂.symm b').2)⟩, ?_⟩
    apply Subtype.ext
    rw [hF]
    simp [hab'']
  refine ⟨MulEquiv.ofBijective F ⟨hFinj, hFsurj⟩, fun a => ?_, fun b => ?_⟩
  · have h := hF a 1 (by simpa using Subgroup.mem_sup_left a.2)
    simp only [Subgroup.coe_one, mul_one, map_one] at h
    exact h
  · have h := hF 1 b (by simpa using Subgroup.mem_sup_right b.2)
    simp only [Subgroup.coe_one, one_mul, map_one] at h
    exact h

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
