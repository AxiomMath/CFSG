module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools

theorem card_eq_card_fiber_mul_ncard_image {G M : Type*} [Group G] [Finite G] [Group M]
    (K : Subgroup G) (f : G → M) (hf : ∀ x ∈ K, ∀ y ∈ K, f (x * y) = f x * f y) :
    Nat.card K = Nat.card {x : G // x ∈ K ∧ f x = 1} * (f '' (K : Set G)).ncard := by
  let φ : K →* M := MonoidHom.mk' (fun x : K => f x) (fun x y => hf x x.2 y y.2)
  have h := Subgroup.card_ker_mul_card_range φ
  have hker : Nat.card φ.ker = Nat.card {x : G // x ∈ K ∧ f x = 1} :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have hrange : (φ.range : Set M) = f '' (K : Set G) := by
    ext m
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hrange' : Nat.card φ.range = (f '' (K : Set G)).ncard := by
    rw [← hrange]
    exact Nat.card_coe_set_eq _
  rw [← h, hker, hrange']

theorem card_le_mul_of_partial_hom {G M : Type*} [Group G] [Finite G] [Group M]
    (K : Subgroup G) (f : G → M) (hf : ∀ x ∈ K, ∀ y ∈ K, f (x * y) = f x * f y) {a b : ℕ}
    (hker : Nat.card {x : G // x ∈ K ∧ f x = 1} ≤ a) (him : (f '' (K : Set G)).ncard ≤ b) :
    Nat.card K ≤ a * b := by
  rw [card_eq_card_fiber_mul_ncard_image K f hf]
  exact Nat.mul_le_mul hker him

theorem le_card_fiber_of_partial_hom {G M : Type*} [Group G] [Finite G] [Group M]
    (K : Subgroup G) (f : G → M) (hf : ∀ x ∈ K, ∀ y ∈ K, f (x * y) = f x * f y) {a b : ℕ}
    (hK : a ≤ Nat.card K) (him : (f '' (K : Set G)).ncard ≤ b) :
    a ≤ Nat.card {x : G // x ∈ K ∧ f x = 1} * b := by
  have h := card_eq_card_fiber_mul_ncard_image K f hf
  calc a ≤ Nat.card K := hK
    _ = Nat.card {x : G // x ∈ K ∧ f x = 1} * (f '' (K : Set G)).ncard := h
    _ ≤ Nat.card {x : G // x ∈ K ∧ f x = 1} * b := Nat.mul_le_mul le_rfl him

theorem exists_conj_le_of_isSylowOf {G : Type*} [Group G] [Finite G] {P K R : Subgroup G}
    (hP : IsSylowOf 2 P K) (hR : IsPGroup 2 R) (hRK : R ≤ K) :
    ∃ c ∈ K, ∀ x ∈ R, c * x * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP'⟩ := hP.exists_sylow_eq_subgroupOf
  have hR' : IsPGroup 2 (R.subgroupOf K) := hR.comap_subtype
  obtain ⟨Q', hQ'⟩ := hR'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K Q' P'
  refine ⟨(c : G), c.2, fun x hx => ?_⟩
  have hxK : x ∈ K := hRK hx
  have hmemQ : (⟨x, hxK⟩ : K) ∈ (Q' : Subgroup K) := hQ' hx
  have hmem : MulAut.conj c ⟨x, hxK⟩ ∈ ((c • Q' : Sylow 2 K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hmemQ
  rw [hc, hP'] at hmem
  exact hmem

theorem card_le_of_isSylowOf_of_le {G : Type*} [Group G] [Finite G] {P K R : Subgroup G}
    (hP : IsSylowOf 2 P K) (hR : IsPGroup 2 R) (hRK : R ≤ K) : Nat.card R ≤ Nat.card P := by
  obtain ⟨c, -, hcP⟩ := exists_conj_le_of_isSylowOf hP hR hRK
  have hle : R.map (MulAut.conj c).toMonoidHom ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcP x hx
  calc Nat.card R = Nat.card (R.map (MulAut.conj c).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj c).injective).symm
    _ ≤ Nat.card P := Subgroup.card_le_of_le hle

theorem mem_map_conj_iff {G : Type*} [Group G] (E : Subgroup G) (g x : G) :
    x ∈ E.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem card_map_conj {G : Type*} [Group G] (E : Subgroup G) (g : G) :
    Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isElemAbelian_map_conj {G : Type*} [Group G] {E : Subgroup G}
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) (g : G) :
    (∀ x ∈ E.map (MulAut.conj g).toMonoidHom, ∀ y ∈ E.map (MulAut.conj g).toMonoidHom,
        x * y = y * x) ∧
      ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, x * x = 1 := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hab x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hsq x hx, map_one]

theorem exists_complement_of_elem {G : Type*} [Group G] [Finite G] {K W' : Subgroup G}
    (hab : ∀ x ∈ W', ∀ y ∈ W', x * y = y * x) (hsq : ∀ x ∈ W', x * x = 1) :
    ∃ Y : Subgroup G, Y ≤ W' ∧ Y ⊓ K = ⊥ ∧ ∀ w ∈ W', ∃ z ∈ K, ∃ y ∈ Y, w = z * y := by
  have hS : ({Y : Subgroup G | Y ≤ W' ∧ Y ⊓ K = ⊥} : Set (Subgroup G)).Nonempty :=
    ⟨⊥, bot_le, bot_inf_eq _⟩
  obtain ⟨Y, ⟨hYW, hYK⟩, hmax⟩ := Set.Finite.exists_maximal (Set.toFinite _) hS
  refine ⟨Y, hYW, hYK, fun w hw => ?_⟩
  by_contra hcon'
  have hcon : ∀ z ∈ K, ∀ y ∈ Y, w ≠ z * y := fun z hz y hy h => hcon' ⟨z, hz, y, hy, h⟩
  have hinv : ∀ x ∈ W', x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hsq x hx)
  let Y' : Subgroup G :=
    { carrier := {x | x ∈ Y ∨ ∃ y ∈ Y, x = w * y}
      mul_mem' := by
        rintro a b (ha | ⟨y, hy, rfl⟩) (hb | ⟨y', hy', rfl⟩)
        · exact Or.inl (Y.mul_mem ha hb)
        · refine Or.inr ⟨a * y', Y.mul_mem ha hy', ?_⟩
          calc a * (w * y') = (a * w) * y' := by rw [mul_assoc]
            _ = (w * a) * y' := by rw [hab a (hYW ha) w hw]
            _ = w * (a * y') := by rw [mul_assoc]
        · exact Or.inr ⟨y * b, Y.mul_mem hy hb, mul_assoc _ _ _⟩
        · refine Or.inl ?_
          have : w * y * (w * y') = y * y' := by
            calc w * y * (w * y') = w * (y * w) * y' := by simp only [mul_assoc]
              _ = w * (w * y) * y' := by rw [hab y (hYW hy) w hw]
              _ = (w * w) * y * y' := by simp only [mul_assoc]
              _ = y * y' := by rw [hsq w hw, one_mul]
          rw [this]
          exact Y.mul_mem hy hy'
      one_mem' := Or.inl Y.one_mem
      inv_mem' := by
        rintro a (ha | ⟨y, hy, rfl⟩)
        · exact Or.inl (Y.inv_mem ha)
        · refine Or.inr ⟨y⁻¹, Y.inv_mem hy, ?_⟩
          rw [mul_inv_rev, hinv w hw]
          exact hab _ (W'.inv_mem (hYW hy)) w hw }
  have hwY' : w ∈ Y' := Or.inr ⟨1, Y.one_mem, (mul_one w).symm⟩
  have hYY' : Y ≤ Y' := fun y hy => Or.inl hy
  have hY'W : Y' ≤ W' := by
    rintro a (ha | ⟨y, hy, rfl⟩)
    · exact hYW ha
    · exact W'.mul_mem hw (hYW hy)
  have hY'K : Y' ⊓ K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hx | ⟨y, hy, rfl⟩, hxK⟩
    · have : x ∈ Y ⊓ K := ⟨hx, hxK⟩
      rw [hYK] at this
      exact this
    · exact absurd (eq_mul_inv_of_mul_eq rfl) (hcon _ hxK y⁻¹ (Y.inv_mem hy))
  have hle := hmax ⟨hY'W, hY'K⟩ hYY'
  exact hcon 1 K.one_mem w (hle hwY') (one_mul w).symm

end CFSG.OddStandard.Seitz77
