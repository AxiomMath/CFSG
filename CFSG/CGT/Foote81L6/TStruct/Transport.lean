module

public import CFSG.CGT.Foote81L6.TStruct.ElemBound

public section

namespace CFSG.CGT.Foote81L6.TStruct

open Subgroup

variable {G : Type*} [Group G]

section Transport

variable {H : Subgroup G} {K : Type*} [Group K] (e : H ≃* K)

@[expose] def liftSub (V : Subgroup K) : Subgroup G :=
  (V.map e.symm.toMonoidHom).map H.subtype

@[expose] def lowerSub (V : Subgroup G) : Subgroup K :=
  (V.subgroupOf H).map e.toMonoidHom

theorem mem_liftSub {V : Subgroup K} {x : G} : x ∈ liftSub e V ↔ ∃ hx : x ∈ H, e ⟨x, hx⟩ ∈ V := by
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨(e.symm v).2, by simpa using hv⟩
  · rintro ⟨hx, hv⟩
    exact ⟨⟨x, hx⟩, ⟨e ⟨x, hx⟩, hv, by simp⟩, rfl⟩

theorem coe_mem_liftSub {V : Subgroup K} {y : H} : (y : G) ∈ liftSub e V ↔ e y ∈ V := by
  rw [mem_liftSub]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨y.2, h⟩⟩

theorem symm_mem_liftSub {V : Subgroup K} {k : K} : ((e.symm k : H) : G) ∈ liftSub e V ↔ k ∈ V := by
  rw [coe_mem_liftSub, MulEquiv.apply_symm_apply]

theorem mem_lowerSub {V : Subgroup G} {k : K} : k ∈ lowerSub e V ↔ ((e.symm k : H) : G) ∈ V := by
  rw [lowerSub, mem_map_equiv, mem_subgroupOf]

theorem liftSub_le (V : Subgroup K) : liftSub e V ≤ H := map_subtype_le _

theorem card_liftSub (V : Subgroup K) : Nat.card ↥(liftSub e V) = Nat.card V := by
  rw [liftSub, card_map_of_injective H.subtype_injective, card_map_of_injective e.symm.injective]

theorem card_lowerSub {V : Subgroup G} (hV : V ≤ H) : Nat.card ↥(lowerSub e V) = Nat.card V := by
  rw [lowerSub, card_map_of_injective e.injective, Nat.card_congr (subgroupOfEquivOfLe hV).toEquiv]

theorem liftSub_lowerSub {V : Subgroup G} (hV : V ≤ H) : liftSub e (lowerSub e V) = V := by
  ext x
  rw [mem_liftSub]
  constructor
  · rintro ⟨hx, h⟩
    rw [mem_lowerSub, MulEquiv.symm_apply_apply] at h
    exact h
  · intro hx
    refine ⟨hV hx, ?_⟩
    rw [mem_lowerSub, MulEquiv.symm_apply_apply]
    exact hx

theorem lowerSub_liftSub (V : Subgroup K) : lowerSub e (liftSub e V) = V := by
  ext k
  rw [mem_lowerSub, symm_mem_liftSub]

theorem liftSub_inj {V V' : Subgroup K} : liftSub e V = liftSub e V' ↔ V = V' := by
  constructor
  · intro h
    rw [← lowerSub_liftSub e V, h, lowerSub_liftSub]
  · rintro rfl
    rfl

theorem mul_self_liftSub {V : Subgroup K} (hV : ∀ x ∈ V, x * x = 1) :
    ∀ x ∈ liftSub e V, x * x = 1 := by
  rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul, hV v hv, map_one, map_one]

theorem mul_self_lowerSub {V : Subgroup G} (hV : ∀ x ∈ V, x * x = 1) :
    ∀ x ∈ lowerSub e V, x * x = 1 := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, show y * y = 1 from Subtype.ext (hV _ hy), map_one]

theorem liftSub_map_conj (V : Subgroup K) (h : H) :
    (liftSub e V).map (MulAut.conj (h : G)).toMonoidHom =
      liftSub e (V.map (MulAut.conj (e h)).toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyH, hyV⟩ := (mem_liftSub e).1 hy
    rw [mem_liftSub]
    refine ⟨mul_mem (mul_mem h.2 hyH) (inv_mem h.2), ⟨e ⟨y, hyH⟩, hyV, ?_⟩⟩
    have : (⟨(h : G) * y * (h : G)⁻¹, mul_mem (mul_mem h.2 hyH) (inv_mem h.2)⟩ : H) =
        h * ⟨y, hyH⟩ * h⁻¹ := rfl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    rw [this, map_mul, map_mul, map_inv]
  · intro hx
    obtain ⟨hxH, k, hk, hke⟩ := (mem_liftSub e).1 hx
    have hmem : (h : G)⁻¹ * x * h ∈ H := mul_mem (mul_mem (inv_mem h.2) hxH) h.2
    have key : e ⟨(h : G)⁻¹ * x * h, hmem⟩ ∈ V := by
      have : (⟨(h : G)⁻¹ * x * h, hmem⟩ : H) = h⁻¹ * ⟨x, hxH⟩ * h := rfl
      rw [this, map_mul, map_mul, map_inv, ← hke]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      simpa [mul_assoc] using hk
    exact ⟨(h : G)⁻¹ * x * h, (mem_liftSub e).2 ⟨hmem, key⟩, by simp [mul_assoc]⟩

theorem inf_normalizer_liftSub (V : Subgroup K) :
    H ⊓ normalizer (liftSub e V : Set G) = liftSub e (normalizer (V : Set K)) := by
  ext g
  rw [mem_inf, mem_liftSub]
  constructor
  · rintro ⟨hg, hgn⟩
    refine ⟨hg, mem_normalizer_iff.2 fun k => ?_⟩
    have h1 := (mem_normalizer_iff.1 hgn) ((e.symm k : H) : G)
    rw [symm_mem_liftSub] at h1
    rw [h1]
    have : (g : G) * ((e.symm k : H) : G) * g⁻¹ =
        ((⟨g, hg⟩ * e.symm k * ⟨g, hg⟩⁻¹ : H) : G) := rfl
    rw [this, coe_mem_liftSub, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · rintro ⟨hg, hgn⟩
    refine ⟨hg, mem_normalizer_iff.2 fun x => ?_⟩
    by_cases hx : x ∈ H
    · have h1 := (mem_normalizer_iff.1 hgn) (e ⟨x, hx⟩)
      have hx1 : x ∈ liftSub e V ↔ e ⟨x, hx⟩ ∈ V := coe_mem_liftSub e (y := ⟨x, hx⟩)
      have hx2 : g * x * g⁻¹ ∈ liftSub e V ↔ e (⟨g, hg⟩ * ⟨x, hx⟩ * ⟨g, hg⟩⁻¹) ∈ V :=
        coe_mem_liftSub e (y := ⟨g, hg⟩ * ⟨x, hx⟩ * ⟨g, hg⟩⁻¹)
      rw [hx1, hx2, map_mul, map_mul, map_inv]
      exact h1
    · have h1 : x ∉ liftSub e V := fun h => hx (liftSub_le e V h)
      have h2 : g * x * g⁻¹ ∉ liftSub e V := by
        intro h
        apply hx
        have h3 := liftSub_le e V h
        have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem hg) h3) hg
      exact iff_of_false h1 h2

theorem inf_centralizer_liftSub (V : Subgroup K) :
    H ⊓ centralizer (liftSub e V : Set G) = liftSub e (centralizer (V : Set K)) := by
  ext g
  rw [mem_inf, mem_liftSub]
  constructor
  · rintro ⟨hg, hgc⟩
    refine ⟨hg, mem_centralizer_iff.2 fun k hk => ?_⟩
    have h1 := (mem_centralizer_iff.1 hgc) ((e.symm k : H) : G) ((symm_mem_liftSub e).2 hk)
    have h2 : e.symm k * ⟨g, hg⟩ = ⟨g, hg⟩ * e.symm k := Subtype.ext h1
    have := congrArg e h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  · rintro ⟨hg, hgc⟩
    refine ⟨hg, mem_centralizer_iff.2 fun x hx => ?_⟩
    obtain ⟨hxH, hxV⟩ := (mem_liftSub e).1 hx
    have h1 := (mem_centralizer_iff.1 hgc) _ hxV
    have h2 : ⟨x, hxH⟩ * ⟨g, hg⟩ = (⟨g, hg⟩ * ⟨x, hxH⟩ : H) :=
      e.injective (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2

theorem lowerSub_normal {V : Subgroup G} (hn : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) :
    (lowerSub e V).Normal := by
  refine ⟨fun k hk c => ?_⟩
  rw [mem_lowerSub] at hk ⊢
  rw [map_mul, map_mul, map_inv]
  exact hn _ (e.symm c).2 _ hk

end Transport

theorem eq_sup_inf_of_card {H₁ H₂ E : Subgroup G} [Finite H₁] [Finite H₂] {k₁ k₂ : ℕ}
    (hc : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) (hd : H₁ ⊓ H₂ = ⊥) (h₁ : ElemBound H₁ k₁)
    (h₂ : ElemBound H₂ k₂) (hE : E ≤ H₁ ⊔ H₂) (hE2 : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card E = k₁ * k₂) :
    E = (E ⊓ H₁) ⊔ (E ⊓ H₂) ∧ Nat.card ↥(E ⊓ H₁) = k₁ ∧ Nat.card ↥(E ⊓ H₂) = k₂ := by
  have hdec : ∀ g ∈ H₁ ⊔ H₂, ∃ x ∈ H₁, ∃ y ∈ H₂, g = x * y := fun g hg =>
    (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc)).1 hg
  have hsq : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y ∈ E → x * x = 1 ∧ y * y = 1 := by
    intro x hx y hy hxy
    have h1 : (x * x) * (y * y) = 1 := by
      calc (x * x) * (y * y) = x * (x * y) * y := by group
        _ = x * (y * x) * y := by rw [hc x hx y hy]
        _ = (x * y) * (x * y) := by group
        _ = 1 := hE2 _ hxy
    exact (eq_and_eq_of_mul_eq_mul hd (mul_mem hx hx) (one_mem _) (mul_mem hy hy) (one_mem _)
      (h1.trans (mul_one 1).symm))
  let P₁ : Subgroup G :=
    { carrier := {x | x ∈ H₁ ∧ ∃ y ∈ H₂, x * y ∈ E}
      mul_mem' := by
        rintro x x' ⟨hx, y, hy, hxy⟩ ⟨hx', y', hy', hxy'⟩
        refine ⟨mul_mem hx hx', y * y', mul_mem hy hy', ?_⟩
        have := mul_mem hxy hxy'
        rwa [show x * y * (x' * y') = x * x' * (y * y') by
          rw [mul_assoc x y, ← mul_assoc y, ← hc x' hx' y hy]; group] at this
      one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro x ⟨hx, y, hy, hxy⟩
        refine ⟨inv_mem hx, y⁻¹, inv_mem hy, ?_⟩
        have := inv_mem hxy
        rwa [mul_inv_rev, ← hc _ (inv_mem hx) _ (inv_mem hy)] at this }
  let P₂ : Subgroup G :=
    { carrier := {y | y ∈ H₂ ∧ ∃ x ∈ H₁, x * y ∈ E}
      mul_mem' := by
        rintro y y' ⟨hy, x, hx, hxy⟩ ⟨hy', x', hx', hxy'⟩
        refine ⟨mul_mem hy hy', x * x', mul_mem hx hx', ?_⟩
        have := mul_mem hxy hxy'
        rwa [show x * y * (x' * y') = x * x' * (y * y') by
          rw [mul_assoc x y, ← mul_assoc y, ← hc x' hx' y hy]; group] at this
      one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro y ⟨hy, x, hx, hxy⟩
        refine ⟨inv_mem hy, x⁻¹, inv_mem hx, ?_⟩
        have := inv_mem hxy
        rwa [mul_inv_rev, ← hc _ (inv_mem hx) _ (inv_mem hy)] at this }
  have hP₁ : P₁ ≤ H₁ := fun x hx => hx.1
  have hP₂ : P₂ ≤ H₂ := fun y hy => hy.1
  haveI : Finite P₁ := Finite.of_injective _ (inclusion_injective hP₁)
  haveI : Finite P₂ := Finite.of_injective _ (inclusion_injective hP₂)
  have hc₁ : Nat.card P₁ ≤ k₁ := h₁ P₁ hP₁ fun x hx => by
    obtain ⟨hx, y, hy, hxy⟩ := hx
    exact (hsq x hx y hy hxy).1
  have hc₂ : Nat.card P₂ ≤ k₂ := h₂ P₂ hP₂ fun y hy => by
    obtain ⟨hy, x, hx, hxy⟩ := hy
    exact (hsq x hx y hy hxy).2
  have hcP : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x := fun x hx y hy => hc x hx.1 y hy.1
  have hiP : P₁ ⊓ P₂ = ⊥ := eq_bot_iff.2 ((inf_le_inf hP₁ hP₂).trans hd.le)
  have hEP : E ≤ P₁ ⊔ P₂ := by
    intro g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hdec g (hE hg)
    exact mul_mem (mem_sup_left ⟨hx, y, hy, hg⟩) (mem_sup_right ⟨hy, x, hx, hg⟩)
  have hcard' : Nat.card ↥(P₁ ⊔ P₂) = Nat.card P₁ * Nat.card P₂ :=
    card_sup_of_le_normalizer (le_normalizer_of_comm hcP) hiP
  haveI : Finite ↥(P₁ ⊔ P₂) := Nat.finite_of_card_ne_zero (by
    rw [hcard']
    exact Nat.mul_ne_zero (Nat.card_pos (α := P₁)).ne' (Nat.card_pos (α := P₂)).ne')
  have hle : Nat.card E ≤ Nat.card ↥(P₁ ⊔ P₂) := card_le_of_le hEP
  rw [hcard', hcard] at hle
  have e₁ : Nat.card P₁ = k₁ := by
    by_contra hne
    have hlt : Nat.card P₁ < k₁ := lt_of_le_of_ne hc₁ hne
    have : Nat.card P₁ * Nat.card P₂ < k₁ * k₂ := by
      calc Nat.card P₁ * Nat.card P₂ ≤ Nat.card P₁ * k₂ := Nat.mul_le_mul_left _ hc₂
        _ < k₁ * k₂ := Nat.mul_lt_mul_of_pos_right hlt (by
          have := Nat.card_pos (α := P₂); omega)
    omega
  have e₂ : Nat.card P₂ = k₂ := by
    by_contra hne
    have hlt : Nat.card P₂ < k₂ := lt_of_le_of_ne hc₂ hne
    have : Nat.card P₁ * Nat.card P₂ < k₁ * k₂ := by
      rw [e₁]
      exact Nat.mul_lt_mul_of_pos_left hlt (by have := Nat.card_pos (α := P₁); omega)
    omega
  have hEeq : E = P₁ ⊔ P₂ := eq_of_le_of_card_ge hEP (by rw [hcard', hcard, e₁, e₂])
  have hP₁E : P₁ = E ⊓ H₁ := by
    apply le_antisymm
    · exact le_inf (hEeq ▸ le_sup_left) hP₁
    · intro x hx
      exact ⟨hx.2, 1, one_mem _, by rw [mul_one]; exact hx.1⟩
  have hP₂E : P₂ = E ⊓ H₂ := by
    apply le_antisymm
    · exact le_inf (hEeq ▸ le_sup_right) hP₂
    · intro y hy
      exact ⟨hy.2, 1, one_mem _, by rw [one_mul]; exact hy.1⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← hP₁E, ← hP₂E]
    exact hEeq
  · rw [← hP₁E, e₁]
  · rw [← hP₂E, e₂]

theorem exists_conj_of_wreath {X Y : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hd : X ⊓ Y = ⊥) {τ : G} (hτ : τ * τ = 1) (hXY : ∀ x ∈ X, τ * x * τ⁻¹ ∈ Y)
    (hYX : ∀ y ∈ Y, τ * y * τ⁻¹ ∈ X) {g : G} (hg : g * τ⁻¹ ∈ X ⊔ Y) (hg2 : g * g = 1) :
    ∃ u ∈ X, u * τ * u⁻¹ = g := by
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  obtain ⟨w₀, hw₀, w₁, hw₁, hw⟩ :=
    (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc)).1 hg
  have hg' : g = w₀ * w₁ * τ := by
    calc g = g * τ⁻¹ * τ := by group
      _ = w₀ * w₁ * τ := by rw [hw]
  have hv₀ : τ * w₁ * τ⁻¹ ∈ X := hYX w₁ hw₁
  have hv₁ : τ * w₀ * τ⁻¹ ∈ Y := hXY w₀ hw₀
  have hc' : (τ * w₁ * τ⁻¹) * (w₁ * (τ * w₀ * τ⁻¹)) =
      (w₁ * (τ * w₀ * τ⁻¹)) * (τ * w₁ * τ⁻¹) := hc _ hv₀ _ (mul_mem hw₁ hv₁)
  have hprod : (w₀ * (τ * w₁ * τ⁻¹)) * (w₁ * (τ * w₀ * τ⁻¹)) = 1 := by
    calc (w₀ * (τ * w₁ * τ⁻¹)) * (w₁ * (τ * w₀ * τ⁻¹))
        = w₀ * ((τ * w₁ * τ⁻¹) * (w₁ * (τ * w₀ * τ⁻¹))) := by group
      _ = w₀ * ((w₁ * (τ * w₀ * τ⁻¹)) * (τ * w₁ * τ⁻¹)) := by rw [hc']
      _ = w₀ * w₁ * (τ * (w₀ * w₁) * τ⁻¹) := by group
      _ = g * g := by rw [hg', hτi]; group
      _ = 1 := hg2
  have h1 := (eq_and_eq_of_mul_eq_mul hd (mul_mem hw₀ hv₀) (one_mem _) (mul_mem hw₁ hv₁)
    (one_mem _) (hprod.trans (mul_one 1).symm)).2
  have hw₁' : w₁ = τ * w₀⁻¹ * τ⁻¹ := by
    calc w₁ = (τ * w₀ * τ⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
      _ = τ * w₀⁻¹ * τ⁻¹ := by group
  refine ⟨w₀, hw₀, ?_⟩
  rw [hg', hw₁']
  group

@[expose] def wreathDiag {X Y : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (τ : G)
    (hXY : ∀ x ∈ X, τ * x * τ⁻¹ ∈ Y) : X →* G :=
  MonoidHom.mk' (fun u => (u : G) * (τ * u * τ⁻¹)) (by
    intro u v
    have h : (v : G) * (τ * u * τ⁻¹) = (τ * u * τ⁻¹) * v := hc v v.2 _ (hXY u u.2)
    show ((u : G) * v) * (τ * ((u : G) * v) * τ⁻¹) =
      ((u : G) * (τ * u * τ⁻¹)) * ((v : G) * (τ * v * τ⁻¹))
    calc ((u : G) * v) * (τ * ((u : G) * v) * τ⁻¹)
        = u * (v * (τ * u * τ⁻¹)) * (τ * v * τ⁻¹) := by group
      _ = u * ((τ * u * τ⁻¹) * v) * (τ * v * τ⁻¹) := by rw [h]
      _ = ((u : G) * (τ * u * τ⁻¹)) * ((v : G) * (τ * v * τ⁻¹)) := by group)

theorem wreathDiag_apply {X Y : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (τ : G)
    (hXY : ∀ x ∈ X, τ * x * τ⁻¹ ∈ Y) (u : X) :
    wreathDiag hc τ hXY u = u * (τ * u * τ⁻¹) := rfl

theorem wreathDiag_injective {X Y : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hd : X ⊓ Y = ⊥) (τ : G) (hXY : ∀ x ∈ X, τ * x * τ⁻¹ ∈ Y) :
    Function.Injective (wreathDiag hc τ hXY) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  rw [wreathDiag_apply] at hu
  exact Subtype.ext (eq_and_eq_of_mul_eq_mul hd u.2 (one_mem _) (hXY u u.2) (one_mem _)
    (hu.trans (mul_one 1).symm)).1

theorem wreathDiag_comm {X Y : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {τ : G}
    (hτ : τ * τ = 1) (hXY : ∀ x ∈ X, τ * x * τ⁻¹ ∈ Y) (u : X) :
    wreathDiag hc τ hXY u * τ = τ * wreathDiag hc τ hXY u := by
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  rw [wreathDiag_apply]
  have h : (u : G) * (τ * u * τ⁻¹) = (τ * u * τ⁻¹) * u := hc u u.2 _ (hXY u u.2)
  calc (u : G) * (τ * u * τ⁻¹) * τ = (τ * u * τ⁻¹) * u * τ := by rw [h]
    _ = τ * ((u : G) * (τ * u * τ⁻¹)) := by rw [hτi]; group

end CFSG.CGT.Foote81L6.TStruct
