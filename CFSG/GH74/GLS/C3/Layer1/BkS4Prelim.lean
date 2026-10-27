module

public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.GH74.GLS.C3.Layer1.P34Proj
public import CFSG.GH74.GLS.C3.Layer1.BackBasic

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.GH74.GLS.C3.Layer1.Back

variable {G : Type} [Group G]

theorem exists_central_of_normal [Finite G] {H W : Subgroup G} (hH : IsPGroup 2 ↥H)
    (hW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W) (hWH : W ≤ H) (hW1 : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 1 ∧ ∀ h ∈ H, h * w = w * h := by
  have : Group.IsNilpotent ↥H := hH.isNilpotent
  have hN : (W.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hW g g.2 n hn⟩
  have hne : W.subgroupOf H ≠ ⊥ := by
    intro h0
    apply hW1
    rw [eq_bot_iff]
    intro w hw
    have : (⟨w, hWH hw⟩ : ↥H) ∈ W.subgroupOf H := hw
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have h2 := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨⟨w, hwH⟩, hwN, hwc⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h2
  refine ⟨w, hwN, fun h => hw1 (Subtype.ext (Subtype.ext h)), fun h hh => ?_⟩
  have := Subgroup.mem_center_iff.1 hwc ⟨h, hh⟩
  exact congrArg Subtype.val this

theorem mem_normalizer_of_two_sided {W : Subgroup G} {a : G} (h1 : ∀ w ∈ W, a * w * a⁻¹ ∈ W)
    (h2 : ∀ w ∈ W, a⁻¹ * w * a ∈ W) : a ∈ normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨h1 w, fun hw => ?_⟩
  have := h2 _ hw
  simpa [mul_assoc] using this

theorem isElementaryAbelian_sup_of_commute {A B : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    CFSG.IsElementaryAbelian 2 ↥(A ⊔ B) := by
  obtain ⟨hAc, hAs⟩ := forall_of_isElementaryAbelian hA
  obtain ⟨hBc, hBs⟩ := forall_of_isElementaryAbelian hB
  have h1 : ∀ x ∈ A ⊔ B, ∀ a ∈ A, x * a = a * x := by
    intro x hx a ha
    have hle : A ⊔ B ≤ centralizer ({a} : Set G) := by
      refine sup_le (fun a' ha' => ?_) (fun b hb => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hAc a' ha' a ha)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hAB a ha b hb).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have h2 : ∀ x ∈ A ⊔ B, ∀ b ∈ B, x * b = b * x := by
    intro x hx b hb
    have hle : A ⊔ B ≤ centralizer ({b} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun b' hb' => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hAB a ha b hb)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hBc b' hb' b hb)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have h3 : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
    intro x hx y hy
    have hle : A ⊔ B ≤ centralizer ({y} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (h1 y hy a ha).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (h2 y hy b hb).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  refine isElementaryAbelian_of_forall h3 (fun u hu => ?_)
  rw [Subgroup.sup_eq_closure] at hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hAs x hx
    · exact hBs x hx
  | one => simp
  | mul x y hx hy hxs hys =>
    have hx' : x ∈ A ⊔ B := by rwa [Subgroup.sup_eq_closure]
    have hy' : y ∈ A ⊔ B := by rwa [Subgroup.sup_eq_closure]
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [h3 y hy' x hx']
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxs, hys, one_mul]
  | inv x hx hxs =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [hxs, inv_one]

theorem mem_zpowers_of_sq {d : G} (hd : d * d = 1) {u : G} (hu : u ∈ zpowers d) : u = 1 ∨ u = d := by
  obtain ⟨k, rfl⟩ := hu
  show d ^ k = 1 ∨ d ^ k = d
  have hd2 : d ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hd
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
    rw [zpow_mul, hd2, one_zpow]
  · right
    obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
    rw [zpow_add_one, zpow_mul, hd2, one_zpow, one_mul]

theorem isElementaryAbelian_zpowers_of_sq {d : G} (hd : d * d = 1) :
    CFSG.IsElementaryAbelian 2 ↥(zpowers d) := by
  refine isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
  · rcases mem_zpowers_of_sq hd hu with rfl | rfl <;> rcases mem_zpowers_of_sq hd hv with rfl | rfl <;>
      simp
  · rcases mem_zpowers_of_sq hd hu with rfl | rfl
    · simp
    · exact hd

theorem mem_sup_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hnorm : B ≤ normalizer (A : Set G) := CFSG.GH74.GLS.C3.Layer1.P34.W_le_normalizer_of
    (fun w hw q hq => by
      have e : w * q * w⁻¹ = q := by
        calc w * q * w⁻¹ = q * w * w⁻¹ := by rw [hAB q hq w hw]
          _ = q := by group
      rw [e]; exact hq)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A B hnorm] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨a, ha, b, hb, rfl⟩

theorem card_sup_of_commute_of_disjoint [Finite G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hnorm : B ≤ normalizer (A : Set G) := CFSG.GH74.GLS.C3.Layer1.P34.W_le_normalizer_of
    (fun w hw q hq => by
      have e : w * q * w⁻¹ = q := by
        calc w * q * w⁻¹ = q * w * w⁻¹ := by rw [hAB q hq w hw]
          _ = q := by group
      rw [e]; exact hq)
  have h := CFSG.GH74.GLS.C3.Layer1.P34.card_mul_inf A B
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnorm, hd, Subgroup.card_bot, mul_one] at h
  exact h


theorem card_sup_le_of_commute [Finite G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  have hnorm : B ≤ normalizer (A : Set G) := CFSG.GH74.GLS.C3.Layer1.P34.W_le_normalizer_of
    (fun w hw q hq => by
      have e : w * q * w⁻¹ = q := by
        calc w * q * w⁻¹ = q * w * w⁻¹ := by rw [hAB q hq w hw]
          _ = q := by group
      rw [e]; exact hq)
  have h := CFSG.GH74.GLS.C3.Layer1.P34.card_mul_inf A B
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnorm] at h
  have hpos : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
  calc Nat.card ↥(A ⊔ B) = Nat.card ↥(A ⊔ B) * 1 := (mul_one _).symm
    _ ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := Nat.mul_le_mul_left _ hpos
    _ = Nat.card ↥A * Nat.card ↥B := h

@[expose] def IsD8 (P : Subgroup G) : Prop := Nonempty (↥P ≃* DihedralGroup 4)

namespace IsD8

open DihedralGroup

theorem conjugate {P : Subgroup G} (h : IsD8 P) (a : G) : IsD8 (CFSG.conjugate P a) := by
  obtain ⟨e⟩ := h
  exact ⟨(conjugateEquiv P a).symm.trans e⟩

theorem card_eq [Finite G] {P : Subgroup G} (h : IsD8 P) : Nat.card ↥P = 8 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]

theorem exists_z {P : Subgroup G} (h : IsD8 P) :
    ∃ z ∈ P, z ≠ 1 ∧ z * z = 1 ∧ (∀ p ∈ P, p * z = z * p) ∧
      ∀ w ∈ P, (∀ p ∈ P, p * w = w * p) → w = 1 ∨ w = z := by
  obtain ⟨e⟩ := h
  have hc : ∀ h : DihedralGroup 4, r 2 * h = h * r 2 := by decide
  have hu : ∀ g : DihedralGroup 4, (∀ h : DihedralGroup 4, g * h = h * g) → g = 1 ∨ g = r 2 := by
    decide
  have h22 : (r 2 : DihedralGroup 4) * r 2 = 1 := by decide
  have h21 : (r 2 : DihedralGroup 4) ≠ 1 := by decide
  refine ⟨((e.symm (r 2) : ↥P) : G), (e.symm (r 2)).2, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply h21
    have h2 : e.symm (r 2) = 1 := Subtype.ext h1
    have := congrArg e h2
    simpa using this
  · have := congrArg Subtype.val
      (show e.symm (r 2) * e.symm (r 2) = 1 by rw [← map_mul, h22, map_one])
    simpa using this
  · intro p hp
    have : (⟨p, hp⟩ : ↥P) * e.symm (r 2) = e.symm (r 2) * ⟨p, hp⟩ := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (hc _).symm
    exact congrArg Subtype.val this
  · intro w hw hcomm
    have hg : ∀ h : DihedralGroup 4, e ⟨w, hw⟩ * h = h * e ⟨w, hw⟩ := by
      intro h
      have h1 : (⟨w, hw⟩ : ↥P) * e.symm h = e.symm h * ⟨w, hw⟩ :=
        Subtype.ext (hcomm _ (e.symm h).2).symm
      have := congrArg e h1
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    rcases hu _ hg with h1 | h1
    · left
      have : (⟨w, hw⟩ : ↥P) = 1 := e.injective (by rw [h1, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨w, hw⟩ : ↥P) = e.symm (r 2) := e.injective (by rw [h1, MulEquiv.apply_symm_apply])
      exact congrArg Subtype.val this

theorem exists_noncentral_involution {P : Subgroup G} (h : IsD8 P) :
    ∃ d ∈ P, d * d = 1 ∧ ∃ p ∈ P, d * p ≠ p * d := by
  obtain ⟨e⟩ := h
  have h1 : (sr 0 : DihedralGroup 4) * sr 0 = 1 := by decide
  have h2 : (sr 0 : DihedralGroup 4) * r 1 ≠ r 1 * sr 0 := by decide
  refine ⟨((e.symm (sr 0) : ↥P) : G), (e.symm (sr 0)).2, ?_, ((e.symm (r 1) : ↥P) : G),
    (e.symm (r 1)).2, ?_⟩
  · have := congrArg Subtype.val
      (show e.symm (sr 0) * e.symm (sr 0) = 1 by rw [← map_mul, h1, map_one])
    simpa using this
  · intro hc
    apply h2
    have : e.symm (sr 0) * e.symm (r 1) = e.symm (r 1) * e.symm (sr 0) := Subtype.ext hc
    have := congrArg e this
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this

theorem card_le_four [Finite G] {P : Subgroup G} (h : IsD8 P) {E : Subgroup G} (hE : E ≤ P)
    (hel : CFSG.IsElementaryAbelian 2 ↥E) : Nat.card ↥E ≤ 4 := by
  obtain ⟨e⟩ := h
  have key : ∀ s : Finset (DihedralGroup 4), (∀ x ∈ s, ∀ y ∈ s, x * y = y * x) →
      (∀ x ∈ s, x * x = 1) → s.card ≤ 4 := by decide +kernel
  obtain ⟨hcomm, hsq⟩ := forall_of_isElementaryAbelian hel
  let f : ↥E → DihedralGroup 4 := fun x => e ⟨x.1, hE x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have := e.injective hxy
    exact Subtype.ext (congrArg (fun z : ↥P => (z : G)) this)
  have hfm : ∀ x y : ↥E, f x * f y = f ⟨(x : G) * y, E.mul_mem x.2 y.2⟩ := by
    intro x y
    show e _ * e _ = e _
    rw [← map_mul]
    rfl
  have : Fintype ↥E := Fintype.ofFinite _
  have hk := key (Finset.univ.image f) ?_ ?_
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ] at hk
    simpa [Nat.card_eq_fintype_card] using hk
  · intro x hx y hy
    obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨y', -, rfl⟩ := Finset.mem_image.1 hy
    rw [hfm, hfm]
    congr 1
    exact Subtype.ext (hcomm _ x'.2 _ y'.2)
  · intro x hx
    obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 hx
    rw [hfm]
    have : (⟨(x' : G) * x', E.mul_mem x'.2 x'.2⟩ : ↥E) = 1 := Subtype.ext (hsq _ x'.2)
    rw [this]
    show e 1 = 1
    exact map_one e

theorem le_closure_involutions {P : Subgroup G} (h : IsD8 P) :
    P ≤ Subgroup.closure {u : G | u ∈ P ∧ u * u = 1} := by
  obtain ⟨e⟩ := h
  have hprod : ∀ g : DihedralGroup 4, ∃ a b : DihedralGroup 4, a * a = 1 ∧ b * b = 1 ∧ g = a * b := by
    decide
  intro p hp
  obtain ⟨a, b, ha, hb, hab⟩ := hprod (e ⟨p, hp⟩)
  have hp' : (⟨p, hp⟩ : ↥P) = e.symm a * e.symm b := by
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hab
  have hpe : p = ((e.symm a : ↥P) : G) * ((e.symm b : ↥P) : G) := congrArg Subtype.val hp'
  rw [hpe]
  refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨(e.symm a).2, ?_⟩)
    (Subgroup.subset_closure ⟨(e.symm b).2, ?_⟩)
  · have := congrArg Subtype.val (show e.symm a * e.symm a = 1 by rw [← map_mul, ha, map_one])
    simpa using this
  · have := congrArg Subtype.val (show e.symm b * e.symm b = 1 by rw [← map_mul, hb, map_one])
    simpa using this

theorem exists_inner {P : Subgroup G} (h : IsD8 P) {s : G} (hs : s ∈ P) (hs2 : s * s = 1)
    (hsn : ∃ p ∈ P, s * p ≠ p * s) {t : G} (htP : ∀ p : G, p ∈ P ↔ t * p * t⁻¹ ∈ P)
    (hts : (t * s * t⁻¹) * s = s * (t * s * t⁻¹)) :
    ∃ g ∈ P, ∀ p ∈ P, t * p * t⁻¹ = g * p * g⁻¹ := by
  obtain ⟨e⟩ := h
  have d8_inner : ∀ σ ρ' s' : DihedralGroup 4, σ * σ = 1 → ¬ (∀ h : DihedralGroup 4, σ * h = h * σ) →
      ρ' ^ 4 = 1 → ρ' ^ 2 ≠ 1 → s' * s' = 1 → s' * ρ' * s' = ρ'⁻¹ → s' * σ = σ * s' →
      ∃ g : DihedralGroup 4, g * DihedralGroup.r 1 * g⁻¹ = ρ' ∧ g * σ * g⁻¹ = s' := by decide
  have d8_gen : ∀ σ : DihedralGroup 4, σ * σ = 1 → ¬ (∀ h : DihedralGroup 4, σ * h = h * σ) →
      ∀ x : DihedralGroup 4, ∃ n : Fin 4, ∃ m : Fin 2,
        x = (DihedralGroup.r 1) ^ (n : ℕ) * σ ^ (m : ℕ) := by decide
  have d8_rel : ∀ σ : DihedralGroup 4, σ * σ = 1 → ¬ (∀ h : DihedralGroup 4, σ * h = h * σ) →
      σ * DihedralGroup.r 1 * σ = (DihedralGroup.r 1)⁻¹ := by decide
  have d8_r1 : (DihedralGroup.r 1 : DihedralGroup 4) ^ 4 = 1 := by decide
  have d8_r1' : (DihedralGroup.r 1 : DihedralGroup 4) ^ 2 ≠ 1 := by decide
  let α : ↥P →* ↥P :=
    { toFun := fun p => ⟨t * p * t⁻¹, (htP p).1 p.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun p q => Subtype.ext (by
        show t * ((p : G) * q) * t⁻¹ = t * p * t⁻¹ * (t * q * t⁻¹)
        group) }
  have hα : Function.Injective α := by
    intro p q hpq
    have := congrArg Subtype.val hpq
    have h1 : t * (p : G) * t⁻¹ = t * q * t⁻¹ := this
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  let α' : DihedralGroup 4 →* DihedralGroup 4 :=
    e.toMonoidHom.comp (α.comp e.symm.toMonoidHom)
  have hα' : Function.Injective α' := by
    intro x y hxy
    have h1 : α (e.symm x) = α (e.symm y) := e.injective hxy
    exact e.symm.injective (hα h1)
  set σ : DihedralGroup 4 := e ⟨s, hs⟩ with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    have : (⟨s, hs⟩ : ↥P) * ⟨s, hs⟩ = 1 := Subtype.ext hs2
    rw [this, map_one]
  have hσn : ¬ (∀ h : DihedralGroup 4, σ * h = h * σ) := by
    intro hc
    obtain ⟨p, hp, hsp⟩ := hsn
    apply hsp
    have h1 := hc (e ⟨p, hp⟩)
    rw [hσdef, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)
  have hα'σ : α' σ = e ⟨t * s * t⁻¹, (htP s).1 hs⟩ := by
    show e (α (e.symm (e ⟨s, hs⟩))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨g, hg1, hg2⟩ := d8_inner σ (α' (DihedralGroup.r 1)) (α' σ) hσ2 hσn
    (by rw [← map_pow, d8_r1, map_one])
    (fun h1 => d8_r1' (hα' (by rw [map_pow, h1, map_one])))
    (by rw [← map_mul, hσ2, map_one])
    (by rw [← map_mul, ← map_mul, d8_rel σ hσ2 hσn, map_inv])
    (by
      rw [hα'σ, hσdef, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hts)
  refine ⟨((e.symm g : ↥P) : G), (e.symm g).2, fun p hp => ?_⟩
  have hall : ∀ x : DihedralGroup 4, α' x = g * x * g⁻¹ := by
    have heq : (α' : DihedralGroup 4 →* DihedralGroup 4) =
        (MulAut.conj g).toMonoidHom := by
      refine MonoidHom.eq_of_eqOn_top ?_
      have hcl : Subgroup.closure ({DihedralGroup.r 1, σ} : Set (DihedralGroup 4)) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        obtain ⟨n, m, rfl⟩ := d8_gen σ hσ2 hσn x
        refine Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
          (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      rw [← hcl]
      refine MonoidHom.eqOn_closure ?_
      intro x hx
      rcases hx with rfl | rfl
      · rw [← hg1]; rfl
      · rw [← hg2]; rfl
    intro x
    exact DFunLike.congr_fun heq x
  have h2 := hall (e ⟨p, hp⟩)
  have h3 : α' (e ⟨p, hp⟩) = e ⟨t * p * t⁻¹, (htP p).1 hp⟩ := by
    show e (α (e.symm (e ⟨p, hp⟩))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [h3] at h2
  have h4 : (⟨t * p * t⁻¹, (htP p).1 hp⟩ : ↥P) = e.symm g * ⟨p, hp⟩ * (e.symm g)⁻¹ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h2
  exact congrArg Subtype.val h4

end IsD8

end CFSG.GH74.GLS.C3.Layer1.Bk
