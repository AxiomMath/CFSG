module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem commutator_commutator_le_of_le_normalizer {N H₁ H₂ H₃ : Subgroup G}
    (hn₁ : H₁ ≤ normalizer (N : Set G)) (hn₂ : H₂ ≤ normalizer (N : Set G))
    (hn₃ : H₃ ≤ normalizer (N : Set G)) (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  set M := normalizer (N : Set G)
  have hN : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  set π := QuotientGroup.mk' (N.subgroupOf M)
  have hmap : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf M, B.subgroupOf M⁆, C.subgroupOf M⁆).map M.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔ ⁅⁅(A.subgroupOf M).map π, (B.subgroupOf M).map π⁆,
        (C.subgroupOf M).map π⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key H₂ H₃ H₁ hn₂ hn₃ hn₁] at h1
  rw [key H₃ H₁ H₂ hn₃ hn₁ hn₂] at h2
  rw [key H₁ H₂ H₃ hn₁ hn₂ hn₃]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem le_of_perfect_of_le_sup_of_commute {M W D : Subgroup G}
    (hWM : W ≤ normalizer (M : Set G)) (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (hDp : ⁅D, D⁆ = D) (hD : D ≤ M ⊔ W) : D ≤ M := by
  have hdec : ∀ a ∈ M ⊔ W, ∃ m ∈ M, ∃ w ∈ W, m * w = a := by
    intro a ha
    have ha' : a ∈ ((M : Set G) * (W : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left M W hWM]
      exact ha
    exact Set.mem_mul.1 ha'
  have hconj : ∀ w ∈ W, ∀ m ∈ M, w * m * w⁻¹ ∈ M := fun w hw m hm =>
    (Subgroup.mem_normalizer_iff.1 (hWM hw) m).1 hm
  have hcomm : ⁅M ⊔ W, M ⊔ W⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨m, hm, w, hw, rfl⟩ := hdec a ha
    obtain ⟨m', hm', w', hw', rfl⟩ := hdec b hb
    have hww : w * w' * w⁻¹ = w' := by
      rw [hW w hw w' hw', mul_inv_cancel_right]
    have key : ⁅m * w, m' * w'⁆ = m * (w * m' * w⁻¹) * (w' * m⁻¹ * w'⁻¹) * m'⁻¹ := by
      calc ⁅m * w, m' * w'⁆
          = m * (w * m' * w⁻¹) * (w * w' * w⁻¹) * m⁻¹ * w'⁻¹ * m'⁻¹ := by
            rw [commutatorElement_def]
            group
        _ = m * (w * m' * w⁻¹) * w' * m⁻¹ * w'⁻¹ * m'⁻¹ := by rw [hww]
        _ = m * (w * m' * w⁻¹) * (w' * m⁻¹ * w'⁻¹) * m'⁻¹ := by group
    rw [key]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm (hconj w hw m' hm'))
      (hconj w' hw' _ (M.inv_mem hm))) (M.inv_mem hm')
  calc D = ⁅D, D⁆ := hDp.symm
    _ ≤ ⁅M ⊔ W, M ⊔ W⁆ := Subgroup.commutator_mono hD hD
    _ ≤ M := hcomm

theorem commutator_le_of_forall_eq_mul_of_le_centralizer {W X W₁ W₂ : Subgroup G}
    (hXW₁ : X ≤ normalizer (W₁ : Set G)) (hW₂ : W₂ ≤ centralizer (X : Set G))
    (hdec : ∀ w ∈ W, ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, w = w₁ * w₂) : ⁅W, X⁆ ≤ W₁ := by
  rw [Subgroup.commutator_le]
  intro w hw x hx
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hdec w hw
  have hxw₂ : x * w₂ = w₂ * x := mem_centralizer_iff.1 (hW₂ hw₂) x hx
  have key : ⁅w₁ * w₂, x⁆ = w₁ * (x * w₁⁻¹ * x⁻¹) := by
    calc ⁅w₁ * w₂, x⁆ = w₁ * (w₂ * x) * w₂⁻¹ * w₁⁻¹ * x⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = w₁ * (x * w₁⁻¹ * x⁻¹) := by
          rw [← hxw₂]
          group
  rw [key]
  exact W₁.mul_mem hw₁ ((Subgroup.mem_normalizer_iff.1 (hXW₁ hx) _).1 (W₁.inv_mem hw₁))

theorem le_normalizer_of_mul_mul_inv_mem {A N : Subgroup G}
    (h : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) : A ≤ normalizer (N : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro n
  refine ⟨h a ha n, fun hn => ?_⟩
  have h1 := h a⁻¹ (A.inv_mem ha) _ hn
  rwa [inv_inv, show a⁻¹ * (a * n * a⁻¹) * a = n by group] at h1

theorem le_normalizer_inf_centralizer_of_commutator_le {W A B : Subgroup G}
    (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (hAW : A ≤ normalizer (W : Set G))
    (hAB : ⁅A, B⁆ ≤ W) :
    A ≤ normalizer ((W ⊓ centralizer (B : Set G) : Subgroup G) : Set G) := by
  apply le_normalizer_of_mul_mul_inv_mem
  intro a ha w hw
  obtain ⟨hwW, hwC⟩ := mem_inf.1 hw
  refine mem_inf.2 ⟨(mem_normalizer_iff.1 (hAW ha) w).1 hwW, ?_⟩
  rw [mem_centralizer_iff]
  intro b hb
  have hc : ⁅a⁻¹, b⁆ ∈ W := hAB (commutator_mem_commutator (A.inv_mem ha) hb)
  have h1 : a⁻¹ * b * a = ⁅a⁻¹, b⁆ * b := by
    rw [commutatorElement_def]
    group
  have hwb : b * w = w * b := mem_centralizer_iff.1 hwC b hb
  have hwc : ⁅a⁻¹, b⁆ * w = w * ⁅a⁻¹, b⁆ := hW _ hc w hwW
  have h2 : (a⁻¹ * b * a) * w = w * (a⁻¹ * b * a) := by
    rw [h1, mul_assoc, hwb, ← mul_assoc, hwc, mul_assoc]
  calc b * (a * w * a⁻¹) = a * ((a⁻¹ * b * a) * w) * a⁻¹ := by group
    _ = a * (w * (a⁻¹ * b * a)) * a⁻¹ := by rw [h2]
    _ = a * w * a⁻¹ * b := by group

theorem le_normalizer_inf_centralizer_self {W A : Subgroup G} :
    A ≤ normalizer ((W ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  apply le_normalizer_of_mul_mul_inv_mem
  intro a ha w hw
  have haw : a * w = w * a := mem_centralizer_iff.1 (mem_inf.1 hw).2 a ha
  rw [haw, mul_inv_cancel_right]
  exact hw

theorem commute_and_inf_eq_bot_of_decomposition {W X Y D : Subgroup G}
    (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (hXp : ⁅X, X⁆ = X) (hYp : ⁅Y, Y⁆ = Y)
    (hXW : X ≤ normalizer (W : Set G)) (hYW : Y ≤ normalizer (W : Set G))
    (hWX : W ≤ normalizer (X : Set G)) (hWY : W ≤ normalizer (Y : Set G))
    (hXY : ⁅X, Y⁆ ≤ W) (hXYW : X ⊓ Y ≤ W)
    (hdec : ∀ w ∈ W, ∃ w₁ ∈ W ⊓ centralizer (Y : Set G),
      ∃ w₂ ∈ W ⊓ centralizer (X : Set G), w = w₁ * w₂)
    (hDp : ⁅D, D⁆ = D) (hD : D ≤ (X ⊔ Y) ⊔ W) (hfix : W ⊓ centralizer (D : Set G) = ⊥) :
    Y ≤ centralizer (X : Set G) ∧ X ⊓ Y = ⊥ ∧ D ≤ X ⊔ Y := by
  have hYX : ⁅Y, X⁆ ≤ W := by
    rw [commutator_comm]
    exact hXY
  have hXW₁ : X ≤ normalizer ((W ⊓ centralizer (Y : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer_of_commutator_le hW hXW hXY
  have hYW₂ : Y ≤ normalizer ((W ⊓ centralizer (X : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer_of_commutator_le hW hYW hYX
  have hYW₁ : Y ≤ normalizer ((W ⊓ centralizer (Y : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer_self
  have hXW₂ : X ≤ normalizer ((W ⊓ centralizer (X : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer_self
  have hdec' : ∀ w ∈ W, ∃ w₂ ∈ W ⊓ centralizer (X : Set G),
      ∃ w₁ ∈ W ⊓ centralizer (Y : Set G), w = w₂ * w₁ := by
    intro w hw
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hdec w hw
    exact ⟨w₂, hw₂, w₁, hw₁, hW w₁ (mem_inf.1 hw₁).1 w₂ (mem_inf.1 hw₂).1⟩
  have hWX₁ : ⁅W, X⁆ ≤ W ⊓ centralizer (Y : Set G) :=
    commutator_le_of_forall_eq_mul_of_le_centralizer hXW₁ inf_le_right hdec
  have hWY₂ : ⁅W, Y⁆ ≤ W ⊓ centralizer (X : Set G) :=
    commutator_le_of_forall_eq_mul_of_le_centralizer hYW₂ inf_le_right hdec'
  have h1 : ⁅X, Y⁆ ≤ W ⊓ centralizer (Y : Set G) := by
    have h := commutator_commutator_le_of_le_normalizer (H₁ := X) (H₂ := X) (H₃ := Y) hXW₁ hXW₁
      hYW₁ ((commutator_mono hXY le_rfl).trans hWX₁) ((commutator_mono hYX le_rfl).trans hWX₁)
    rwa [hXp] at h
  have h2 : ⁅X, Y⁆ ≤ W ⊓ centralizer (X : Set G) := by
    have h := commutator_commutator_le_of_le_normalizer (H₁ := Y) (H₂ := Y) (H₃ := X) hYW₂ hYW₂
      hXW₂ ((commutator_mono hYX le_rfl).trans hWY₂) ((commutator_mono hXY le_rfl).trans hWY₂)
    rw [hYp, commutator_comm] at h
    exact h
  have hcent : ∀ g ∈ W, g ∈ centralizer (X : Set G) → g ∈ centralizer (Y : Set G) →
      g ∈ W ⊓ centralizer (D : Set G) := by
    intro g hgW hgX hgY
    refine mem_inf.2 ⟨hgW, ?_⟩
    have hle : (X ⊔ Y) ⊔ W ≤ centralizer ({g} : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro x hx
        rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.1 hgX x hx
      · intro y hy
        rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.1 hgY y hy
      · intro w hw
        rw [mem_centralizer_singleton_iff]
        exact hW w hw g hgW
    rw [mem_centralizer_iff]
    intro d hd
    exact mem_centralizer_singleton_iff.1 (hle (hD hd))
  have hbot : ⁅X, Y⁆ = ⊥ := by
    rw [eq_bot_iff, ← hfix]
    intro g hg
    obtain ⟨hgW, hgY⟩ := mem_inf.1 (h1 hg)
    exact hcent g hgW (mem_inf.1 (h2 hg)).2 hgY
  have hYC : Y ≤ centralizer (X : Set G) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hbot
  have hYN : Y ≤ normalizer (X : Set G) := by
    apply le_normalizer_of_mul_mul_inv_mem
    intro y hy x hx
    rw [← mem_centralizer_iff.1 (hYC hy) x hx, mul_inv_cancel_right]
    exact hx
  have hXYset : ∀ n ∈ X ⊔ Y, ∃ x ∈ X, ∃ y ∈ Y, x * y = n := by
    intro n hn
    have hn' : n ∈ ((X : Set G) * (Y : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left X Y hYN]
      exact hn
    exact Set.mem_mul.1 hn'
  have hWM : W ≤ normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
    apply le_normalizer_of_mul_mul_inv_mem
    intro w hw n hn
    obtain ⟨x, hx, y, hy, rfl⟩ := hXYset n hn
    have e : w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 (hWX hw) x).1 hx))
      (mem_sup_right ((mem_normalizer_iff.1 (hWY hw) y).1 hy))
  have hDM : D ≤ X ⊔ Y := le_of_perfect_of_le_sup_of_commute hWM hW hDp hD
  have hinf : X ⊓ Y = ⊥ := by
    rw [eq_bot_iff, ← hfix]
    intro g hg
    obtain ⟨hgX, hgY⟩ := mem_inf.1 hg
    refine hcent g (hXYW hg) (hYC hgY) ?_
    rw [mem_centralizer_iff]
    intro y hy
    exact (mem_centralizer_iff.1 (hYC hy) g hgX).symm
  exact ⟨hYC, hinf, hDM⟩

theorem swapFactor_of_decomposition {t : G} {W X D : Subgroup G}
    (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (hXp : ⁅X, X⁆ = X)
    (hXW : X ≤ normalizer (W : Set G)) (htW : t ∈ normalizer (W : Set G))
    (hWX : W ≤ normalizer (X : Set G))
    (hXY : ⁅X, X.map (MulAut.conj t).toMonoidHom⁆ ≤ W)
    (hXYW : X ⊓ X.map (MulAut.conj t).toMonoidHom ≤ W)
    (hdec : ∀ w ∈ W, ∃ w₁ ∈ W ⊓ centralizer (X.map (MulAut.conj t).toMonoidHom : Set G),
      ∃ w₂ ∈ W ⊓ centralizer (X : Set G), w = w₁ * w₂)
    (hDp : ⁅D, D⁆ = D) (hD : D ≤ (X ⊔ X.map (MulAut.conj t).toMonoidHom) ⊔ W)
    (hfix : W ⊓ centralizer (D : Set G) = ⊥) :
    X.map (MulAut.conj t).toMonoidHom ≤ centralizer (X : Set G) ∧
      X ⊓ X.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      D ≤ X ⊔ X.map (MulAut.conj t).toMonoidHom := by
  have hconj : ∀ g ∈ normalizer (W : Set G), ∀ w ∈ W, g * w * g⁻¹ ∈ W := fun g hg w hw =>
    (mem_normalizer_iff.1 hg w).1 hw
  have hYp : ⁅X.map (MulAut.conj t).toMonoidHom, X.map (MulAut.conj t).toMonoidHom⁆ =
      X.map (MulAut.conj t).toMonoidHom := by
    rw [← Subgroup.map_commutator, hXp]
  have hYW : X.map (MulAut.conj t).toMonoidHom ≤ normalizer (W : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem htW (hXW hx)) (inv_mem htW)
  have hWY : W ≤ normalizer ((X.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    apply le_normalizer_of_mul_mul_inv_mem
    rintro w hw _ ⟨x, hx, rfl⟩
    have hu : t⁻¹ * w * t⁻¹⁻¹ ∈ W := hconj t⁻¹ (inv_mem htW) w hw
    rw [inv_inv] at hu
    have hux : (t⁻¹ * w * t) * x * (t⁻¹ * w * t)⁻¹ ∈ X :=
      (mem_normalizer_iff.1 (hWX hu) x).1 hx
    refine ⟨(t⁻¹ * w * t) * x * (t⁻¹ * w * t)⁻¹, hux, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact commute_and_inf_eq_bot_of_decomposition hW hXp hYp hXW hYW hWX hWY hXY hXYW hdec hDp hD
    hfix

end CFSG.SeitzReduction.LinearPilot
