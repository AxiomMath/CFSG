module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCore

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private def innerInducing (A V : Subgroup G) : Subgroup G where
  carrier := {w | w ∈ A ∧ ∃ a ∈ V, ∀ x ∈ A, a * x * a⁻¹ = w * x * w⁻¹}
  one_mem' := ⟨A.one_mem, 1, V.one_mem, by intro x _; simp⟩
  mul_mem' := by
    intro w₁ w₂ h₁ h₂
    obtain ⟨h₁A, a₁, ha₁, h₁'⟩ := h₁
    obtain ⟨h₂A, a₂, ha₂, h₂'⟩ := h₂
    refine ⟨A.mul_mem h₁A h₂A, a₁ * a₂, V.mul_mem ha₁ ha₂, ?_⟩
    intro x hx
    calc (a₁ * a₂) * x * (a₁ * a₂)⁻¹
        = a₁ * (a₂ * x * a₂⁻¹) * a₁⁻¹ := by group
      _ = a₁ * (w₂ * x * w₂⁻¹) * a₁⁻¹ := by rw [h₂' x hx]
      _ = w₁ * (w₂ * x * w₂⁻¹) * w₁⁻¹ :=
          h₁' _ (A.mul_mem (A.mul_mem h₂A hx) (A.inv_mem h₂A))
      _ = (w₁ * w₂) * x * (w₁ * w₂)⁻¹ := by group
  inv_mem' := by
    intro w hw
    obtain ⟨hwA, a, ha, hw'⟩ := hw
    refine ⟨A.inv_mem hwA, a⁻¹, V.inv_mem ha, ?_⟩
    intro x hx
    have hy : w⁻¹ * x * w ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hwA) hx) hwA
    have hx' : a * (w⁻¹ * x * w) * a⁻¹ = x := by
      calc a * (w⁻¹ * x * w) * a⁻¹
          = w * (w⁻¹ * x * w) * w⁻¹ := hw' _ hy
        _ = x := by group
    calc a⁻¹ * x * (a⁻¹)⁻¹
        = a⁻¹ * x * a := by group
      _ = a⁻¹ * (a * (w⁻¹ * x * w) * a⁻¹) * a := by rw [hx']
      _ = w⁻¹ * x * w := by group
      _ = w⁻¹ * x * (w⁻¹)⁻¹ := by group

omit [Finite G] in
private theorem mem_innerInducing {A V : Subgroup G} {w : G} :
    w ∈ innerInducing A V ↔ w ∈ A ∧ ∃ a ∈ V, ∀ x ∈ A, a * x * a⁻¹ = w * x * w⁻¹ :=
  Iff.rfl

omit [Finite G] in
private theorem pow_conj_eq_of_mem_innerInducing {A : Subgroup G} {w a : G} (hwA : w ∈ A)
    (hw : ∀ x ∈ A, a * x * a⁻¹ = w * x * w⁻¹) (n : ℕ) :
    ∀ x ∈ A, a ^ n * x * (a ^ n)⁻¹ = w ^ n * x * (w ^ n)⁻¹ := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
      intro x hx
      have hy : a ^ n * x * (a ^ n)⁻¹ ∈ A := by
        rw [ih x hx]
        exact A.mul_mem (A.mul_mem (A.pow_mem hwA n) hx) (A.inv_mem (A.pow_mem hwA n))
      calc a ^ (n + 1) * x * (a ^ (n + 1))⁻¹
          = a * (a ^ n * x * (a ^ n)⁻¹) * a⁻¹ := by rw [pow_succ', mul_inv_rev]; group
        _ = w * (a ^ n * x * (a ^ n)⁻¹) * w⁻¹ := hw _ hy
        _ = w * (w ^ n * x * (w ^ n)⁻¹) * w⁻¹ := by rw [ih x hx]
        _ = w ^ (n + 1) * x * (w ^ (n + 1))⁻¹ := by rw [pow_succ', mul_inv_rev]; group

omit [Finite G] in
private theorem isPGroup_innerInducing {A V : Subgroup G}
    (hZ : A ⊓ centralizer (A : Set G) = ⊥) (hV : IsPGroup 2 V) :
    IsPGroup 2 (innerInducing A V) := by
  intro g
  obtain ⟨hgA, a, ha, hw⟩ := mem_innerInducing.mp g.2
  obtain ⟨k, hk⟩ := hV ⟨a, ha⟩
  have haK : a ^ 2 ^ k = 1 := by
    simpa [Subgroup.coe_pow] using congrArg (Subtype.val) hk
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  have hcomm : (g : G) ^ 2 ^ k ∈ centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := pow_conj_eq_of_mem_innerInducing hgA hw (2 ^ k) x hx
    rw [haK] at h
    have hx' : (g : G) ^ 2 ^ k * x * ((g : G) ^ 2 ^ k)⁻¹ = x := by simpa using h.symm
    calc x * (g : G) ^ 2 ^ k
        = ((g : G) ^ 2 ^ k * x * ((g : G) ^ 2 ^ k)⁻¹) * (g : G) ^ 2 ^ k := by
          conv_lhs => rw [← hx']
      _ = (g : G) ^ 2 ^ k * x := by group
  have hmem : (g : G) ^ 2 ^ k ∈ A ⊓ centralizer (A : Set G) := ⟨A.pow_mem hgA _, hcomm⟩
  exact Subgroup.mem_bot.mp (hZ ▸ hmem)

omit [Finite G] in
private theorem innerInducing_ne_bot {A V : Subgroup G}
    (hinner : ∀ a ∈ V, ∃ w ∈ A, ∀ x ∈ A, a * x * a⁻¹ = w * x * w⁻¹)
    (hnot : ¬ V ≤ centralizer (A : Set G)) : innerInducing A V ≠ ⊥ := by
  rw [SetLike.le_def] at hnot
  push Not at hnot
  obtain ⟨v, hv, hvc⟩ := hnot
  simp only [Subgroup.mem_centralizer_iff] at hvc
  push Not at hvc
  obtain ⟨x, hx, hxv⟩ := hvc
  obtain ⟨w, hwA, hw⟩ := hinner v hv
  have hwne : w ≠ 1 := by
    intro hw1
    have h : v * x * v⁻¹ = x := by simpa [hw1] using hw x hx
    have hvx : v * x = x * v := by
      calc v * x = (v * x * v⁻¹) * v := by group
        _ = x * v := by rw [h]
    exact hxv hvx.symm
  intro hbot
  have hwbot : w ∈ (⊥ : Subgroup G) :=
    hbot ▸ mem_innerInducing.mpr ⟨hwA, v, hv, hw⟩
  exact hwne (Subgroup.mem_bot.mp hwbot)

private theorem inf_centralizer_ne_bot_of_isPGroup {W : Subgroup G} (hW : IsPGroup 2 W)
    (hne : W ≠ ⊥) : W ⊓ centralizer (W : Set G) ≠ ⊥ := by
  have hlt : (⊥ : Subgroup W) < Subgroup.center W :=
    @IsPGroup.bot_lt_center 2 W _ hW _ ((Subgroup.nontrivial_iff_ne_bot W).mpr hne) _
  obtain ⟨z, hzmem, hzne⟩ :=
    @Subgroup.exists_ne_one_of_nontrivial W _ (Subgroup.center W)
      ((Subgroup.nontrivial_iff_ne_bot (Subgroup.center W)).mpr hlt.ne')
  refine fun hbot => hzne ?_
  have hzW : (z : G) ∈ W := z.2
  have hzc : (z : G) ∈ centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzmem (⟨h, hh⟩ : W))
  have hzZ : (z : G) ∈ W ⊓ centralizer (W : Set G) := ⟨hzW, hzc⟩
  exact Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ hzZ))

omit [Finite G] in
private theorem inf_center_le_inf_centralizer {A V : Subgroup G}
    (hinner : ∀ a ∈ V, ∃ w ∈ A, ∀ x ∈ A, a * x * a⁻¹ = w * x * w⁻¹) :
    innerInducing A V ⊓ centralizer ((innerInducing A V : Subgroup G) : Set G) ≤
      A ⊓ centralizer (V : Set G) := by
  intro z hz
  have hzW : z ∈ innerInducing A V := hz.1
  have hzcW : z ∈ centralizer ((innerInducing A V : Subgroup G) : Set G) := hz.2
  have hzA : z ∈ A := (mem_innerInducing.mp hzW).1
  rw [Subgroup.mem_inf]
  refine ⟨hzA, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hzcW ⊢
  intro v hv
  obtain ⟨w, hwA, hw⟩ := hinner v hv
  have hwW : w ∈ innerInducing A V := mem_innerInducing.mpr ⟨hwA, v, hv, hw⟩
  have hwz : w * z = z * w := hzcW w hwW
  have hvz : v * z * v⁻¹ = w * z * w⁻¹ := hw z hzA
  have hzfix : w * z * w⁻¹ = z := by rw [hwz]; group
  have hvfix : v * z * v⁻¹ = z := by rw [hvz, hzfix]
  calc v * z = (v * z * v⁻¹) * v := by group
    _ = z * v := by rw [hvfix]

omit [Finite G] in
private theorem inf_centralizer_le_normalizer_inf_center {A V : Subgroup G} :
    A ⊓ centralizer (V : Set G) ≤
      normalizer ((innerInducing A V ⊓
        centralizer ((innerInducing A V : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  refine (le_trans ?_ (Subgroup.centralizer_le_normalizer _))
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hyA, hyC⟩ := hy
  rw [Subgroup.mem_centralizer_iff] at hyC
  obtain ⟨hwA, b, hb, hwb⟩ := mem_innerInducing.mp hw.1
  have hby : b * y * b⁻¹ = y := by rw [hyC b hb]; group
  have hwy : w * y * w⁻¹ = y := by rw [← hwb y hyA, hby]
  calc w * y = (w * y * w⁻¹) * w := by group
    _ = y * w := by rw [hwy]

theorem IsPIsolatedOver.le_centralizer_of_inner {A V : Subgroup G}
    (hZ : A ⊓ centralizer (A : Set G) = ⊥) (hV : IsPGroup 2 V)
    (hinner : ∀ a ∈ V, ∃ w ∈ A, ∀ x ∈ A, a * x * a⁻¹ = w * x * w⁻¹)
    (hiso : IsPIsolatedOver 2 (A ⊓ centralizer (V : Set G)) ⊥) :
    V ≤ centralizer (A : Set G) := by
  classical
  by_contra hnot
  have hWne : innerInducing A V ≠ ⊥ := innerInducing_ne_bot hinner hnot
  have hW : IsPGroup 2 (innerInducing A V) := isPGroup_innerInducing hZ hV
  have hZne : innerInducing A V ⊓ centralizer ((innerInducing A V : Subgroup G) : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot_of_isPGroup hW hWne
  have hKH : A ⊓ centralizer (V : Set G) ≤ normalizer (⊥ : Subgroup G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hle : innerInducing A V ⊓ centralizer ((innerInducing A V : Subgroup G) : Set G) ≤
      (⊥ : Subgroup G) :=
    hiso.le_of_normal IsPGroup.of_bot bot_le hKH (inf_center_le_inf_centralizer hinner)
      (hW.to_le inf_le_left) (inf_centralizer_le_normalizer_inf_center)
  exact hZne (le_bot_iff.mp hle)

end CFSG.GroupTheory
