module

public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4

open Subgroup CFSG CFSG.ABGLocalTools

variable {C : Type} [Group C]

structure TIData (v : C) (Zs : Set C) (S E : Subgroup C) (x : C) : Prop where
  v_sq : v * v = 1
  v_ne : v ≠ 1
  v_comm : ∀ c : C, c * v = v * c
  Z_sq : ∀ z ∈ Zs, z * z = 1
  Z_ne : ∀ z ∈ Zs, z ≠ 1
  v_nmem : v ∉ Zs
  Z_conj : ∀ z ∈ Zs, ∀ g : C, g * z * g⁻¹ ∈ Zs
  Z_mul_v : ∀ z ∈ Zs, z * v ∈ Zs
  sylow : IsSylowOf 2 S ⊤
  E_le : E ≤ S
  E_card : Nat.card E = 8
  E_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  E_sq : ∀ a ∈ E, a * a = 1
  v_mem : v ∈ E
  S_norm : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E
  Z_inter : ∀ y ∈ S, (y ∈ Zs ↔ (y ∈ E ∧ y ≠ 1 ∧ y ≠ v))
  x_Z : x ∈ Zs
  x_E : x ∈ E
  Z_single : ∀ z ∈ Zs, ∃ c : C, c * x * c⁻¹ = z
  cent : ∀ g : C, g * x = x * g → ∀ e ∈ E, g * e * g⁻¹ ∈ E

namespace TIData

variable {v : C} {Zs : Set C} {S E : Subgroup C} {x : C}

theorem mem_normalizer_of_forall [Finite C] (E : Subgroup C) {g : C}
    (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E) : g ∈ normalizer (E : Set C) := by
  have hinj : Function.Injective (fun e : E => (⟨g * (e : C) * g⁻¹, hg e e.2⟩ : E)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only at this
    exact Subtype.ext (by simpa using this)
  have hsurj : Function.Surjective (fun e : E => (⟨g * (e : C) * g⁻¹, hg e e.2⟩ : E)) :=
    Finite.injective_iff_surjective.1 hinj
  rw [mem_normalizer_iff]
  intro y
  refine ⟨hg y, fun hy => ?_⟩
  obtain ⟨e, he⟩ := hsurj ⟨g * y * g⁻¹, hy⟩
  have h1 : g * (e : C) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val he
  have h2 : (e : C) = y := mul_left_cancel (mul_right_cancel h1)
  rw [← h2]
  exact e.2

theorem S_le_normalizer [Finite C] (h : TIData v Zs S E x) : S ≤ normalizer (E : Set C) :=
  fun s hs => mem_normalizer_of_forall E (h.S_norm s hs)

theorem sylow_normalizer [Finite C] (h : TIData v Zs S E x) :
    IsSylowOf 2 S (normalizer (E : Set C)) :=
  IsSylowOf.of_le h.sylow h.S_le_normalizer le_top

omit [Group C] in
theorem isPGroup_zpowers {C : Type} [Group C] {z : C} (hz : z * z = 1) :
    IsPGroup 2 (zpowers z) := by
  intro g
  obtain ⟨g, hg⟩ := g
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
  refine ⟨1, Subtype.ext ?_⟩
  show (z ^ m) ^ (2 ^ 1) = 1
  have h2 : z ^ (2 : ℕ) = 1 := by rw [sq]; exact hz
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]

theorem Z_conj' (h : TIData v Zs S E x) {z : C} (hz : z ∈ Zs) (g : C) : g⁻¹ * z * g ∈ Zs := by
  have := h.Z_conj z hz g⁻¹
  simpa using this

theorem conj_v (h : TIData v Zs S E x) (g : C) : g * v * g⁻¹ = v := by
  rw [h.v_comm g]; group

theorem Zmem_of_mem_E (h : TIData v Zs S E x) {y : C} (hy : y ∈ E) (h1 : y ≠ 1) (hv : y ≠ v) :
    y ∈ Zs :=
  (h.Z_inter y (h.E_le hy)).2 ⟨hy, h1, hv⟩

theorem ti_x [Finite C] (h : TIData v Zs S E x) {g : C} (hg : g * x * g⁻¹ ∈ E) :
    g ∈ normalizer (E : Set C) := by
  set N : Subgroup C := normalizer (E : Set C) with hN
  let E'' : Subgroup C := E.map (MulAut.conj g⁻¹).toMonoidHom
  have hE''mem : ∀ y, y ∈ E'' ↔ ∃ e ∈ E, g⁻¹ * e * g = y := by
    intro y
    simp only [E'', Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hE''N : E'' ≤ N := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := (hE''mem y).1 hy
    have hyx : (g⁻¹ * e * g) * x = x * (g⁻¹ * e * g) := by
      calc (g⁻¹ * e * g) * x = g⁻¹ * (e * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * e) * g := by rw [h.E_comm e he _ hg]
        _ = x * (g⁻¹ * e * g) := by group
    exact mem_normalizer_of_forall E (h.cent _ hyx)
  have hE''p : IsPGroup 2 E'' := by
    have hc : Nat.card E'' = 2 ^ 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, h.E_card]
      norm_num
    exact IsPGroup.of_card hc
  obtain ⟨m, hmN, hm⟩ := exists_mem_conj_le_of_isSylowOf h.sylow_normalizer hE''N hE''p
  have hmain : ∀ e ∈ E, (g * m)⁻¹ * e * (g * m) ∈ E := by
    intro e he
    have hs : m⁻¹ * (g⁻¹ * e * g) * m ∈ S := hm _ ((hE''mem _).2 ⟨e, he, rfl⟩)
    have hs' : (g * m)⁻¹ * e * (g * m) = m⁻¹ * (g⁻¹ * e * g) * m := by group
    have hsS : (g * m)⁻¹ * e * (g * m) ∈ S := by rw [hs']; exact hs
    by_cases h1 : e = 1
    · subst h1
      simp
    by_cases hv : e = v
    · subst hv
      have := h.conj_v (g * m)⁻¹
      rw [inv_inv] at this
      rw [this]; exact h.v_mem
    have heZ : e ∈ Zs := h.Zmem_of_mem_E he h1 hv
    have hZ : (g * m)⁻¹ * e * (g * m) ∈ Zs := h.Z_conj' heZ (g * m)
    exact ((h.Z_inter _ hsS).1 hZ).1
  have hk : (g * m)⁻¹ ∈ N := by
    apply mem_normalizer_of_forall E
    intro e he
    have := hmain e he
    simpa [mul_assoc] using this
  have hgm : g * m ∈ N := by simpa using N.inv_mem hk
  have : g = (g * m) * m⁻¹ := by group
  rw [this]
  exact N.mul_mem hgm (N.inv_mem hmN)

theorem ti_all [Finite C] (h : TIData v Zs S E x) {e g : C} (he : e ∈ E) (heZ : e ∈ Zs)
    (hg : g * e * g⁻¹ ∈ E) : g ∈ normalizer (E : Set C) := by
  obtain ⟨c, hc⟩ := h.Z_single e heZ
  have hcN : c ∈ normalizer (E : Set C) := h.ti_x (by rw [hc]; exact he)
  have hgcN : g * c ∈ normalizer (E : Set C) := by
    apply h.ti_x
    have : g * c * x * (g * c)⁻¹ = g * (c * x * c⁻¹) * g⁻¹ := by group
    rw [this, hc]; exact hg
  have : g = (g * c) * c⁻¹ := by group
  rw [this]
  exact (normalizer (E : Set C)).mul_mem hgcN ((normalizer (E : Set C)).inv_mem hcN)

theorem exists_conj_mem_E [Finite C] (h : TIData v Zs S E x) {z : C} (hzZ : z ∈ Zs)
    (hzN : z ∈ normalizer (E : Set C)) :
    ∃ n ∈ normalizer (E : Set C), n⁻¹ * z * n ∈ E ∧ n⁻¹ * z * n ∈ Zs := by
  obtain ⟨k, hkN, hk⟩ := exists_mem_conj_le_of_isSylowOf h.sylow_normalizer
    (X := zpowers z) (zpowers_le.2 hzN) (isPGroup_zpowers (h.Z_sq z hzZ))
  have hs : k⁻¹ * z * k ∈ S := hk z (mem_zpowers z)
  have hZ : k⁻¹ * z * k ∈ Zs := h.Z_conj' hzZ k
  exact ⟨k, hkN, ((h.Z_inter _ hs).1 hZ).1, hZ⟩

theorem ti_Z [Finite C] (h : TIData v Zs S E x) {z g : C} (hzZ : z ∈ Zs)
    (hzN : z ∈ normalizer (E : Set C)) (hgz : g * z * g⁻¹ ∈ normalizer (E : Set C)) :
    g ∈ normalizer (E : Set C) := by
  obtain ⟨n, hnN, hnE, hnZ⟩ := h.exists_conj_mem_E hzZ hzN
  have hz'Z : g * z * g⁻¹ ∈ Zs := h.Z_conj z hzZ g
  obtain ⟨n', hn'N, hn'E, hn'Z⟩ := h.exists_conj_mem_E hz'Z hgz
  have key : (n'⁻¹ * g * n) * (n⁻¹ * z * n) * (n'⁻¹ * g * n)⁻¹ = n'⁻¹ * (g * z * g⁻¹) * n' := by
    group
  have hmem : n'⁻¹ * g * n ∈ normalizer (E : Set C) :=
    h.ti_all hnE hnZ (by rw [key]; exact hn'E)
  have : g = n' * (n'⁻¹ * g * n) * n⁻¹ := by group
  rw [this]
  exact (normalizer (E : Set C)).mul_mem
    ((normalizer (E : Set C)).mul_mem hn'N hmem) ((normalizer (E : Set C)).inv_mem hnN)

end TIData

end CFSG.GH74.GLS.C3.Layer2.L4
