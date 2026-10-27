module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Lattice

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem gold_mem_normalizer_of_conj_le {W : Subgroup G} {g : G}
    (h : ∀ w ∈ W, g * w * g⁻¹ ∈ W) : g ∈ normalizer (W : Set G) := by
  have hle : W.map (MulAut.conj g).toMonoidHom ≤ W := by
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  have hcard : Nat.card (W.map (MulAut.conj g).toMonoidHom) = Nat.card W :=
    card_map_of_injective (MulAut.conj g).injective
  have heq : W.map (MulAut.conj g).toMonoidHom = W :=
    eq_of_le_of_card_ge hle (by rw [hcard])
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact h x
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := by simpa [MulAut.conj_apply] using hyx
      simpa using h1
    rwa [← this]

theorem gold_exists_conj_le_sylow (T : Sylow 2 G) {X : Subgroup G} (hX : IsPGroup 2 X) :
    ∃ h : G, ∀ x ∈ X, h * x * h⁻¹ ∈ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G Q T
  refine ⟨h, fun x hx => ?_⟩
  have hmem : MulAut.conj h x ∈ ((h • Q : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact smul_mem_pointwise_smul _ _ _ (hQ hx)
  rw [hh] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem gold_exists_conj_le_sylow_of_le {K X : Subgroup G} (hXK : X ≤ K) (hX : IsPGroup 2 X)
    (Q : Sylow 2 K) : ∃ c ∈ K, ∀ x ∈ X, c * x * c⁻¹ ∈ (Q : Subgroup K).map K.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX' : IsPGroup 2 (X.subgroupOf K) := hX.of_equiv (subgroupOfEquivOfLe hXK).symm
  obtain ⟨Q', hQ'⟩ := hX'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K Q' Q
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hXK hx⟩ : K) ∈ (Q' : Subgroup K) := hQ' (mem_subgroupOf.mpr hx)
  have hmem : MulAut.conj c (⟨x, hXK hx⟩ : K) ∈ ((c • Q' : Sylow 2 K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact smul_mem_pointwise_smul _ _ _ hxQ
  rw [hc] at hmem
  exact ⟨_, hmem, by simp [MulAut.conj_apply]⟩

omit [Finite G] in
theorem gold_isPGroup_map {K : Subgroup G} (Q : Sylow 2 K) :
    IsPGroup 2 ((Q : Subgroup K).map K.subtype) :=
  Q.isPGroup'.map K.subtype

theorem gold_mem_of_conj_le (T : Sylow 2 G) {W A : Subgroup G} (hWT : W ≤ T)
    (hW : ∀ g : G, (∀ w ∈ W, g * w * g⁻¹ ∈ (T : Subgroup G)) → ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    (hAW : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a)
    (hAN : ∀ g ∈ normalizer (W : Set G), ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    {X : Set G} (hXW : ∀ x ∈ X, ∀ w ∈ W, x * w = w * x)
    {g : G} (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ A) : ∀ x ∈ X, x ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer X with hCdef
  have hWC : W ≤ C := fun w hw => mem_centralizer_iff.mpr fun x hx => hXW x hx w hw
  set W' := W.map (MulAut.conj g⁻¹).toMonoidHom with hW'def
  have hW'C : W' ≤ C := by
    rintro _ ⟨w, hw, rfl⟩
    refine mem_centralizer_iff.mpr fun x hx => ?_
    have h1 := hAW _ (hg x hx) w hw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc x * (g⁻¹ * w * g) = g⁻¹ * ((g * x * g⁻¹) * w) * g := by group
      _ = g⁻¹ * (w * (g * x * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * w * g * x := by group
  have hWp : IsPGroup 2 W := (T.isPGroup').to_le hWT
  have hW'p : IsPGroup 2 W' := hWp.map _
  have hWp' : IsPGroup 2 (W.subgroupOf C) := hWp.of_equiv (subgroupOfEquivOfLe hWC).symm
  obtain ⟨Q, hQ⟩ := hWp'.exists_le_sylow
  obtain ⟨c, hcC, hc⟩ := gold_exists_conj_le_sylow_of_le hW'C hW'p Q
  obtain ⟨h, hh⟩ := gold_exists_conj_le_sylow T (gold_isPGroup_map Q)
  have hhN : h ∈ normalizer (W : Set G) := by
    refine gold_mem_normalizer_of_conj_le (hW h fun w hw => hh w ?_)
    exact ⟨⟨w, hWC hw⟩, hQ (mem_subgroupOf.mpr hw), rfl⟩
  have hkN : h * c * g⁻¹ ∈ normalizer (W : Set G) := by
    refine gold_mem_normalizer_of_conj_le (hW _ fun w hw => ?_)
    have h1 := hh _ (hc _ ⟨w, hw, rfl⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    rw [show h * c * g⁻¹ * w * (h * c * g⁻¹)⁻¹ = h * (c * (g⁻¹ * w * g) * c⁻¹) * h⁻¹ by group]
    exact h1
  have hcg : c * g⁻¹ ∈ normalizer (W : Set G) := by
    rw [show c * g⁻¹ = h⁻¹ * (h * c * g⁻¹) by group]
    exact mul_mem (inv_mem hhN) hkN
  intro x hx
  have hxc : x * c = c * x := (mem_centralizer_iff.mp hcC) x hx
  have h1 := hAN _ hcg _ (hg x hx)
  rwa [show c * g⁻¹ * (g * x * g⁻¹) * (c * g⁻¹)⁻¹ = x by
    rw [show c * g⁻¹ * (g * x * g⁻¹) * (c * g⁻¹)⁻¹ = c * x * c⁻¹ by group, ← hxc]; group] at h1

theorem gold_9_3_one (T : Sylow 2 G) {W A : Subgroup G} (hWT : W ≤ T)
    (hW : ∀ g : G, (∀ w ∈ W, g * w * g⁻¹ ∈ (T : Subgroup G)) → ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    (hAW : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a)
    (hAN : ∀ g ∈ normalizer (W : Set G), ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    {B : Set G} {g : G} (hg : ∀ b ∈ B, g * b * g⁻¹ ∈ A) {b : G} (hb : b ∈ B) :
    (∀ w ∈ W, b * w = w * b) ↔ b ∈ A := by
  constructor
  · intro hbW
    exact gold_mem_of_conj_le T hWT hW hAW hAN (X := {x | x ∈ B ∧ ∀ w ∈ W, x * w = w * x})
      (fun x hx => hx.2) (g := g) (fun x hx => hg x hx.1) b ⟨hb, hbW⟩
  · exact hAW b

theorem gold_9_3_two (T : Sylow 2 G) {W A : Subgroup G} (hWT : W ≤ T)
    (hW : ∀ g : G, (∀ w ∈ W, g * w * g⁻¹ ∈ (T : Subgroup G)) → ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    (hAW : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a)
    (hAN : ∀ g ∈ normalizer (W : Set G), ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    {B : Subgroup G} {g₀ : G} (hg₀ : ∀ b ∈ B, g₀ * b * g₀⁻¹ ∈ A) :
    ∃ g : G, (∀ b ∈ B, g * b * g⁻¹ ∈ A) ∧
      ∀ x ∈ (T : Subgroup G), x ∈ normalizer (B : Set G) → g * x * g⁻¹ ∈ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (B : Set G) with hNdef
  set X₀ := (T : Subgroup G) ⊓ N with hX₀def
  have hX₀p : IsPGroup 2 (X₀.subgroupOf N) :=
    ((T.isPGroup').to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨Q, hQ⟩ := hX₀p.exists_le_sylow
  set W'' := W.map (MulAut.conj g₀⁻¹).toMonoidHom with hW''def
  have hW''c : ∀ y ∈ W'', ∀ b ∈ B, b * y = y * b := by
    rintro _ ⟨w, hw, rfl⟩ b hb
    have h1 := hAW _ (hg₀ b hb) w hw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc b * (g₀⁻¹ * w * g₀) = g₀⁻¹ * ((g₀ * b * g₀⁻¹) * w) * g₀ := by group
      _ = g₀⁻¹ * (w * (g₀ * b * g₀⁻¹)) * g₀ := by rw [h1]
      _ = g₀⁻¹ * w * g₀ * b := by group
  have hW''N : W'' ≤ N := by
    intro y hy
    rw [hNdef, mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [← hW''c y hy b hb]
      simpa using hb
    · intro hb
      have h1 := hW''c y hy _ hb
      have e : b = y * b * y⁻¹ := by
        have h2 : y * b = y * (y * b * y⁻¹) := by
          calc y * b = y * b * y⁻¹ * y := by group
            _ = y * (y * b * y⁻¹) := h1
        exact mul_left_cancel h2
      rwa [e]
  have hW''p : IsPGroup 2 W'' := ((T.isPGroup').to_le hWT).map _
  obtain ⟨n, hnN, hn⟩ := gold_exists_conj_le_sylow_of_le hW''N hW''p Q
  obtain ⟨h, hh⟩ := gold_exists_conj_le_sylow T (gold_isPGroup_map Q)
  have hkN : h * n * g₀⁻¹ ∈ normalizer (W : Set G) := by
    refine gold_mem_normalizer_of_conj_le (hW _ fun w hw => ?_)
    have h1 := hh _ (hn _ ⟨w, hw, rfl⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    rw [show h * n * g₀⁻¹ * w * (h * n * g₀⁻¹)⁻¹ = h * (n * (g₀⁻¹ * w * g₀) * n⁻¹) * h⁻¹ by
      group]
    exact h1
  have hnB : ∀ b ∈ B, n⁻¹ * b * n ∈ B := by
    intro b hb
    have := (mem_normalizer_iff.mp (inv_mem hnN) b).mp hb
    simpa using this
  have hXW : ∀ x ∈ {x | ∃ b ∈ B, h * b * h⁻¹ = x}, ∀ w ∈ W, x * w = w * x := by
    rintro _ ⟨b, hb, rfl⟩ w hw
    have hw0 : (h * n * g₀⁻¹)⁻¹ * w * (h * n * g₀⁻¹) ∈ W := by
      have := (mem_normalizer_iff.mp (inv_mem hkN) w).mp hw
      simpa using this
    set w₀ := (h * n * g₀⁻¹)⁻¹ * w * (h * n * g₀⁻¹) with hw₀def
    have hww : w = h * (n * (g₀⁻¹ * w₀ * g₀) * n⁻¹) * h⁻¹ := by rw [hw₀def]; group
    have h1 := hW''c _ ⟨w₀, hw0, rfl⟩ _ (hnB b hb)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    rw [hww]
    calc h * b * h⁻¹ * (h * (n * (g₀⁻¹ * w₀ * g₀) * n⁻¹) * h⁻¹) =
          h * n * ((n⁻¹ * b * n) * (g₀⁻¹ * w₀ * g₀)) * n⁻¹ * h⁻¹ := by group
      _ = h * n * ((g₀⁻¹ * w₀ * g₀) * (n⁻¹ * b * n)) * n⁻¹ * h⁻¹ := by rw [h1]
      _ = h * (n * (g₀⁻¹ * w₀ * g₀) * n⁻¹) * h⁻¹ * (h * b * h⁻¹) := by group
  have hXA := gold_mem_of_conj_le T hWT hW hAW hAN hXW (g := g₀ * h⁻¹) (by
    rintro _ ⟨b, hb, rfl⟩
    rw [show g₀ * h⁻¹ * (h * b * h⁻¹) * (g₀ * h⁻¹)⁻¹ = g₀ * b * g₀⁻¹ by group]
    exact hg₀ b hb)
  refine ⟨h, fun b hb => hXA _ ⟨b, hb, rfl⟩, fun x hxT hxN => hh x ?_⟩
  exact ⟨⟨x, hxN⟩, hQ (mem_subgroupOf.mpr ⟨hxT, hxN⟩), rfl⟩

@[expose] def goldCommHom (A : Subgroup G) (t : G) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) : A →* A where
  toFun x := ⟨(x : G) * t * (x : G)⁻¹ * t⁻¹, by
    rw [show (x : G) * t * (x : G)⁻¹ * t⁻¹ = x * (t * (x : G)⁻¹ * t⁻¹) by group]
    exact mul_mem x.2 (htA _ (inv_mem x.2))⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_inv_rev]
    have ha : t * (x : G)⁻¹ * t⁻¹ ∈ A := htA _ (inv_mem x.2)
    have hb : t * (y : G)⁻¹ * t⁻¹ ∈ A := htA _ (inv_mem y.2)
    have e : (y : G) * (t * (y : G)⁻¹ * t⁻¹) * (t * (x : G)⁻¹ * t⁻¹) =
        (t * (x : G)⁻¹ * t⁻¹) * ((y : G) * (t * (y : G)⁻¹ * t⁻¹)) :=
      hAab _ (mul_mem y.2 hb) _ ha
    calc (x : G) * y * t * ((y : G)⁻¹ * (x : G)⁻¹) * t⁻¹ =
          x * ((y : G) * (t * (y : G)⁻¹ * t⁻¹) * (t * (x : G)⁻¹ * t⁻¹)) := by group
      _ = x * ((t * (x : G)⁻¹ * t⁻¹) * ((y : G) * (t * (y : G)⁻¹ * t⁻¹))) := by rw [e]
      _ = x * t * (x : G)⁻¹ * t⁻¹ * (y * t * (y : G)⁻¹ * t⁻¹) := by group

omit [Finite G] in
theorem goldCommHom_apply {A : Subgroup G} {t : G} (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (x : A) :
    ((goldCommHom A t hAab htA x : A) : G) = x * t * (x : G)⁻¹ * t⁻¹ := rfl

omit [Finite G] in
theorem goldCommHom_mem_ker {A : Subgroup G} {t : G} (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (x : A) :
    x ∈ (goldCommHom A t hAab htA).ker ↔ (x : G) * t = t * x := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff, goldCommHom_apply]
  simp only [OneMemClass.coe_one]
  constructor
  · intro h
    calc (x : G) * t = x * t * (x : G)⁻¹ * t⁻¹ * (t * x) := by group
      _ = t * x := by rw [h, one_mul]
  · intro h
    rw [h]; group

theorem gold_card_mul_le {K : Type*} [Group K] [Finite K] (φ : K →* K) (hφ : φ.range ≤ φ.ker)
    {B₁ : Subgroup K} (hB₁ : B₁ ≤ φ.ker) :
    Nat.card K * Nat.card B₁ ≤ Nat.card (B₁.comap φ) * Nat.card φ.ker := by
  have h1 : (B₁.comap φ).index = B₁.relIndex φ.range := index_comap B₁ φ
  have h2 : B₁.relIndex φ.range ≤ B₁.relIndex φ.ker :=
    relIndex_le_of_le_right hφ index_ne_zero_of_finite
  have h3 := relIndex_mul_card (H := B₁) (K := φ.ker)
  rw [inf_of_le_left hB₁] at h3
  have h4 := card_mul_index (B₁.comap φ)
  rw [← h4, mul_assoc, ← h3]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (h1 ▸ h2))

theorem gold_cor4 (T : Sylow 2 G) {W A : Subgroup G} (hWT : W ≤ T)
    (hW : ∀ g : G, (∀ w ∈ W, g * w * g⁻¹ ∈ (T : Subgroup G)) → ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    (hAT : A ≤ T) (hAW : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a)
    (hAN : ∀ g ∈ normalizer (W : Set G), ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    {t : G} (htT : t ∈ (T : Subgroup G)) (htA : t ∉ A) (hconj : ∃ g : G, g * t * g⁻¹ ∈ A) :
    ∃ B : Subgroup G, B ≤ T ∧ ¬ B ≤ A ∧ (∃ g : G, ∀ b ∈ B, g * b * g⁻¹ ∈ A) ∧
      (centralizer ({t} : Set G)).relIndex A ≤ (centralizer (W : Set G)).relIndex B ∧
      Nat.card A ≤ Nat.card B * (centralizer (W : Set G)).relIndex B := by
  classical
  have hTN : ∀ x ∈ (T : Subgroup G), x ∈ normalizer (W : Set G) := fun x hx =>
    gold_mem_normalizer_of_conj_le (hW x fun w hw => mul_mem (mul_mem hx (hWT hw)) (inv_mem hx))
  have htAn : ∀ a ∈ A, t * a * t⁻¹ ∈ A := hAN t (hTN t htT)
  obtain ⟨g₀, hg₀⟩ := hconj
  have ht2 : t * t = 1 := by
    have h1 : g₀ * t * g₀⁻¹ * (g₀ * t * g₀⁻¹) = 1 := by rw [← sq]; exact hA2 _ hg₀
    calc t * t = g₀⁻¹ * (g₀ * t * g₀⁻¹ * (g₀ * t * g₀⁻¹)) * g₀ := by group
      _ = 1 := by rw [h1]; group
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  let B₁ : G → Subgroup G := fun g => A ⊓ A.comap (MulAut.conj g).toMonoidHom
  have mem_B₁ : ∀ g x, x ∈ B₁ g ↔ x ∈ A ∧ g * x * g⁻¹ ∈ A := fun g x => by
    simp only [B₁, mem_inf, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hB₁A : ∀ g, B₁ g ≤ A := fun g => inf_le_left
  have : Nonempty {g : G // g * t * g⁻¹ ∈ A} := ⟨⟨g₀, hg₀⟩⟩
  obtain ⟨⟨g, hg⟩, hmax⟩ :=
    Finite.exists_max (fun g : {g : G // g * t * g⁻¹ ∈ A} => Nat.card (B₁ g.1))
  have hmax' : ∀ g' : G, g' * t * g'⁻¹ ∈ A → Nat.card (B₁ g') ≤ Nat.card (B₁ g) :=
    fun g' hg' => hmax ⟨g', hg'⟩
  have hB₁t : ∀ x ∈ B₁ g, x * t = t * x := by
    intro x hx
    obtain ⟨-, hgx⟩ := (mem_B₁ g x).mp hx
    have h1 := hAab _ hgx _ hg
    have h2 : g * (x * t) * g⁻¹ = g * (t * x) * g⁻¹ := by
      calc g * (x * t) * g⁻¹ = g * x * g⁻¹ * (g * t * g⁻¹) := by group
        _ = g * t * g⁻¹ * (g * x * g⁻¹) := h1
        _ = g * (t * x) * g⁻¹ := by group
    simpa using h2
  set φ := goldCommHom A t hAab htAn with hφdef
  have hφ : ∀ x : A, ((φ x : A) : G) = x * t * (x : G)⁻¹ * t⁻¹ := goldCommHom_apply hAab htAn
  have hker : ∀ x : A, x ∈ φ.ker ↔ (x : G) * t = t * x := goldCommHom_mem_ker hAab htAn
  have hφA : ∀ x : A, (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ A := fun x => by
    rw [← hφ]; exact (φ x).2
  have hrange : φ.range ≤ φ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hker, hφ]
    set y := (x : G) * t * (x : G)⁻¹ * t⁻¹ with hydef
    have hy2 : y * y = 1 := by rw [← sq]; exact hA2 _ (hφA x)
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have e : t * y * t⁻¹ = y⁻¹ := by
      rw [hydef]
      calc t * ((x : G) * t * (x : G)⁻¹ * t⁻¹) * t⁻¹ =
            t * x * t * (x : G)⁻¹ * (t⁻¹ * t⁻¹) := by group
        _ = t * x * t * (x : G)⁻¹ := by rw [htinv, ht2, mul_one]
        _ = t * x * t⁻¹ * (x : G)⁻¹ := by rw [htinv]
        _ = ((x : G) * t * (x : G)⁻¹ * t⁻¹)⁻¹ := by group
    rw [hyinv] at e
    calc y * t = (t * y * t⁻¹) * t := by rw [e]
      _ = t * y := by group
  set B₁' : Subgroup A := (B₁ g).subgroupOf A with hB₁'def
  have hB₁'ker : B₁' ≤ φ.ker := fun x hx => (hker x).mpr (hB₁t _ (mem_subgroupOf.mp hx))
  set B₂' : Subgroup A := B₁'.comap φ with hB₂'def
  have hcount := gold_card_mul_le φ hrange hB₁'ker
  have hkerB₂ : φ.ker ≤ B₂' := fun x hx => by
    rw [hB₂'def, mem_comap, (MonoidHom.mem_ker).mp hx]; exact one_mem _
  set B₂ : Subgroup G := B₂'.map A.subtype with hB₂def
  have mem_B₂ : ∀ x, x ∈ B₂ ↔ x ∈ A ∧ x * t * x⁻¹ * t⁻¹ ∈ B₁ g := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have h1 : φ y ∈ B₁' := mem_comap.mp hy
      show (y : G) * t * (y : G)⁻¹ * t⁻¹ ∈ B₁ g
      rw [← hφ]; exact mem_subgroupOf.mp h1
    · rintro ⟨hxA, hx⟩
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      show (⟨x, hxA⟩ : A) ∈ B₁'.comap φ
      rw [mem_comap, hB₁'def, mem_subgroupOf, hφ]; exact hx
  have hB₁B₂ : B₁ g ≤ B₂ := fun x hx => (mem_B₂ x).mpr ⟨hB₁A g hx, by
    rw [hB₁t x hx, show t * x * x⁻¹ * t⁻¹ = 1 by group]; exact one_mem _⟩
  set X := B₁ g ⊔ zpowers t with hXdef
  have hgX : ∀ y ∈ X, g * y * g⁻¹ ∈ A := by
    have hle : X ≤ A.comap (MulAut.conj g).toMonoidHom :=
      sup_le inf_le_right (zpowers_le.mpr (by simpa [MulAut.conj_apply] using hg))
    intro y hy
    simpa [MulAut.conj_apply] using hle hy
  obtain ⟨g₁, hg₁A, hg₁T⟩ := gold_9_3_two T hWT hW hAW hAN hgX
  have hg₁t : g₁ * t * g₁⁻¹ ∈ A := hg₁A t (mem_sup_right (mem_zpowers t))
  have hB₁le : B₁ g ≤ B₁ g₁ := fun x hx =>
    (mem_B₁ g₁ x).mpr ⟨hB₁A g hx, hg₁A x (mem_sup_left hx)⟩
  have hB₁eq : B₁ g₁ = B₁ g := (eq_of_le_of_card_ge hB₁le (hmax' g₁ hg₁t)).symm
  have hB₂N : ∀ x ∈ B₂, x ∈ normalizer (X : Set G) := by
    intro x hx
    obtain ⟨hxA, hxt⟩ := (mem_B₂ x).mp hx
    apply gold_mem_normalizer_of_conj_le
    have hle : X ≤ X.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun b hb => ?_) (zpowers_le.mpr ?_)
      · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show x * b * x⁻¹ = b by rw [hAab x hxA b (hB₁A g hb)]; group]
        exact mem_sup_left hb
      · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t by group]
        exact mul_mem (mem_sup_left hxt) (mem_sup_right (mem_zpowers t))
    intro y hy
    simpa [MulAut.conj_apply] using hle hy
  have hex : ∃ x ∈ B₂, x ∉ B₁ g := by
    by_cases hc : ∃ x ∈ A, x * t = t * x ∧ x ∉ B₁ g
    · obtain ⟨x, hxA, hxt, hxB⟩ := hc
      refine ⟨x, (mem_B₂ x).mpr ⟨hxA, ?_⟩, hxB⟩
      rw [show x * t * x⁻¹ * t⁻¹ = 1 by rw [hxt]; group]
      exact one_mem _
    · push Not at hc
      by_contra hall
      push Not at hall
      have hAB : ∀ a ∈ A, a ∈ B₁ g := by
        intro a ha
        apply hall
        refine (mem_B₂ a).mpr ⟨ha, ?_⟩
        have h1 : φ ⟨a, ha⟩ ∈ φ.ker := hrange ⟨⟨a, ha⟩, rfl⟩
        rw [hker, hφ] at h1
        exact hc _ (hφA ⟨a, ha⟩) h1
      have hgN : g ∈ normalizer (A : Set G) :=
        gold_mem_normalizer_of_conj_le fun a ha => ((mem_B₁ g a).mp (hAB a ha)).2
      exact htA ((mem_normalizer_iff.mp hgN t).mpr hg)
  set B := B₂.map (MulAut.conj g₁).toMonoidHom with hBdef
  have mem_B : ∀ y, y ∈ B ↔ ∃ x ∈ B₂, g₁ * x * g₁⁻¹ = y := fun y => by
    simp [hBdef, MulAut.conj_apply]
  have hBA : ∀ b ∈ B, g₁⁻¹ * b * g₁⁻¹⁻¹ ∈ A := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := (mem_B b).mp hb
    rw [show g₁⁻¹ * (g₁ * x * g₁⁻¹) * g₁⁻¹⁻¹ = x by group]
    exact ((mem_B₂ x).mp hx).1
  have hCB : centralizer (W : Set G) ⊓ B = (B₁ g).map (MulAut.conj g₁).toMonoidHom := by
    ext y
    simp only [mem_inf, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨hyW, hyB⟩
      obtain ⟨x, hx, rfl⟩ := (mem_B _).mp hyB
      have hyA : g₁ * x * g₁⁻¹ ∈ A := by
        refine (gold_9_3_one T hWT hW hAW hAN (B := (B : Set G)) hBA hyB).mp ?_
        intro w hw
        exact ((mem_centralizer_iff.mp hyW) w hw).symm
      refine ⟨x, ?_, rfl⟩
      rw [← hB₁eq]
      exact (mem_B₁ g₁ x).mpr ⟨((mem_B₂ x).mp hx).1, hyA⟩
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ B₁ g₁ := hB₁eq ▸ hx
      refine ⟨mem_centralizer_iff.mpr fun w hw => ?_, (mem_B _).mpr ⟨x, hB₁B₂ hx, rfl⟩⟩
      exact (hAW _ ((mem_B₁ g₁ x).mp hx').2 w hw).symm
  have hCA : centralizer ({t} : Set G) ⊓ A = φ.ker.map A.subtype := by
    ext y
    constructor
    · rintro ⟨hyt, hyA⟩
      refine ⟨⟨y, hyA⟩, (hker _).mpr ?_, rfl⟩
      exact mem_centralizer_singleton_iff.mp hyt
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_centralizer_singleton_iff.mpr ((hker x).mp hx), x.2⟩
  have cB₁ : Nat.card B₁' = Nat.card (B₁ g) := Nat.card_congr (subgroupOfEquivOfLe (hB₁A g)).toEquiv
  have cB₂ : Nat.card B₂ = Nat.card B₂' := card_map_of_injective A.subtype_injective
  have cB : Nat.card B = Nat.card B₂ := card_map_of_injective (MulAut.conj g₁).injective
  have cCB : Nat.card (centralizer (W : Set G) ⊓ B : Subgroup G) = Nat.card (B₁ g) := by
    rw [hCB]; exact card_map_of_injective (MulAut.conj g₁).injective
  have cCA : Nat.card (centralizer ({t} : Set G) ⊓ A : Subgroup G) = Nat.card φ.ker := by
    rw [hCA]; exact card_map_of_injective A.subtype_injective
  have rA := relIndex_mul_card (H := centralizer ({t} : Set G)) (K := A)
  have rB := relIndex_mul_card (H := centralizer (W : Set G)) (K := B)
  rw [cCA] at rA
  rw [cCB, cB, cB₂] at rB
  rw [cB₁] at hcount
  have hker_le : Nat.card φ.ker ≤ Nat.card B₂' := card_le_of_le hkerB₂
  have hpos1 : 0 < Nat.card φ.ker := Nat.card_pos
  have hpos2 : 0 < Nat.card (B₁ g) := Nat.card_pos
  refine ⟨B, ?_, ?_, ⟨g₁⁻¹, hBA⟩, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_B y).mp hy
    exact hg₁T x (hAT ((mem_B₂ x).mp hx).1) (hB₂N x hx)
  · intro hle
    obtain ⟨x, hxB₂, hxB₁⟩ := hex
    apply hxB₁
    rw [← hB₁eq]
    exact (mem_B₁ g₁ x).mpr ⟨((mem_B₂ x).mp hxB₂).1, hle ((mem_B _).mpr ⟨x, hxB₂, rfl⟩)⟩
  ·
    set rt := (centralizer ({t} : Set G)).relIndex A
    set rw := (centralizer (W : Set G)).relIndex B
    have h1 : rt * (Nat.card φ.ker * Nat.card (B₁ g)) ≤ rw * (Nat.card φ.ker * Nat.card (B₁ g)) := by
      calc rt * (Nat.card φ.ker * Nat.card (B₁ g)) = Nat.card A * Nat.card (B₁ g) := by
            rw [← rA]; ring
        _ ≤ Nat.card B₂' * Nat.card φ.ker := hcount
        _ = rw * (Nat.card φ.ker * Nat.card (B₁ g)) := by rw [← rB]; ring
    exact Nat.le_of_mul_le_mul_right h1 (Nat.mul_pos hpos1 hpos2)
  ·
    rw [cB, cB₂]
    set rw := (centralizer (W : Set G)).relIndex B
    have h1 : Nat.card A * Nat.card (B₁ g) ≤ (Nat.card B₂' * rw) * Nat.card (B₁ g) := by
      calc Nat.card A * Nat.card (B₁ g) ≤ Nat.card B₂' * Nat.card φ.ker := hcount
        _ ≤ Nat.card B₂' * Nat.card B₂' := Nat.mul_le_mul_left _ hker_le
        _ = (Nat.card B₂' * rw) * Nat.card (B₁ g) := by rw [← rB]; ring
    exact Nat.le_of_mul_le_mul_right h1 hpos2

theorem gold_cor4_self (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ T)
    (hA : ∀ g : G, (∀ a ∈ A, g * a * g⁻¹ ∈ (T : Subgroup G)) → ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    (∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (T : Subgroup G) → g⁻¹ * a * g ∈ A) ∨
      ((∃ t ∈ (T : Subgroup G), t ∉ A ∧ ∃ g : G, g * t * g⁻¹ ∈ A) ∧
        ∀ t ∈ (T : Subgroup G), t ∉ A → (∃ g : G, g * t * g⁻¹ ∈ A) →
          ∃ B : Subgroup G, B ≤ T ∧ ¬ B ≤ A ∧ (∃ g : G, ∀ b ∈ B, g * b * g⁻¹ ∈ A) ∧
            (centralizer ({t} : Set G)).relIndex A ≤ (centralizer (A : Set G)).relIndex B ∧
            Nat.card A ≤ Nat.card B * (centralizer (A : Set G)).relIndex B) := by
  have hAN : ∀ g ∈ normalizer (A : Set G), ∀ a ∈ A, g * a * g⁻¹ ∈ A :=
    fun g hg a ha => (mem_normalizer_iff.mp hg a).mp ha
  by_cases hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (T : Subgroup G) → g⁻¹ * a * g ∈ A
  · exact Or.inl hcl
  · refine Or.inr ⟨?_, fun t ht htA hc => gold_cor4 T hAT hA hAT hAab hAN hAab hA2 ht htA hc⟩
    push Not at hcl
    obtain ⟨a, ha, g, hgT, hgA⟩ := hcl
    exact ⟨_, hgT, hgA, g, by rw [show g * (g⁻¹ * a * g) * g⁻¹ = a by group]; exact ha⟩

end CFSG.SeitzReduction.RankOne
