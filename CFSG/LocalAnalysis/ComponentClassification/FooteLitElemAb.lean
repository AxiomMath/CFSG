module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public section

namespace CFSG.ComponentClassification.FooteLit

open Subgroup

variable {G : Type*} [Group G]

theorem card_sup_zpowers_eq [Finite G] {W : Subgroup G} {x : G} (hxW : x ∉ W) (hx2 : x ^ 2 = 1)
    (hcomm : ∀ w ∈ W, w * x = x * w) : Nat.card ↥(W ⊔ zpowers x) = 2 * Nat.card W := by
  have hx1 : x ≠ 1 := fun h => hxW (h ▸ one_mem W)
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hc : ∀ (w : W) (c : zpowers x), Commute (W.subtype w) ((zpowers x).subtype c) := by
    rintro w ⟨c, k, rfl⟩
    exact (Commute.zpow_right (hcomm w w.2) k)
  set f : W × zpowers x →* G := MonoidHom.noncommCoprod W.subtype (zpowers x).subtype hc with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨w, c⟩ hwc
    have h1 : (w : G) * c = 1 := hwc
    have hcW : (c : G) ∈ W := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem w.2
    have hc1 : c = 1 := by
      obtain ⟨c, k, rfl⟩ := c
      by_contra hne
      apply hxW
      rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exfalso
        apply hne
        apply Subtype.ext
        show x ^ (j + j) = 1
        rw [← two_mul, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hx2,
          one_zpow]
      · have h2 : x ^ (2 * j + 1) = x := by
          rw [zpow_add, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hx2,
            one_zpow, one_mul, zpow_one]
        rw [← h2]
        exact hcW
    have hw1 : w = 1 := by
      apply Subtype.ext
      rw [hc1, OneMemClass.coe_one, mul_one] at h1
      exact h1
    rw [hw1, hc1]
    rfl
  have hrange : f.range = W ⊔ zpowers x := by
    rw [hf, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod,
    Nat.card_zpowers, hord, mul_comm]

theorem isKleinFour_of_card_eq_four {W : Subgroup G} (h4 : Nat.card W = 4)
    (h2 : ∀ x ∈ W, x ^ 2 = 1) : IsKleinFour W := by
  refine ⟨h4, ?_⟩
  have hsq : ∀ x : W, x ^ 2 = 1 := fun x => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact h2 x x.2)
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton W := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : W)
    omega
  · exact h

theorem mem_of_isKleinFour {W : Subgroup G} (hW : IsKleinFour W) {w x y : G} (hw : w ∈ W)
    (hx : x ∈ W) (hy : y ∈ W) (hw1 : w ≠ 1) (hx1 : x ≠ 1) (hwx : w ≠ x) :
    y = 1 ∨ y = w ∨ y = x ∨ y = w * x := by
  have : IsKleinFour W := hW
  by_cases hy1 : y = 1
  · exact Or.inl hy1
  by_cases hyw : y = w
  · exact Or.inr (Or.inl hyw)
  by_cases hyx : y = x
  · exact Or.inr (Or.inr (Or.inl hyx))
  right; right; right
  have h := IsKleinFour.eq_mul_of_ne_all (G := W) (x := ⟨w, hw⟩) (y := ⟨x, hx⟩) (z := ⟨y, hy⟩)
    (fun h => hw1 (congrArg Subtype.val h)) (fun h => hx1 (congrArg Subtype.val h))
    (fun h => hwx (congrArg Subtype.val h)) (fun h => hy1 (congrArg Subtype.val h))
    (fun h => hyw (congrArg Subtype.val h)) (fun h => hyx (congrArg Subtype.val h))
  exact congrArg Subtype.val h

theorem sq_eq_one_of_isKleinFour {W : Subgroup G} (hW : IsKleinFour W) {x : G} (hx : x ∈ W) :
    x ^ 2 = 1 := by
  have h := IsKleinFour.mul_self (G := W) ⟨x, hx⟩
  rw [sq]
  exact congrArg Subtype.val h

theorem commute_of_sq_eq_one {B : Subgroup G} (hB : ∀ x ∈ B, x ^ 2 = 1) {x y : G} (hx : x ∈ B)
    (hy : y ∈ B) : x * y = y * x := by
  have h1 : ∀ z ∈ B, z⁻¹ = z := fun z hz => inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hB z hz)
  calc x * y = (x * y)⁻¹ := (h1 _ (mul_mem hx hy)).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [h1 y hy, h1 x hx]

theorem isMulCommutative_of_sq_eq_one {B : Subgroup G} (hB : ∀ x ∈ B, x ^ 2 = 1) :
    IsMulCommutative B :=
  ⟨⟨fun x y => Subtype.ext (commute_of_sq_eq_one hB x.2 y.2)⟩⟩

theorem sq_eq_one_of_mem_sup {H K : Subgroup G} (hH : ∀ x ∈ H, x ^ 2 = 1)
    (hK : ∀ x ∈ K, x ^ 2 = 1) (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    ∀ g ∈ H ⊔ K, g ^ 2 = 1 := by
  have hHK : H ≤ normalizer (K : Set G) := fun x hx => mem_normalizer_iff.mpr fun y => by
    constructor
    · intro hy
      rw [show x * y * x⁻¹ = y by rw [hc x hx y hy]; group]
      exact hy
    · intro hy
      have h := hc x hx _ hy
      have e : y = x * y * x⁻¹ := by
        calc y = x⁻¹ * (x * y * x⁻¹ * x) := by group
          _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [h]
          _ = x * y * x⁻¹ := by group
      rw [e]
      exact hy
  intro g hg
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right H K hHK] at hg
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  rw [sq, show a * b * (a * b) = a * (b * a) * b by group, ← hc a ha b hb,
    show a * (a * b) * b = (a * a) * (b * b) by group, ← sq, ← sq, hH a ha, hK b hb, one_mul]

theorem sq_eq_one_of_mem_zpowers {x : G} (hx2 : x ^ 2 = 1) {y : G} (hy : y ∈ zpowers x) :
    y ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]

theorem sup_zpowers_spec [Finite G] {W : Subgroup G} (hW : IsKleinFour W) {x : G} (hxW : x ∉ W)
    (hx2 : x ^ 2 = 1) (hcomm : ∀ w ∈ W, w * x = x * w) :
    (∀ g ∈ W ⊔ zpowers x, g ^ 2 = 1) ∧ Nat.card ↥(W ⊔ zpowers x) = 8 := by
  refine ⟨sq_eq_one_of_mem_sup (fun y hy => sq_eq_one_of_isKleinFour hW hy)
    (fun y hy => sq_eq_one_of_mem_zpowers hx2 hy) fun w hw y hy => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (hcomm w hw) k).eq
  · rw [card_sup_zpowers_eq hxW hx2 hcomm, hW.card_four]

theorem eq_of_mem_zpowers_of_sq {x y : G} (hx2 : x ^ 2 = 1) (hy1 : y ≠ 1) (hy : y ∈ zpowers x) :
    y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exfalso
    apply hy1
    rw [← two_mul, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hx2,
      one_zpow]
  · rw [zpow_add, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hx2,
      one_zpow, one_mul, zpow_one]

theorem isKleinFour_sup_zpowers [Finite G] {x y : G} (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : y ≠ x) (hc : x * y = y * x) :
    IsKleinFour ↥(zpowers x ⊔ zpowers y) := by
  have hyx : y ∉ zpowers x := fun h => hxy (eq_of_mem_zpowers_of_sq hx2 hy1 h)
  have hcomm : ∀ w ∈ zpowers x, w * y = y * w := fun w hw => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact (Commute.zpow_left hc k).eq
  refine isKleinFour_of_card_eq_four ?_ (sq_eq_one_of_mem_sup
    (fun z hz => sq_eq_one_of_mem_zpowers hx2 hz) (fun z hz => sq_eq_one_of_mem_zpowers hy2 hz)
    fun a ha b hb => ?_)
  · rw [card_sup_zpowers_eq hyx hy2 hcomm, Nat.card_zpowers, orderOf_eq_prime hx2 hx1]
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (hcomm a ha) k).eq

theorem exists_isKleinFour_le [Finite G] {B : Subgroup G} (hB2 : ∀ x ∈ B, x ^ 2 = 1)
    (hB4 : 4 ≤ Nat.card B) : ∃ W : Subgroup G, IsKleinFour W ∧ W ≤ B := by
  classical
  have hex : ∀ a : G, ∃ b ∈ B, b ≠ 1 ∧ b ≠ a := by
    intro a
    by_contra hall
    push Not at hall
    have hsub : (B : Set G) ⊆ {1, a} := fun b hb => by
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      · exact Or.inr (hall b hb hb1)
    have h1 : (B : Set G).ncard ≤ ({1, a} : Set G).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, a} : Set G).ncard ≤ 2 := by
      have := Set.ncard_insert_le (1 : G) ({a} : Set G)
      rwa [Set.ncard_singleton] at this
    have h3 : (B : Set G).ncard = Nat.card B := Nat.card_coe_set_eq _
    omega
  obtain ⟨x, hx, hx1, -⟩ := hex 1
  obtain ⟨y, hy, hy1, hyx⟩ := hex x
  refine ⟨_, isKleinFour_sup_zpowers (hB2 x hx) (hB2 y hy) hx1 hy1 hyx
    (commute_of_sq_eq_one hB2 hx hy), sup_le (zpowers_le.mpr hx) (zpowers_le.mpr hy)⟩

theorem exists_card_eight_mem [Finite G] {F : Subgroup G} (hF2 : ∀ x ∈ F, x ^ 2 = 1)
    (hF8 : Nat.card F = 8) {x : G} (hx2 : x ^ 2 = 1) (hxF : ∀ f ∈ F, f * x = x * f) :
    ∃ F' : Subgroup G, (∀ y ∈ F', y ^ 2 = 1) ∧ Nat.card F' = 8 ∧ x ∈ F' ∧
      F' ≤ F ⊔ zpowers x := by
  by_cases hx : x ∈ F
  · exact ⟨F, hF2, hF8, hx, le_sup_left⟩
  obtain ⟨W, hW, hWF⟩ := exists_isKleinFour_le hF2 (by rw [hF8]; norm_num)
  have hxW : x ∉ W := fun h => hx (hWF h)
  obtain ⟨h2, h8⟩ := sup_zpowers_spec hW hxW hx2 fun w hw => hxF w (hWF hw)
  exact ⟨_, h2, h8, mem_sup_right (mem_zpowers x), sup_le_sup_right hWF _⟩

theorem eq_of_isKleinFour_of_commute [Finite G] {α : Type*} (𝓜 : Subgroup G → α) {R : Subgroup G}
    (h𝓜 : ∀ F W : Subgroup G, F ≤ R → (∀ x ∈ F, x ^ 2 = 1) → Nat.card F = 8 →
      IsKleinFour W → W ≤ F → 𝓜 F = 𝓜 W)
    {W U : Subgroup G} (hW : IsKleinFour W) (hU : IsKleinFour U) (hWR : W ≤ R) (hUR : U ≤ R)
    (hWU : ∀ w ∈ W, ∀ u ∈ U, w * u = u * w) : 𝓜 W = 𝓜 U := by
  by_cases hUW : U ≤ W
  · have heq : U = W := Subgroup.eq_of_le_of_card_ge hUW (by rw [hW.card_four, hU.card_four])
    rw [heq]
  have hWU' : ¬ W ≤ U := fun h => hUW (Subgroup.eq_of_le_of_card_ge h
    (by rw [hW.card_four, hU.card_four])).ge
  obtain ⟨u, hu, huW⟩ := IsConcreteLE.not_le_iff_exists.mp hUW
  obtain ⟨w, hw, hwU⟩ := IsConcreteLE.not_le_iff_exists.mp hWU'
  have hu2 := sq_eq_one_of_isKleinFour hU hu
  have hw2 := sq_eq_one_of_isKleinFour hW hw
  have hu1 : u ≠ 1 := fun h => huW (h ▸ one_mem W)
  have hw1 : w ≠ 1 := fun h => hwU (h ▸ one_mem U)
  have hwu : u ≠ w := fun h => hwU (h ▸ hu)
  obtain ⟨hF₁2, hF₁8⟩ := sup_zpowers_spec hW huW hu2 fun w' hw' => hWU w' hw' u hu
  have hwU2 : w ∉ U := hwU
  obtain ⟨hF₂2, hF₂8⟩ := sup_zpowers_spec hU hwU2 hw2 fun u' hu' => (hWU w hw u' hu').symm
  have hX := isKleinFour_sup_zpowers hw2 hu2 hw1 hu1 hwu (hWU w hw u hu)
  have hR₁ : W ⊔ zpowers u ≤ R := sup_le hWR (zpowers_le.mpr (hUR hu))
  have hR₂ : U ⊔ zpowers w ≤ R := sup_le hUR (zpowers_le.mpr (hWR hw))
  have hX₁ : zpowers w ⊔ zpowers u ≤ W ⊔ zpowers u := sup_le_sup_right (zpowers_le.mpr hw) _
  have hX₂ : zpowers w ⊔ zpowers u ≤ U ⊔ zpowers w := by
    rw [sup_comm (zpowers w) (zpowers u)]
    exact sup_le_sup_right (zpowers_le.mpr hu) _
  calc 𝓜 W = 𝓜 (W ⊔ zpowers u) := (h𝓜 _ _ hR₁ hF₁2 hF₁8 hW le_sup_left).symm
    _ = 𝓜 (zpowers w ⊔ zpowers u) := h𝓜 _ _ hR₁ hF₁2 hF₁8 hX hX₁
    _ = 𝓜 (U ⊔ zpowers w) := (h𝓜 _ _ hR₂ hF₂2 hF₂8 hX hX₂).symm
    _ = 𝓜 U := h𝓜 _ _ hR₂ hF₂2 hF₂8 hU le_sup_left

theorem card_le_two_mul_card_inf_centralizer_of_or [Finite G] {H : Subgroup G} {x y : G}
    (h : ∀ g ∈ H, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = y) :
    Nat.card H ≤ 2 * Nat.card ↥(H ⊓ centralizer ({x} : Set G)) := by
  classical
  have hmemC : ∀ g : G, g ∈ centralizer ({x} : Set G) ↔ g * x * g⁻¹ = x := fun g => by
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hg; rw [hg]; group
    · intro hg
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [hg]
  by_cases hall : ∀ g ∈ H, g * x * g⁻¹ = x
  · have hle : H ≤ H ⊓ centralizer ({x} : Set G) := fun g hg =>
      mem_inf.mpr ⟨hg, (hmemC g).mpr (hall g hg)⟩
    have := Subgroup.card_le_of_le hle
    omega
  push Not at hall
  obtain ⟨g₀, hg₀, hg₀x⟩ := hall
  have hg₀y : g₀ * x * g₀⁻¹ = y := (h g₀ hg₀).resolve_left hg₀x
  set C := H ⊓ centralizer ({x} : Set G) with hC
  have hsub : (H : Set G) ⊆ (C : Set G) ∪ (fun z => g₀ * z) '' (C : Set G) := by
    intro g hg
    rcases h g hg with hgx | hgx
    · exact Or.inl (mem_inf.mpr ⟨hg, (hmemC g).mpr hgx⟩)
    · right
      refine ⟨g₀⁻¹ * g, mem_inf.mpr ⟨mul_mem (inv_mem hg₀) hg, ?_⟩, by simp⟩
      rw [hmemC]
      calc g₀⁻¹ * g * x * (g₀⁻¹ * g)⁻¹ = g₀⁻¹ * (g * x * g⁻¹) * g₀ := by group
        _ = g₀⁻¹ * (g₀ * x * g₀⁻¹) * g₀ := by rw [hgx, hg₀y]
        _ = x := by group
  have hfin : ((C : Set G) ∪ (fun z => g₀ * z) '' (C : Set G)).Finite :=
    (Set.toFinite (C : Set G)).union ((Set.toFinite (C : Set G)).image _)
  calc Nat.card H = (H : Set G).ncard := (Nat.card_coe_set_eq _)
    _ ≤ ((C : Set G) ∪ (fun z => g₀ * z) '' (C : Set G)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (C : Set G).ncard + ((fun z => g₀ * z) '' (C : Set G)).ncard := Set.ncard_union_le _ _
    _ = 2 * Nat.card C := by
      rw [Set.ncard_image_of_injective _ (mul_right_injective g₀), ← Nat.card_coe_set_eq,
        two_mul]
      rfl

end CFSG.ComponentClassification.FooteLit
