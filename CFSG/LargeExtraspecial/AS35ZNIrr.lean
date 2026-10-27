module

public import CFSG.LargeExtraspecial.AS35ZUBasic
public import CFSG.LargeExtraspecial.AS35ZNIrrPG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Fischer.Classification.Unitary

namespace AS35Z

variable {L : Type} [Group L] {D : Set L} {k : ℕ}

theorem two_pow_le_card_of_normalized_L (hD : AS35L.IsTClass D) (hk : 2 ≤ k)
    (ψ : L ⧸ center L ≃* PG (k + 2))
    (hZ : ∀ u ∈ center L, ∀ j : ℕ, u ^ 2 ^ j = 1 → u = 1)
    {t : L} (ht : t ∈ D) {Y : Subgroup L} (hY2 : IsPGroup 2 Y) (htY : t ∈ Y)
    (hYc : ∀ y ∈ Y, y * t = t * y)
    (hYn : ∀ g : L, g * t * g⁻¹ = t → ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hne : ∃ y ∈ Y, y ≠ 1 ∧ y ≠ t) : 2 ^ (2 * k + 1) ≤ Nat.card Y := by
  have hm : 3 ≤ k + 2 := by omega
  set f : L →* PG (k + 2) := ψ.toMonoidHom.comp (QuotientGroup.mk' (center L)) with hf
  have hfx : ∀ x, f x = ψ (QuotientGroup.mk x) := fun _ => rfl
  have hker : ∀ y ∈ Y, f y = 1 → y = 1 := by
    intro y hy h1
    have hyZ : y ∈ center L := by
      rw [← QuotientGroup.eq_one_iff]
      exact ψ.injective (by rw [← hfx, h1, map_one])
    obtain ⟨j, hj⟩ := hY2 ⟨y, hy⟩
    exact hZ y hyZ j (congrArg Subtype.val hj)
  have hinj : Set.InjOn f Y := by
    intro a ha b hb hab
    have h1 := hker (a⁻¹ * b) (Y.mul_mem (Y.inv_mem ha) hb) (by
      rw [map_mul, map_inv, hab, inv_mul_cancel])
    rw [← mul_inv_cancel_left a b, h1, mul_one]
  have htD := hD.mem_DG hk ψ ht
  obtain ⟨w, hw0, hw, hwt⟩ := htD
  have hcls := DG_eq_isConj hm (v₀_ne_zero (n := k)) herm_v₀_v₀
  have htv : f t ∈ DG (k + 2) := ⟨w, hw0, hw, hwt⟩
  rw [hcls] at htv
  obtain ⟨c₀, hc₀⟩ := isConj_iff.1 (show IsConj (tq (v₀ k)) (f t) from htv)
  set φ : PG (k + 2) →* PG (k + 2) := (MulAut.conj c₀⁻¹).toMonoidHom with hφ
  have hφx : ∀ x, φ x = c₀⁻¹ * x * c₀ := fun x => by simp [hφ]
  have hφt : φ (f t) = tq (v₀ k) := by rw [hφx, ← hc₀]; group
  set Yb : Subgroup (PG (k + 2)) := (Y.map f).map φ with hYb
  have hmem : ∀ x, x ∈ Yb ↔ ∃ y ∈ Y, φ (f y) = x := by
    intro x
    simp only [hYb, Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨f y, ⟨y, hy, rfl⟩, rfl⟩
  have hbound := two_pow_le_card_of_normalized hk (Y := Yb) (hY2.map _ |>.map _)
    ((hmem _).2 ⟨t, htY, hφt⟩)
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := (hmem x).1 hx
      rw [← hφt, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hYc y hy])
    (by
      intro c hc x hx
      obtain ⟨y, hy, rfl⟩ := (hmem x).1 hx
      have hc' : (c₀ * c * c₀⁻¹) * f t = f t * (c₀ * c * c₀⁻¹) := by
        rw [← hc₀]
        calc c₀ * c * c₀⁻¹ * (c₀ * tq (v₀ k) * c₀⁻¹) = c₀ * (c * tq (v₀ k)) * c₀⁻¹ := by group
          _ = c₀ * (tq (v₀ k) * c) * c₀⁻¹ := by rw [hc]
          _ = c₀ * tq (v₀ k) * c₀⁻¹ * (c₀ * c * c₀⁻¹) := by group
      obtain ⟨g, hgt, hgc⟩ := hD.exists_lift_centralizer hk ψ ht (c := c₀ * c * c₀⁻¹)
        (by rw [← hfx]; exact hc')
      refine (hmem _).2 ⟨g * y * g⁻¹, hYn g hgt y hy, ?_⟩
      rw [hφx, hφx, map_mul, map_mul, map_inv, hfx g, hgc]
      group)
    (by
      obtain ⟨y, hy, hy1, hyt⟩ := hne
      refine ⟨φ (f y), (hmem _).2 ⟨y, hy, rfl⟩, fun h1 => hy1 ?_, fun h2 => hyt ?_⟩
      · have h1' : f y = 1 := by
          have := congrArg (fun x => c₀ * x * c₀⁻¹) h1
          simp only [hφx] at this
          simpa [mul_assoc] using this
        exact hker y hy h1'
      · rw [← hφt] at h2
        exact hinj hy htY ((MulAut.conj c₀⁻¹).injective h2))
  have hcard1 : Nat.card Yb = Nat.card (Y.map f) :=
    Subgroup.card_map_of_injective (MulAut.conj c₀⁻¹).injective
  have hcard2 : Nat.card (Y.map f) = Nat.card Y := by
    change Nat.card (↑(Y.map f) : Set (PG (k + 2))) = Nat.card ((Y : Set L))
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinj]
  rw [← hcard2, ← hcard1]
  exact hbound

theorem eq_one_or_eq_of_normalized_L (hD : AS35L.IsTClass D) (hk : 2 ≤ k)
    (ψ : L ⧸ center L ≃* PG (k + 2)) (hZ : ∀ u ∈ center L, u * u = 1 → u = 1) {d : L}
    (hd : d ∈ D) {W : Subgroup L} (hW2 : ∀ w ∈ W, w * w = 1) (hdW : d ∈ W)
    (hWn : ∀ g : L, g * d * g⁻¹ = d → ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    ∀ w ∈ W, w = 1 ∨ w = d := by
  intro w hw
  rcases hD.mk_eq_one_or_eq_of_normalized hk ψ hd hW2 hdW hWn w hw with h1 | h1
  · left
    have hwZ : w ∈ center L := by
      rw [← QuotientGroup.eq_one_iff]
      exact ψ.injective (by rw [h1, map_one])
    exact hZ w hwZ (hW2 w hw)
  · right
    have hZ' : d⁻¹ * w ∈ center L := QuotientGroup.eq.1 (ψ.injective h1).symm
    have h2 := hZ _ hZ' (hW2 _ (W.mul_mem (W.inv_mem hdW) hw))
    rw [← mul_inv_cancel_left d w, h2, mul_one]

end AS35Z

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G} {k : ℕ}

namespace ZUHyp

variable (h : S.ZUHyp k)
include h

theorem center_pow {u : closure S.DbarAsc} (hu : u ∈ center (closure S.DbarAsc)) {j : ℕ}
    (hj : u ^ 2 ^ j = 1) : u = 1 :=
  Subtype.ext (h.eq_one_of_central u.2 (mem_center_iff'.1 hu)
    (by rw [← Subgroup.coe_pow, hj]; rfl))

theorem two_pow_le_card {t : S.O} (ht : t ∈ S.DbarAsc) {Y : Subgroup S.O}
    (hYL : Y ≤ closure S.DbarAsc) (hY2 : IsPGroup 2 Y) (htY : t ∈ Y)
    (hYc : ∀ y ∈ Y, y * t = t * y)
    (hYn : ∀ c ∈ closure S.DbarAsc, c * t = t * c → ∀ y ∈ Y, c * y * c⁻¹ ∈ Y)
    (hne : ∃ y ∈ Y, y ≠ 1 ∧ y ≠ t) : 2 ^ (2 * k + 1) ≤ Nat.card Y := by
  obtain ⟨ψ⟩ := h.psu
  have hD := h.hyp.isTClass ht
  set Y' := Y.subgroupOf (closure S.DbarAsc) with hY'
  have hmem : ∀ x : closure S.DbarAsc, x ∈ Y' ↔ (x : S.O) ∈ Y := fun x => Iff.rfl
  have hcard : Nat.card Y' = Nat.card Y := Nat.card_congr (subgroupOfEquivOfLe hYL).toEquiv
  rw [← hcard]
  refine AS35Z.two_pow_le_card_of_normalized_L hD h.two_le ψ
    (fun u hu j hj => h.center_pow hu hj) (t := mkL ht) ht
    (hY2.of_equiv (subgroupOfEquivOfLe hYL).symm) ((hmem _).2 htY) ?_ ?_ ?_
  · intro y hy
    exact Subtype.ext (hYc _ ((hmem y).1 hy))
  · intro g hg y hy
    rw [hmem]
    have hgt : g * mkL ht = mkL ht * g := by
      calc g * mkL ht = g * mkL ht * g⁻¹ * g := by group
        _ = mkL ht * g := by rw [hg]
    exact hYn g g.2 (congrArg Subtype.val hgt) _ ((hmem y).1 hy)
  · obtain ⟨y, hy, hy1, hyt⟩ := hne
    exact ⟨⟨y, hYL hy⟩, (hmem _).2 hy, fun h1 => hy1 (congrArg Subtype.val h1),
      fun h2 => hyt (congrArg Subtype.val h2)⟩

end ZUHyp

end Setting

end CFSG.LargeExtraspecial
