module

public import CFSG.GroupTheory.NonabelianSimpleOrderSixty
public import CFSG.Foundations.Basic

public section

namespace CFSG.GroupTheory

open scoped Pointwise

variable {H : Type*} [Group H]

theorem card_sup_mul_card_inf_of_commute [Finite H] (L R : Subgroup H)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup H) * Nat.card (L ⊓ R : Subgroup H) = Nat.card L * Nat.card R ∧
    ((L ⊔ R : Subgroup H) : Set H) = (L : Set H) * (R : Set H) := by
  let μ : L × R →* H := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : H) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hset : ((L ⊔ R : Subgroup H) : Set H) = (L : Set H) * (R : Set H) := by
    rw [← hrange]
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.1.2, x.2, x.2.2, rfl⟩
    · rintro ⟨l, hl, r, hr, rfl⟩
      exact ⟨(⟨l, hl⟩, ⟨r, hr⟩), rfl⟩
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup H) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : H), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : H)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  exact ⟨by rw [mul_comm]; exact this, hset⟩

theorem inf_centralizer_eq_map_center (L : Subgroup H) :
    L ⊓ Subgroup.centralizer (L : Set H) = (Subgroup.center L).map L.subtype := by
  ext x
  constructor
  · rintro ⟨hxL, hxC⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    change (⟨x, hxL⟩ : L) ∈ Subgroup.center L
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC y y.2)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    have := Subgroup.mem_center_iff.1 hy ⟨z, hz⟩
    exact congrArg Subtype.val this

theorem card_eq_index_mul_card_quotient_center_mul_card_centralizer [Finite H]
    (L : Subgroup H) :
    Nat.card H = (L ⊔ Subgroup.centralizer (L : Set H)).index *
      Nat.card (L ⧸ Subgroup.center L) * Nat.card (Subgroup.centralizer (L : Set H)) := by
  set R := Subgroup.centralizer (L : Set H)
  have hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 hy x hx
  obtain ⟨hcard, -⟩ := card_sup_mul_card_inf_of_commute L R hc
  have hZ : Nat.card (L ⊓ R : Subgroup H) = Nat.card (Subgroup.center L) := by
    rw [inf_centralizer_eq_map_center]
    exact Subgroup.card_map_of_injective L.subtype_injective
  rw [hZ, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L)] at hcard
  have hpos : 0 < Nat.card (Subgroup.center L) := Nat.card_pos
  have hsup : Nat.card (L ⊔ R : Subgroup H) = Nat.card (L ⧸ Subgroup.center L) * Nat.card R := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hcard]
    ring
  rw [← (L ⊔ R).index_mul_card, hsup, mul_assoc]

theorem quasisimple_commuting_product_centralizer_order_bound [Finite H] (L : Subgroup H)
    (hL : IsQuasisimple L) :
    ((L ⊔ Subgroup.centralizer (L : Set H) : Subgroup H) : Set H) =
        (L : Set H) * (Subgroup.centralizer (L : Set H) : Set H) ∧
    L ⊓ Subgroup.centralizer (L : Set H) = (Subgroup.center L).map L.subtype ∧
    Nat.card H = (L ⊔ Subgroup.centralizer (L : Set H)).index *
      Nat.card (L ⧸ Subgroup.center L) * Nat.card (Subgroup.centralizer (L : Set H)) ∧
    Nat.card (L ⧸ Subgroup.center L) * Nat.card (Subgroup.centralizer (L : Set H)) ∣
      Nat.card H ∧
    60 * Nat.card (Subgroup.centralizer (L : Set H)) ≤ Nat.card H ∧
    ∀ A : Subgroup H, A ≤ Subgroup.centralizer (L : Set H) → 60 * Nat.card A ≤ Nat.card H := by
  set R := Subgroup.centralizer (L : Set H)
  have hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 hy x hx
  have hformula := card_eq_index_mul_card_quotient_center_mul_card_centralizer L
  have hdvd : Nat.card (L ⧸ Subgroup.center L) * Nat.card R ∣ Nat.card H := by
    rw [hformula, mul_assoc]
    exact dvd_mul_left _ _
  obtain ⟨-, hsimple, hna⟩ := hL
  have h60 : 60 ≤ Nat.card (L ⧸ Subgroup.center L) :=
    nonabelian_simple_order_at_least_sixty hsimple hna
  have hR : 60 * Nat.card R ≤ Nat.card H :=
    (Nat.mul_le_mul_right _ h60).trans (Nat.le_of_dvd Nat.card_pos hdvd)
  refine ⟨(card_sup_mul_card_inf_of_commute L R hc).2, inf_centralizer_eq_map_center L,
    hformula, hdvd, hR, fun A hA => ?_⟩
  exact (Nat.mul_le_mul_left 60 (Subgroup.card_le_of_le hA)).trans hR

theorem card_formula_of_le [Finite H] (L K : Subgroup H) (hLK : L ≤ K) :
    Nat.card K = (L ⊔ (Subgroup.centralizer (L : Set H) ⊓ K)).relIndex K *
      Nat.card (L ⧸ Subgroup.center L) *
      Nat.card (Subgroup.centralizer (L : Set H) ⊓ K : Subgroup H) := by
  set R := Subgroup.centralizer (L : Set H) ⊓ K with hR
  have hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 hy.1 x hx
  obtain ⟨hcard, -⟩ := card_sup_mul_card_inf_of_commute L R hc
  have hinf : L ⊓ R = (Subgroup.center L).map L.subtype := by
    rw [← inf_centralizer_eq_map_center]
    ext x
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hLK h.1⟩⟩
  have hZ : Nat.card (L ⊓ R : Subgroup H) = Nat.card (Subgroup.center L) := by
    rw [hinf]
    exact Subgroup.card_map_of_injective L.subtype_injective
  rw [hZ, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L)] at hcard
  have hpos : 0 < Nat.card (Subgroup.center L) := Nat.card_pos
  have hsup : Nat.card (L ⊔ R : Subgroup H) = Nat.card (L ⧸ Subgroup.center L) * Nat.card R := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hcard]
    ring
  have hle : L ⊔ R ≤ K := sup_le hLK inf_le_right
  have hidx := ((L ⊔ R).subgroupOf K).index_mul_card
  have hcardsub : Nat.card ((L ⊔ R).subgroupOf K) = Nat.card (L ⊔ R : Subgroup H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hcardsub, hsup] at hidx
  rw [Subgroup.relIndex, ← hidx]
  ring

theorem quasisimple_commuting_product_centralizer_order_bound_element {G : Type*} [Group G]
    [Finite G] (L : Subgroup G) (hL : IsQuasisimple L) (t : G)
    (ht : t ∈ Subgroup.centralizer (L : Set G)) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) =
        (L ⊔ (Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer {t})).relIndex
          (Subgroup.centralizer {t}) *
        Nat.card (L ⧸ Subgroup.center L) *
        Nat.card (Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) :
          Subgroup G) ∧
    Nat.card (L ⧸ Subgroup.center L) *
        Nat.card (Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) :
          Subgroup G) ∣ Nat.card (Subgroup.centralizer ({t} : Set G)) ∧
    60 * Nat.card (Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) :
          Subgroup G) ≤ Nat.card (Subgroup.centralizer ({t} : Set G)) := by
  have hLC : L ≤ Subgroup.centralizer ({t} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 ht x hx
  have hformula := card_formula_of_le L _ hLC
  have hdvd : Nat.card (L ⧸ Subgroup.center L) *
      Nat.card (Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) :
        Subgroup G) ∣ Nat.card (Subgroup.centralizer ({t} : Set G)) := by
    rw [hformula, mul_assoc]
    exact dvd_mul_left _ _
  obtain ⟨-, hsimple, hna⟩ := hL
  have h60 : 60 ≤ Nat.card (L ⧸ Subgroup.center L) :=
    nonabelian_simple_order_at_least_sixty hsimple hna
  exact ⟨hformula, hdvd, (Nat.mul_le_mul_right _ h60).trans (Nat.le_of_dvd Nat.card_pos hdvd)⟩

end CFSG.GroupTheory
