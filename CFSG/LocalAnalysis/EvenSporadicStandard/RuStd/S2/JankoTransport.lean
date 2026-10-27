module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.JankoCard

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

theorem jankoSetting_of_G {G : Type} [Group G] [Finite G] {f t r r₁ : G} {D E : Subgroup G}
    (hf5 : orderOf f = 5) (ht2 : orderOf t = 2) (hft : f * t = t * f)
    (hD : Nonempty (↥D ≃* A5)) (hDf : D ≤ centralizer ({f} : Set G))
    (hDt : D ≤ centralizer ({t} : Set G)) (hDdisj : Disjoint (zpowers f) D)
    (htD : t ∉ zpowers f ⊔ D)
    (hCt : centralizer ({f} : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ⊔ (zpowers f ⊔ D))
    (hE : E ≤ centralizer ({f} : Set G)) (hE8 : Nat.card E = 8) (hE2 : ∀ x ∈ E, x * x = 1)
    (htE : t ∈ E) (hr : r ∈ centralizer ({f} : Set G)) (hrE : r ∈ normalizer (E : Set G))
    (hr₁ : r₁ ∈ centralizer ({f} : Set G)) (hr₁E : r₁ ∈ normalizer (E : Set G))
    (hr3 : orderOf r = 3) (hr₁3 : orderOf r₁ = 3)
    (htrans : ∀ e ∈ E, e ≠ 1 → ∀ e' ∈ E, e' ≠ 1 →
      ∃ y ∈ closure ({r, r₁} : Set G), y * e * y⁻¹ = e') :
    JankoSetting ↥(centralizer ({f} : Set G)) ⟨f, mem_centralizer_singleton_iff.2 rfl⟩
      ⟨t, mem_centralizer_singleton_iff.2 hft.symm⟩ ⟨r, hr⟩ ⟨r₁, hr₁⟩
      (D.subgroupOf (centralizer ({f} : Set G))) (E.subgroupOf (centralizer ({f} : Set G))) := by
  set C := centralizer ({f} : Set G) with hC
  have hfC : f ∈ C := mem_centralizer_singleton_iff.2 rfl
  have htC : t ∈ C := mem_centralizer_singleton_iff.2 hft.symm
  have hmapD : (D.subgroupOf C).map C.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDf
  have hmapZ : (zpowers (⟨f, hfC⟩ : C)).map C.subtype = zpowers f := by
    rw [MonoidHom.map_zpowers]; rfl
  have hmapT : (zpowers (⟨t, htC⟩ : C)).map C.subtype = zpowers t := by
    rw [MonoidHom.map_zpowers]; rfl
  exact
    { f_central := mem_center_iff.2 fun g => Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
      f_ord := by rw [← Subgroup.orderOf_coe]; exact hf5
      t_ord := by rw [← Subgroup.orderOf_coe]; exact ht2
      D_iso := ⟨(Subgroup.subgroupOfEquivOfLe hDf).trans hD.some⟩
      D_cent := fun d hd => by
        rw [mem_centralizer_singleton_iff]
        exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt hd))
      D_disj := by
        rw [Subgroup.disjoint_def]
        intro x hx hxD
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
        have h1 : (f ^ k) ∈ zpowers f ⊓ D := ⟨mem_zpowers_iff.2 ⟨k, rfl⟩, hxD⟩
        rw [hDdisj.eq_bot] at h1
        exact Subtype.ext (mem_bot.1 h1)
      t_not_mem := by
        intro hmem
        apply htD
        have := Subgroup.mem_map_of_mem C.subtype hmem
        rwa [Subgroup.map_sup, hmapZ, hmapD] at this
      cent_t := by
        apply Subgroup.map_injective C.subtype_injective
        have h1 : (centralizer ({(⟨t, htC⟩ : C)} : Set C)).map C.subtype =
            C ⊓ centralizer ({t} : Set G) := by
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact ⟨x.2, mem_centralizer_singleton_iff.2
              (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx))⟩
          · rintro ⟨hyC, hyt⟩
            exact ⟨⟨y, hyC⟩, mem_centralizer_singleton_iff.2
              (Subtype.ext (mem_centralizer_singleton_iff.1 hyt)), rfl⟩
        rw [h1, hCt, Subgroup.map_sup, Subgroup.map_sup, hmapT, hmapZ, hmapD]
      E_card := by
        rw [← hE8]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
      E_exp := fun x hx => Subtype.ext (hE2 _ hx)
      t_mem := htE
      r_norm := by
        rw [mem_normalizer_iff]
        intro x
        rw [mem_subgroupOf, mem_subgroupOf]
        exact (mem_normalizer_iff.1 hrE) (x : G)
      r₁_norm := by
        rw [mem_normalizer_iff]
        intro x
        rw [mem_subgroupOf, mem_subgroupOf]
        exact (mem_normalizer_iff.1 hr₁E) (x : G)
      r_ord := by rw [← Subgroup.orderOf_coe]; exact hr3
      r₁_ord := by rw [← Subgroup.orderOf_coe]; exact hr₁3
      trans := by
        intro e he he1 e' he' he'1
        obtain ⟨y, hy, hye⟩ := htrans (e : G) he (fun h1 => he1 (Subtype.ext h1)) (e' : G) he'
          (fun h1 => he'1 (Subtype.ext h1))
        have hcl : (closure ({(⟨r, hr⟩ : C), ⟨r₁, hr₁⟩} : Set C)).map C.subtype =
            closure ({r, r₁} : Set G) := by
          rw [MonoidHom.map_closure, Set.image_pair]; rfl
        rw [← hcl] at hy
        obtain ⟨y', hy', rfl⟩ := hy
        exact ⟨y', hy', Subtype.ext hye⟩ }

namespace JankoFive

theorem card_inf_centralizer {G : Type*} [Group G] (C : Subgroup G) {x : G} (hx : x ∈ C) :
    Nat.card ↥(C ⊓ centralizer ({x} : Set G)) =
      Nat.card ↥(centralizer ({(⟨x, hx⟩ : C)} : Set C)) := by
  have h1 : (centralizer ({(⟨x, hx⟩ : C)} : Set C)).map C.subtype =
      C ⊓ centralizer ({x} : Set G) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hz))⟩
    · rintro ⟨hyC, hyx⟩
      exact ⟨⟨y, hyC⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 hyx)), rfl⟩
  rw [← h1]
  exact Subgroup.card_map_of_injective C.subtype_injective

end JankoFive

end CFSG.EvenSporadicStandard.RuStd.S2
