module

public import CFSG.Open.AschbacherComponentTypeTheorem5MilestoneDefs
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

open CFSG.Open

namespace CFSG.ComponentClassification.AschbacherTheorem5

theorem oddCore_eq_native (G : Type*) [Group G] :
    aschbacherThm5OddCore G = componentClassificationOddCore G := rfl

theorem oddCore_characteristic (G : Type*) [Group G] :
    (aschbacherThm5OddCore G).Characteristic := OddCore.characteristic G

theorem oddCore_odd (G : Type*) [Group G] [Finite G] :
    Odd (Nat.card (aschbacherThm5OddCore G)) := OddCore.odd_card G

theorem quotient_oddCore_eq_bot (G : Type*) [Group G] [Finite G] :
    aschbacherThm5OddCore (G ⧸ aschbacherThm5OddCore G) = ⊥ :=
  OddCore.quotient_corefree G

theorem core_le {G : Type*} [Group G] (D : Subgroup G) :
    aschbacherThm5Core D ≤ D := Subgroup.map_subtype_le _

theorem core_odd {G : Type*} [Group G] [Finite G] (D : Subgroup G) :
    Odd (Nat.card (aschbacherThm5Core D)) := by
  rw [aschbacherThm5Core, Subgroup.card_subtype]
  exact oddCore_odd D

theorem preimage_le {G : Type*} [Group G] (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    aschbacherThm5Preimage D Abar ≤ D := Subgroup.map_subtype_le _

theorem core_le_preimage {G : Type*} [Group G] (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    aschbacherThm5Core D ≤ aschbacherThm5Preimage D Abar := by
  apply Subgroup.map_mono
  simpa only [QuotientGroup.ker_mk'] using
    Subgroup.ker_le_comap (QuotientGroup.mk' (aschbacherThm5OddCore D)) Abar

theorem preimage_subgroupOf {G : Type*} [Group G] (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    (aschbacherThm5Preimage D Abar).subgroupOf D =
      Abar.comap (QuotientGroup.mk' (aschbacherThm5OddCore D)) :=
  Subgroup.comap_map_eq_self_of_injective D.subtype_injective _

theorem preimage_quotient_image {G : Type*} [Group G] (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    ((aschbacherThm5Preimage D Abar).subgroupOf D).map
      (QuotientGroup.mk' (aschbacherThm5OddCore D)) = Abar := by
  rw [preimage_subgroupOf]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem preimage_injective {G : Type*} [Group G] (D : Subgroup G) :
    Function.Injective (aschbacherThm5Preimage D) :=
  (Subgroup.map_injective D.subtype_injective).comp
    (Subgroup.comap_injective (QuotientGroup.mk'_surjective _))

theorem mem_preimage_iff {G : Type*} [Group G] (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) (d : D) :
    d.val ∈ aschbacherThm5Preimage D Abar ↔
      QuotientGroup.mk' (aschbacherThm5OddCore D) d ∈ Abar := by
  change D.subtype d ∈ (Abar.comap
    (QuotientGroup.mk' (aschbacherThm5OddCore D))).map D.subtype ↔ _
  exact Subgroup.mem_map_iff_mem D.subtype_injective

theorem preimage_top {G : Type*} [Group G] (D : Subgroup G) :
    aschbacherThm5Preimage D ⊤ = D := by
  rw [aschbacherThm5Preimage, Subgroup.comap_top, Subgroup.map_top,
    Subgroup.range_subtype]

theorem preimage_sup {G : Type*} [Group G] (D : Subgroup G)
    (Abar Bbar : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    aschbacherThm5Preimage D (Abar ⊔ Bbar) =
      aschbacherThm5Preimage D Abar ⊔ aschbacherThm5Preimage D Bbar := by
  rw [aschbacherThm5Preimage, ← Subgroup.comap_sup_eq _ _ _
    (QuotientGroup.mk'_surjective _), Subgroup.map_sup]
  rfl

theorem preimages_generate {G Index : Type*} [Group G] [Nonempty Index]
    (D : Subgroup G) (Abar : Index → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hgen : ⨆ i, Abar i = ⊤) :
    (⨆ i, aschbacherThm5Preimage D (Abar i)) = D := by
  let quotient := QuotientGroup.mk' (aschbacherThm5OddCore D)
  let family := fun i => (Abar i).comap quotient
  have hkernel : quotient.ker ≤ ⨆ i, family i := by
    obtain ⟨i⟩ := ‹Nonempty Index›
    exact (Subgroup.ker_le_comap quotient (Abar i)).trans (le_iSup family i)
  have hmap : (⨆ i, family i).map quotient = ⊤ := by
    rw [Subgroup.map_iSup]
    simp only [family, quotient, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective _)]
    exact hgen
  have hfull : (⨆ i, family i) = ⊤ := by
    have hcomap := Subgroup.comap_map_eq quotient (⨆ i, family i)
    rw [hmap, Subgroup.comap_top, sup_eq_left.mpr hkernel] at hcomap
    exact hcomap.symm
  change (⨆ i, (family i).map D.subtype) = D
  rw [← Subgroup.map_iSup, hfull, Subgroup.map_top, Subgroup.range_subtype]

theorem preimage_normal {G : Type*} [Group G] (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) [Abar.Normal] :
    ((aschbacherThm5Preimage D Abar).subgroupOf D).Normal := by
  rw [preimage_subgroupOf]
  infer_instance

theorem two_factor_product {G : Type*} [Group G] (D : Subgroup G)
    (Abar Bbar : Subgroup (D ⧸ aschbacherThm5OddCore D)) [Abar.Normal]
    (hgen : Abar ⊔ Bbar = ⊤) :
    ∀ d ∈ D, ∃ a ∈ aschbacherThm5Preimage D Abar,
      ∃ b ∈ aschbacherThm5Preimage D Bbar, d = a * b := by
  let first := Abar.comap (QuotientGroup.mk' (aschbacherThm5OddCore D))
  let second := Bbar.comap (QuotientGroup.mk' (aschbacherThm5OddCore D))
  have hfull : first ⊔ second = ⊤ := by
    rw [Subgroup.comap_sup_eq _ _ _ (QuotientGroup.mk'_surjective _), hgen,
      Subgroup.comap_top]
  intro d hd
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := first) (t := second)).mp
      (hfull.symm ▸ Subgroup.mem_top (⟨d, hd⟩ : D))
  exact ⟨a.val, Subgroup.mem_map_of_mem D.subtype ha,
    b.val, Subgroup.mem_map_of_mem D.subtype hb, (congrArg Subtype.val hab).symm⟩

end CFSG.ComponentClassification.AschbacherTheorem5
