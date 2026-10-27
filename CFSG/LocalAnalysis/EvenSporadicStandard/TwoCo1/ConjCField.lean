module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ConjC

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_centIn_top {G : Type*} [Group G] (L : Subgroup G) {y : G} (hy : y ∈ L) :
    Nat.card (centIn (⊤ : Subgroup L) (⟨y, hy⟩ : L)) = Nat.card (centIn L y) :=
  Nat.card_congr
    { toFun := fun k => ⟨(k.1 : G), Subgroup.mem_inf.2 ⟨k.1.2,
        Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val
          (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 k.2).2))⟩⟩
      invFun := fun k => ⟨⟨k.1, (Subgroup.mem_inf.1 k.2).1⟩, Subgroup.mem_inf.2
        ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
          (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 k.2).2))⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem invType_top_of_invType {G : Type*} [Group G] {L : Subgroup G} {z : G} {ζ : L}
    (hζz : (ζ : G) = z) {c : ℕ} {y : G} (hy : InvType L z c y) :
    ∃ hyL : y ∈ L, InvType (⊤ : Subgroup L) ζ c ⟨y, hyL⟩ := by
  obtain ⟨hyL, hyo, hyz, hno8, hcard⟩ := hy
  refine ⟨hyL, Subgroup.mem_top _, (Subgroup.orderOf_coe (⟨y, hyL⟩ : L)).symm.trans hyo,
    fun h => hyz ((congrArg Subtype.val h).trans hζz), ?_, ?_⟩
  · rintro ⟨v, -, hv⟩
    refine hno8 ⟨(v : G), v.2, ?_⟩
    rw [← SubgroupClass.coe_pow]
    exact congrArg Subtype.val hv
  · rw [card_centIn_top L hyL]
    exact hcard

theorem conj_typeC_of_isSporadic
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hperf : Group.IsPerfect L)
    (hQ : IsSporadic (L ⧸ Subgroup.center L) .Co1) {z : G} (hz2 : orderOf z = 2)
    (hZ : (Subgroup.center L).map L.subtype = Subgroup.zpowers z) {y y' : G}
    (hy : InvType L z co0C3 y) (hy' : InvType L z co0C3 y') :
    ∃ h ∈ L, h * y' * h⁻¹ = y := by
  obtain ⟨e⟩ := hQ
  obtain ⟨ζ, hζc, hζz⟩ : z ∈ (Subgroup.center L).map L.subtype := hZ ▸ Subgroup.mem_zpowers z
  have hζo : orderOf ζ = 2 := by
    rw [← hz2, ← hζz]
    exact (orderOf_injective L.subtype L.subtype_injective ζ).symm
  have hcenter : Subgroup.center L = Subgroup.zpowers ζ := by
    refine Subgroup.map_injective L.subtype_injective ?_
    rw [hZ, MonoidHom.map_zpowers, ← hζz]
  let π : L →* Carrier .Co1 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.zpowers ζ := by
    rw [← hcenter]
    ext x
    simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]
  obtain ⟨hyL, hyT⟩ := invType_top_of_invType hζz hy
  obtain ⟨hyL', hyT'⟩ := invType_top_of_invType hζz hy'
  obtain ⟨h, -, hh⟩ := conj_typeC_of_cover π ζ hπ hker hζc hζo hperf hyT hyT'
  exact ⟨h.1, h.2, congrArg Subtype.val hh⟩

end CFSG.EvenSporadicStandard.TwoCo1
