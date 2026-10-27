module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Co3InvPerm
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Sp62

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Sporadic.Schreier.Co3 CFSG.Blueprint CFSG.Blueprint.NativeSporadic

private theorem centralizer_subtype_equiv {G : Type*} [Group G] (H : Subgroup G) (w : ↥H) :
    Nonempty (↥(H ⊓ centralizer ({(w : G)} : Set G)) ≃* ↥(centralizer ({w} : Set ↥H))) := by
  have hmap : (centralizer ({w} : Set ↥H)).map H.subtype =
      H ⊓ centralizer ({(w : G)} : Set G) := by
    rw [CFSG.Sporadic.SmallOddCore.map_centralizer_eq_inf H.subtype_injective
      ({w} : Set ↥H), Subgroup.range_subtype, Set.image_singleton]
    rfl
  exact ⟨(MulEquiv.subgroupCongr hmap).symm.trans
    (Subgroup.equivMapOfInjective (centralizer ({w} : Set ↥H)) H.subtype
      H.subtype_injective).symm⟩

private theorem centralizer_equiv_map_range {G M : Type*} [Group G] [Group M] (f : G →* M)
    (hf : Function.Injective f) (w : G) :
    Nonempty (↥(centralizer ({w} : Set G)) ≃* ↥(f.range ⊓ centralizer ({f w} : Set M))) := by
  have hmap : (centralizer ({w} : Set G)).map f = f.range ⊓ centralizer ({f w} : Set M) := by
    rw [CFSG.Sporadic.SmallOddCore.map_centralizer_eq_inf hf ({w} : Set G), Set.image_singleton]
  exact ⟨(Subgroup.equivMapOfInjective (centralizer ({w} : Set G)) f hf).trans
    (MulEquiv.subgroupCongr hmap)⟩

section Certified


theorem co3_centralizer_cases {G : Type} [Group G] {Λ : Subgroup G} (hΛ : IsSporadic ↥Λ .Co3)
    {u : G} (huΛ : u ∈ Λ) (hu : orderOf u = 2) :
    Nonempty (↥(Λ ⊓ centralizer ({u} : Set G)) ≃* ↥co3M) ∨
      ∃ N : Subgroup G, N ≤ Λ ⊓ centralizer ({u} : Set G) ∧
        (∀ c ∈ Λ ⊓ centralizer ({u} : Set G), ∀ n ∈ N, c * n * c⁻¹ ∈ N) ∧
        Nonempty (↥N ≃* ↥NativeSporadic.M12) ∧
        Nat.card ↥(Λ ⊓ centralizer ({u} : Set G)) = 2 * 95040 := by
  obtain ⟨e⟩ := hΛ
  set ι : ↥Λ →* Equiv.Perm (Fin 276) :=
    co3P.subtype.comp (e.trans co3PermEquiv).toMonoidHom
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (e.trans co3PermEquiv).injective
  have hrange : ι.range = co3P := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (e.trans co3PermEquiv).surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let u' : ↥Λ := ⟨u, huΛ⟩
  have hu'order : orderOf u' = 2 := by
    rw [← Subgroup.orderOf_coe u']
    show orderOf u = 2
    exact hu
  have hτP : ι u' ∈ co3P := hrange ▸ ⟨u', rfl⟩
  have hτ : orderOf (ι u') = 2 := by rw [orderOf_injective ι hι, hu'order]
  have hφ1 : Nonempty (↥(Λ ⊓ centralizer ({u} : Set G)) ≃*
      ↥(centralizer ({u'} : Set ↥Λ))) := centralizer_subtype_equiv Λ u'
  have hφ2 : Nonempty (↥(centralizer ({u'} : Set ↥Λ)) ≃*
      ↥(co3P ⊓ centralizer ({ι u'} : Set (Equiv.Perm (Fin 276))))) := by
    obtain ⟨f'⟩ := centralizer_equiv_map_range ι hι u'
    exact ⟨f'.trans (MulEquiv.subgroupCongr (by rw [hrange]))⟩
  let φ : ↥(Λ ⊓ centralizer ({u} : Set G)) ≃*
      ↥(co3P ⊓ centralizer ({ι u'} : Set (Equiv.Perm (Fin 276)))) :=
    hφ1.some.trans hφ2.some
  rcases co3P_inf_centralizer_cases hτP hτ with hcase | hcase
  · obtain ⟨iso⟩ := hcase
    exact Or.inl ⟨φ.trans iso⟩
  · obtain ⟨iso⟩ := hcase
    right
    obtain ⟨N₀, hN₀norm, hM12₀, hcard⟩ := co3M1_structure
    obtain ⟨e₀⟩ := hM12₀
    let H : Subgroup G := Λ ⊓ centralizer ({u} : Set G)
    let ψ : ↥H ≃* ↥co3M1 := φ.trans iso
    let N' : Subgroup ↥H := N₀.map ψ.symm.toMonoidHom
    let N : Subgroup G := N'.map H.subtype
    have hN'norm : N'.Normal := hN₀norm.map ψ.symm.toMonoidHom ψ.symm.surjective
    refine ⟨N, ?_, ?_, ?_, ?_⟩
    · exact Subgroup.map_subtype_le N'
    · intro c hc n hn
      rcases Subgroup.mem_map.mp hn with ⟨n', hn', rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨c, hc⟩ * n' * ⟨c, hc⟩⁻¹, ?_, rfl⟩
      exact hN'norm.conj_mem n' hn' ⟨c, hc⟩
    · refine ⟨(Subgroup.equivMapOfInjective N' H.subtype H.subtype_injective).symm.trans
        ((Subgroup.equivMapOfInjective N₀ ψ.symm.toMonoidHom ψ.symm.injective).symm.trans
          e₀)⟩
    · exact (Nat.card_congr ψ.toEquiv).trans hcard

theorem isTwoSp62_inf_centralizer {G : Type} [Group G] {Λ : Subgroup G}
    (hΛ : IsSporadic ↥Λ .Co3) {u : G} (huΛ : u ∈ Λ) (hu : orderOf u = 2)
    (h : 2 ^ 10 ∣ Nat.card ↥(Λ ⊓ centralizer ({u} : Set G))) :
    IsTwoSp62 ↥(Λ ⊓ centralizer ({u} : Set G)) := by
  rcases co3_centralizer_cases hΛ huΛ hu with hcase | hcase
  · obtain ⟨e⟩ := hcase
    exact IsTwoSp62.of_mulEquiv e.symm isTwoSp62_co3M
  · obtain ⟨_N, _hNle, _hnorm, _hM12, hcard⟩ := hcase
    exfalso
    rw [hcard] at h
    norm_num at h

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT