module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Transport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Action

variable {G : Type} [Group G]

@[expose] def k32ConjAut (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    MulAut ↥K where
  toFun k := ⟨g * k * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg k).mp k.2⟩
  invFun k := ⟨g⁻¹ * k * g, by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) k).mp k.2
    simpa using this⟩
  left_inv k := by apply Subtype.ext; simp [mul_assoc]
  right_inv k := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

@[expose] def k32ActHom (K N : Subgroup G) (hN : N ≤ Subgroup.normalizer (K : Set G)) :
    ↥N →* MulAut ↥K where
  toFun n := k32ConjAut K n (hN n.2)
  map_one' := by ext k; simp [k32ConjAut]
  map_mul' a b := by ext k; simp [k32ConjAut, mul_assoc]

theorem k32ActHom_apply (K N : Subgroup G) (hN : N ≤ Subgroup.normalizer (K : Set G)) (n : ↥N)
    (k : ↥K) : ((k32ActHom K N hN n k : ↥K) : G) = n * k * (n : G)⁻¹ := rfl

theorem k32ActHom_of_mem (K N : Subgroup G) (hN : N ≤ Subgroup.normalizer (K : Set G)) (n : ↥N)
    (hn : (n : G) ∈ K) : k32ActHom K N hN n = MulAut.conj (⟨n, hn⟩ : ↥K) := by
  ext k
  simp [k32ActHom_apply]

theorem k32ActHom_eq_one_iff (K N : Subgroup G) (hN : N ≤ Subgroup.normalizer (K : Set G))
    (n : ↥N) : k32ActHom K N hN n = 1 ↔ (n : G) ∈ Subgroup.centralizer (K : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := congrArg (fun φ => ((φ ⟨k, hk⟩ : ↥K) : G)) h
    simp only [k32ActHom_apply, MulAut.one_apply] at this
    calc k * n = (n * k * (n : G)⁻¹) * n := by rw [this]
      _ = n * k := by group
  · intro h
    ext k
    have := Subgroup.mem_centralizer_iff.mp h k k.2
    simp only [k32ActHom_apply, MulAut.one_apply]
    calc (n : G) * k * (n : G)⁻¹ = k * n * (n : G)⁻¹ := by rw [← this]
      _ = k := by group

end Action

section Transport

variable {G D : Type} [Group G] [Group D]

theorem k32_isSylowTwoOf_map {H T : Subgroup G} (α : ↥H →* D) (hT : IsSylowTwoOf T H) :
    IsSylowTwoOf ((T.subgroupOf H).map α) α.range := by
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
  · have h2 : IsPGroup 2 (T.subgroupOf H) := by
      have : IsPGroup 2 ↥T := hT.2.1
      exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
    exact h2.of_surjective (α.subgroupMap _) (α.subgroupMap_surjective _)
  · have heq : ((T.subgroupOf H).map α).subgroupOf α.range =
        (T.subgroupOf H).map α.rangeRestrict := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨t, ht, hty⟩
        exact ⟨t, ht, Subtype.ext hty⟩
      · rintro ⟨t, ht, hty⟩
        exact ⟨t, ht, congrArg Subtype.val hty⟩
    rw [heq]
    intro hdvd
    exact hT.2.2 (hdvd.trans (Subgroup.index_map_dvd _ α.rangeRestrict_surjective))

theorem k32_relIndex_map_dvd (f : G →* D) {H K : Subgroup G} (hHK : H ≤ K) :
    (H.map f).relIndex (K.map f) ∣ H.relIndex K := by
  have heq : (H.map f).subgroupOf (K.map f) = (H.subgroupOf K).map (f.subgroupMap K) := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨h, hh, hhy⟩
      exact ⟨⟨h, hHK hh⟩, hh, Subtype.ext hhy⟩
    · rintro ⟨k, hk, hky⟩
      exact ⟨k, hk, congrArg Subtype.val hky⟩
  rw [Subgroup.relIndex, heq]
  exact Subgroup.index_map_dvd _ (f.subgroupMap_surjective K)

theorem k32_isA4Block_top {L U : Subgroup G} (h : IsA4Block L U) :
    IsA4Block (⊤ : Subgroup ↥L) (U.subgroupOf L) := by
  have hUL : U ≤ L := h.le
  have hTop : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hU' : (U.subgroupOf L).map L.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUL
  refine IsA4Block.of_map_injective L.subtype Subtype.val_injective ?_
  rw [hTop, hU']
  exact h

theorem k32_isA4Block_range {L U : Subgroup G} (h : IsA4Block L U) (f : ↥L →* D)
    (hf : Function.Injective f) : IsA4Block f.range ((U.subgroupOf L).map f) := by
  have h₂ := IsA4Block.map_of_injective (k32_isA4Block_top h) f hf
  rwa [← MonoidHom.range_eq_map] at h₂

end Transport

end CFSG.QuasithinUnique.DoubleA3
