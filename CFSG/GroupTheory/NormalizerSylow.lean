module

public import CFSG.Dihedral.DihedralFusionStepReplacement

public noncomputable section

namespace CFSG.GorensteinWalter

open scoped Pointwise

universe u v

theorem hom_to_pGroup_eq_one_of_sylow
    {N : Type u} {A : Type v} [Group N] [Finite N] [Group A]
    {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A)
    (f : N →* A) (S : Sylow p N)
    (hS : ∀ s : S, f s = 1) : ∀ g : N, f g = 1 := by
  intro g
  obtain ⟨s, hs, hsg⟩ := hom_to_pGroup_image_on_sylow hA f S g
  exact hsg.symm.trans (hS ⟨s, hs⟩)

theorem exists_sylow_normalizer_of_card_max
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (H : Subgroup G) (hHS : H ≤ (S : Subgroup G))
    (hmax : ∀ K : Subgroup G, K ≤ (S : Subgroup G) → Nonempty (K ≃* H) →
      Nat.card ((Subgroup.normalizer (K : Set G)).subgroupOf (S : Subgroup G)) ≤
        Nat.card ((Subgroup.normalizer (H : Set G)).subgroupOf (S : Subgroup G))) :
    ∃ T : Sylow p (Subgroup.normalizer (H : Set G)),
      (T : Subgroup (Subgroup.normalizer (H : Set G))) =
        (S : Subgroup G).subgroupOf (Subgroup.normalizer (H : Set G)) := by
  let N := Subgroup.normalizer (H : Set G)
  let R : Subgroup N := (S : Subgroup G).subgroupOf N
  have hR : IsPGroup p R := S.isPGroup'.comap_subtype
  obtain ⟨T, hRT⟩ := hR.exists_le_sylow
  have hH : IsPGroup p H := S.isPGroup'.to_le hHS
  let : (H.subgroupOf N).Normal := by
    change (H.subgroupOf (Subgroup.normalizer (H : Set G))).Normal
    infer_instance
  have hHN : IsPGroup p (H.subgroupOf N) := hH.comap_subtype
  have hHT : H.subgroupOf N ≤ (T : Subgroup N) :=
    hHN.le_sylow_of_normal T
  let U : Subgroup G := (T : Subgroup N).map N.subtype
  have hU : IsPGroup p U := T.isPGroup'.map N.subtype
  obtain ⟨Q, hUQ⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  let e := MulAut.conj g
  let K : Subgroup G := H.map e.toMonoidHom
  let V : Subgroup G := U.map e.toMonoidHom
  have hQmap : (Q : Subgroup G).map e.toMonoidHom = (S : Subgroup G) := by
    have h := congrArg (fun P : Sylow p G => (P : Subgroup G)) hg
    exact h
  have hVS : V ≤ (S : Subgroup G) := (Subgroup.map_mono hUQ).trans_eq hQmap
  have hHU : H ≤ U := by
    rw [← Subgroup.map_subgroupOf_eq_of_le
      (Subgroup.le_normalizer : H ≤ N)]
    exact Subgroup.map_mono hHT
  have hKU : K ≤ V := Subgroup.map_mono hHU
  have hKS : K ≤ (S : Subgroup G) := hKU.trans hVS
  have hVN : V ≤ Subgroup.normalizer (K : Set G) := by
    have hUN : U ≤ N := Subgroup.map_subtype_le (T : Subgroup N)
    have h := Subgroup.map_mono (f := e.toMonoidHom) hUN
    rwa [Subgroup.map_equiv_normalizer_eq] at h
  have hKequiv : Nonempty (K ≃* H) :=
    ⟨(H.equivMapOfInjective e.toMonoidHom e.injective).symm⟩
  have hbound := hmax K hKS hKequiv
  have hVle : V ≤ (Subgroup.normalizer (K : Set G)) ⊓ (S : Subgroup G) :=
    le_inf hVN hVS
  have hcardV : Nat.card V = Nat.card (T : Subgroup N) := by
    rw [Subgroup.card_map_of_injective e.injective,
      Subgroup.card_map_of_injective N.subtype_injective]
  have hcardK : Nat.card ((Subgroup.normalizer (K : Set G)).subgroupOf
      (S : Subgroup G)) =
      Nat.card ((Subgroup.normalizer (K : Set G)) ⊓ (S : Subgroup G) : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective
      (f := (S : Subgroup G).subtype) (S : Subgroup G).subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  have hcardR : Nat.card ((Subgroup.normalizer (H : Set G)).subgroupOf
      (S : Subgroup G)) = Nat.card R := by
    rw [← Subgroup.card_map_of_injective
      (f := (S : Subgroup G).subtype) (S : Subgroup G).subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    change Nat.card (N ⊓ (S : Subgroup G) : Subgroup G) =
      Nat.card ((S : Subgroup G).subgroupOf N)
    rw [← Subgroup.card_map_of_injective (f := N.subtype) N.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hcardT : Nat.card (T : Subgroup N) ≤ Nat.card R := by
    calc
      Nat.card (T : Subgroup N) = Nat.card V := hcardV.symm
      _ ≤ Nat.card ((Subgroup.normalizer (K : Set G)) ⊓
          (S : Subgroup G) : Subgroup G) := Subgroup.card_le_of_le hVle
      _ = Nat.card ((Subgroup.normalizer (K : Set G)).subgroupOf
          (S : Subgroup G)) := hcardK.symm
      _ ≤ Nat.card ((Subgroup.normalizer (H : Set G)).subgroupOf
          (S : Subgroup G)) := hbound
      _ = Nat.card R := hcardR
  exact ⟨T, (Subgroup.eq_of_le_of_card_ge hRT hcardT).symm⟩

@[expose] def localNormalizerToNormalizer
    {G : Type u} [Group G] (S H : Subgroup G) :
    ((Subgroup.normalizer (H : Set G)).subgroupOf S) →*
      Subgroup.normalizer (H : Set G) where
  toFun x := ⟨x.val.val, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem localNormalizerToNormalizer_injective
    {G : Type u} [Group G] (S H : Subgroup G) :
    Function.Injective (localNormalizerToNormalizer S H) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Subgroup.normalizer (H : Set G) => z.val) hxy

theorem localNormalizerToNormalizer_range
    {G : Type u} [Group G] (S H : Subgroup G) :
    (localNormalizerToNormalizer S H).range =
      S.subgroupOf (Subgroup.normalizer (H : Set G)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.val.property
  · intro hx
    exact ⟨⟨⟨x.val, hx⟩, x.property⟩, rfl⟩

theorem exists_sylow_localNormalizer_range_of_card_max
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (H : Subgroup G) (hHS : H ≤ (S : Subgroup G))
    (hmax : ∀ K : Subgroup G, K ≤ (S : Subgroup G) → Nonempty (K ≃* H) →
      Nat.card ((Subgroup.normalizer (K : Set G)).subgroupOf (S : Subgroup G)) ≤
        Nat.card ((Subgroup.normalizer (H : Set G)).subgroupOf (S : Subgroup G))) :
    ∃ T : Sylow p (Subgroup.normalizer (H : Set G)),
      (T : Subgroup (Subgroup.normalizer (H : Set G))) =
        (localNormalizerToNormalizer (S : Subgroup G) H).range := by
  rw [localNormalizerToNormalizer_range]
  exact exists_sylow_normalizer_of_card_max S H hHS hmax

theorem exists_sylow_normalizer_map_of_card_max
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (H : Subgroup G) (hHS : H ≤ (S : Subgroup G))
    (hmax : ∀ K : Subgroup G, K ≤ (S : Subgroup G) → Nonempty (K ≃* H) →
      Nat.card ((Subgroup.normalizer (K : Set G)).subgroupOf (S : Subgroup G)) ≤
        Nat.card ((Subgroup.normalizer (H : Set G)).subgroupOf (S : Subgroup G))) :
    ∃ T : Sylow p (Subgroup.normalizer (H : Set G)),
      (T : Subgroup (Subgroup.normalizer (H : Set G))).map
          (Subgroup.normalizer (H : Set G)).subtype =
        (S : Subgroup G) ⊓ Subgroup.normalizer (H : Set G) := by
  obtain ⟨T, hT⟩ := exists_sylow_normalizer_of_card_max S H hHS hmax
  exact ⟨T, by rw [hT, Subgroup.subgroupOf_map_subtype]⟩

end CFSG.GorensteinWalter
