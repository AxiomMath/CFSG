module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSolvableOrSevenCoordinates
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerAffine

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.CosetNormalizer

variable {G : Type*} [Group G]

theorem mem_normalizer_subgroupOf_iff {L U : Subgroup G} (hUL : U ≤ L) (n : L) :
    n ∈ Subgroup.normalizer ((U.subgroupOf L : Subgroup L) : Set L) ↔
      (n : G) ∈ Subgroup.normalizer (U : Set G) := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (H := U) (f := L.subtype)
    (by rw [Subgroup.range_subtype]; exact hUL)
  change n ∈ Subgroup.normalizer ((U.comap L.subtype : Subgroup L) : Set L) ↔ _
  rw [← h]
  rfl

theorem inf_normalizer_le_normalizer_coset {L U : Subgroup G} {u : G}
    (huL : ∀ l ∈ L, Commute u l) :
    L ⊓ Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) := by
  rintro n ⟨hnL, hnU⟩
  refine centralizer_inf_normalizer_le_normalizer_coset U u ⟨?_, hnU⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (huL n hnL).eq.symm

@[expose] def subgroupOfCosetEquiv {L U : Subgroup G} (hUL : U ≤ L) (u : G) :
    U.subgroupOf L ≃ ((fun v : G => u * v) '' (U : Set G)) :=
  (Subgroup.subgroupOfEquivOfLe hUL).toEquiv.trans (Additive.ofMul.trans (cosetCoordinates U u))

theorem subgroupOfCosetEquiv_apply {L U : Subgroup G} (hUL : U ≤ L) (u : G)
    (w : U.subgroupOf L) :
    (subgroupOfCosetEquiv hUL u w : G) = u * ((w : L) : G) :=
  rfl

@[expose] def subgroupOfCosetPerm {L U : Subgroup G} (hUL : U ≤ L) (u : G) :
    MulAut (U.subgroupOf L) →* Equiv.Perm ((fun v : G => u * v) '' (U : Set G)) :=
  (subgroupOfCosetEquiv hUL u).permCongrHom.toMonoidHom.comp (MulAut.toPerm _)

theorem subgroupOfCosetPerm_apply {L U : Subgroup G} (hUL : U ≤ L) (u : G)
    (σ : MulAut (U.subgroupOf L)) (w : U.subgroupOf L) :
    subgroupOfCosetPerm hUL u σ (subgroupOfCosetEquiv hUL u w) =
      subgroupOfCosetEquiv hUL u (σ w) := by
  change (subgroupOfCosetEquiv hUL u).permCongr σ.toEquiv _ = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

theorem subgroupOfCosetPerm_injective {L U : Subgroup G} (hUL : U ≤ L) (u : G) :
    Function.Injective (subgroupOfCosetPerm hUL u) := by
  intro σ τ hστ
  refine MulEquiv.ext fun w => (subgroupOfCosetEquiv hUL u).injective ?_
  rw [← subgroupOfCosetPerm_apply, ← subgroupOfCosetPerm_apply, hστ]

theorem subgroupOfCosetPerm_normalizerMonoidHom {L U : Subgroup G} (hUL : U ≤ L) {u : G}
    (huL : ∀ l ∈ L, Commute u l)
    (n : Subgroup.normalizer ((U.subgroupOf L : Subgroup L) : Set L))
    (hn : ((n : L) : G) ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) :
    subgroupOfCosetPerm hUL u ((U.subgroupOf L).normalizerMonoidHom n) =
      cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G)) ⟨((n : L) : G), hn⟩ := by
  refine Equiv.ext fun x => ?_
  obtain ⟨w, rfl⟩ := (subgroupOfCosetEquiv hUL u).surjective x
  apply Subtype.ext
  rw [subgroupOfCosetPerm_apply, subgroupOfCosetEquiv_apply, cosetNormalizerPerm_apply,
    subgroupOfCosetEquiv_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  change u * (((n : L) : G) * ((w : L) : G) * ((n : L) : G)⁻¹) =
    ((n : L) : G) * (u * ((w : L) : G)) * ((n : L) : G)⁻¹
  rw [← mul_assoc ((n : L) : G), ← (huL _ (n : L).2).eq]
  group

theorem subgroupOfCosetPerm_range_map {L U : Subgroup G} (hUL : U ≤ L) {u : G}
    (huL : ∀ l ∈ L, Commute u l) :
    (U.subgroupOf L).normalizerMonoidHom.range.map (subgroupOfCosetPerm hUL u) =
      ((L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf
          (Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)))).map
        (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))) := by
  ext σ
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    have hnU := (mem_normalizer_subgroupOf_iff hUL (n : L)).mp n.2
    have hn := inf_normalizer_le_normalizer_coset huL ⟨(n : L).2, hnU⟩
    exact ⟨⟨((n : L) : G), hn⟩, Subgroup.mem_subgroupOf.mpr ⟨(n : L).2, hnU⟩,
      (subgroupOfCosetPerm_normalizerMonoidHom hUL huL n hn).symm⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨hmL, hmU⟩ := Subgroup.mem_subgroupOf.mp hm
    let n : Subgroup.normalizer ((U.subgroupOf L : Subgroup L) : Set L) :=
      ⟨⟨m, hmL⟩, (mem_normalizer_subgroupOf_iff hUL ⟨m, hmL⟩).mpr hmU⟩
    exact ⟨_, ⟨n, rfl⟩, subgroupOfCosetPerm_normalizerMonoidHom hUL huL n m.2⟩

theorem coset_conjugation_image_of_singer {L U : Subgroup G} (hUL : U ≤ L) {u : G}
    (huL : ∀ l ∈ L, Commute u l) {m : ℕ}
    (hcyc : IsCyclic (U.subgroupOf L).normalizerMonoidHom.range)
    (hcard : Nat.card (U.subgroupOf L).normalizerMonoidHom.range = m)
    (hreg : ∀ x y : U.subgroupOf L, x ≠ 1 → y ≠ 1 →
      ∃! σ : (U.subgroupOf L).normalizerMonoidHom.range, (σ : MulAut (U.subgroupOf L)) x = y) :
    IsCyclic (((L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf
        (Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)))).map
          (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G)))) ∧
      Nat.card (((L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf
        (Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)))).map
          (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G)))) = m ∧
      ∀ x y : (fun v : G => u * v) '' (U : Set G), (x : G) ≠ u → (y : G) ≠ u →
        ∃! σ : ((L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf
          (Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)))).map
            (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))),
          (σ : Equiv.Perm ((fun v : G => u * v) '' (U : Set G))) x = y := by
  rw [← subgroupOfCosetPerm_range_map hUL huL]
  refine ⟨isCyclic_map _ _, ?_, fun x y hx hy => ?_⟩
  · rw [Subgroup.card_map_of_injective (subgroupOfCosetPerm_injective hUL u), hcard]
  · obtain ⟨a, rfl⟩ := (subgroupOfCosetEquiv hUL u).surjective x
    obtain ⟨b, rfl⟩ := (subgroupOfCosetEquiv hUL u).surjective y
    have hne : ∀ w : U.subgroupOf L, (subgroupOfCosetEquiv hUL u w : G) ≠ u → w ≠ 1 := by
      rintro w hw rfl
      exact hw (mul_one u)
    refine existsUnique_map (p := fun σ : Equiv.Perm ((fun v : G => u * v) '' (U : Set G)) =>
      σ (subgroupOfCosetEquiv hUL u a) = subgroupOfCosetEquiv hUL u b) _ _ ?_
    refine (existsUnique_congr fun σ => ?_).mp (hreg a b (hne a hx) (hne b hy))
    rw [subgroupOfCosetPerm_apply]
    exact (subgroupOfCosetEquiv hUL u).injective.eq_iff.symm

end CFSG.ProperTwoGeneratedCore.RankOnePair
