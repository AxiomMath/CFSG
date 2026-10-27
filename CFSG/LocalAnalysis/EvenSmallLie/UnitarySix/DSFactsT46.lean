module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeParabolic

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Sporadic.Schreier CFSG.Fischer

theorem card_subgroupOf_T46
    {H : Subgroup (Equiv.Perm (Fin 693))} (hH : H ≤ T46) :
    Nat.card (H.subgroupOf T46) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv

theorem image_conjClass_T46
    (a : T46) :
    (Subtype.val '' conjClass (uK.subgroupOf T46) a) = conjClass uK (a : Equiv.Perm (Fin 693)) := by
  ext x
  constructor
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k, uK_le_T46 hk⟩ * a * ⟨k, uK_le_T46 hk⟩⁻¹, ⟨⟨k, uK_le_T46 hk⟩, hk, rfl⟩, rfl⟩

theorem mem_normalizer_T46
    {H : Subgroup (Equiv.Perm (Fin 693))} (hH : H ≤ T46) {x : T46} :
    x ∈ Subgroup.normalizer ((H.subgroupOf T46 : Subgroup T46) : Set T46) ↔
      (x : Equiv.Perm (Fin 693)) ∈ Subgroup.normalizer (H : Set (Equiv.Perm (Fin 693))) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx h
    by_cases hT : h ∈ T46
    · have := hx ⟨h, hT⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · constructor
      · exact fun hh => absurd (hH hh) hT
      · intro hh
        exact absurd (by
          have := T46.mul_mem (T46.mul_mem (T46.inv_mem x.2) (hH hh)) x.2
          simpa [mul_assoc] using this) hT
  · intro hx h
    have := hx (h : Equiv.Perm (Fin 693))
    simpa [Subgroup.mem_subgroupOf] using this

@[expose] noncomputable def toddT46 :
    ToddParabolic T46 where
  A := uA.subgroupOf T46
  K := uK.subgroupOf T46
  S := uS.subgroupOf T46
  a₁ := ⟨j1, uA_le_T46 j1_mem⟩
  a₂ := ⟨j2, uA_le_T46 j2_mem⟩
  a₃ := ⟨j3, uA_le_T46 j3_mem⟩
  card_Q := card_T46_eq
  card_A := (card_subgroupOf_T46 uA_le_T46).trans (card_uA.trans (by norm_num))
  A_comm x hx y hy := Subtype.ext (uA_comm _ hx _ hy)
  A_sq x hx := Subtype.ext (by simpa using uA_sq _ hx)
  card_K := (card_subgroupOf_T46 uK_le_T46).trans card_uK
  lieModel_K := lieModel_of_mulEquiv_S ((Subgroup.subgroupOfEquivOfLe uK_le_T46).trans uKEquivS)
  K_le_normalizer k hk := (mem_normalizer_T46 uA_le_T46).2 (uK_le_normalizer hk)
  A_inf_K := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : Equiv.Perm (Fin 693)) ∈ uA ⊓ uK := ⟨hx.1, hx.2⟩
    rw [uA_inf_uK, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).2 (Subtype.ext h1)
  normalizer_A := by
    refine le_antisymm (fun x hx => ?_) (sup_le Subgroup.le_normalizer fun k hk =>
      (mem_normalizer_T46 uA_le_T46).2 (uK_le_normalizer hk))
    have h1 : (x : Equiv.Perm (Fin 693)) ∈ uP := by
      rw [← normalizer_uA]
      exact ⟨x.2, (mem_normalizer_T46 uA_le_T46).1 hx⟩
    rw [uP_eq] at h1
    rw [← Subgroup.subgroupOf_sup uA_le_T46 uK_le_T46]
    exact h1
  centralizer_A := by
    refine le_antisymm (fun x hx => ?_) fun x hx => ?_
    · have hc : (x : Equiv.Perm (Fin 693)) ∈
          T46 ⊓ Subgroup.centralizer (uA : Set (Equiv.Perm (Fin 693))) := by
        refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
        have := Subgroup.mem_centralizer_iff.1 hx ⟨h, uA_le_T46 hh⟩ hh
        exact congrArg Subtype.val this
      rw [centralizer_uA] at hc
      exact hc
    · exact Subgroup.mem_centralizer_iff.2 fun h hh => Subtype.ext (uA_comm _ hh _ hx)
  a_mem := ⟨j1_mem, j2_mem, j3_mem⟩
  conj_into_A t ht := by
    obtain ⟨g, hg, hgA⟩ := conj_into_uA t.2 (by rw [Subgroup.orderOf_coe]; exact ht)
    exact ⟨⟨g, hg⟩, hgA⟩
  classes t ht := by
    obtain ⟨g, hg, hgj⟩ := involution_classes t.2 (by rw [Subgroup.orderOf_coe]; exact ht)
    have key : ∀ (j : Equiv.Perm (Fin 693)) (hj : j ∈ T46), g * t * g⁻¹ = j →
        IsConj t ⟨j, hj⟩ := fun j hj h => isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext h⟩
    rcases hgj with h | h | h
    · exact Or.inl (key _ _ h)
    · exact Or.inr (Or.inl (key _ _ h))
    · exact Or.inr (Or.inr (key _ _ h))
  not_isConj := by
    have hmap : ∀ {a b : Equiv.Perm (Fin 693)} (ha : a ∈ T46) (hb : b ∈ T46),
        IsConj (⟨a, ha⟩ : T46) ⟨b, hb⟩ → IsConj a b := fun ha hb h => by
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      exact isConj_iff.2 ⟨c, congrArg Subtype.val hc⟩
    obtain ⟨h12, h13, h23⟩ := not_isConj_j
    exact ⟨fun h => h12 (hmap _ _ h), fun h => h13 (hmap _ _ h), fun h => h23 (hmap _ _ h)⟩
  orbits a ha ha1 := by
    have ha1' : (a : Equiv.Perm (Fin 693)) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hback : ∀ (j : Equiv.Perm (Fin 693)) (hj : j ∈ T46),
        (a : Equiv.Perm (Fin 693)) ∈ conjClass uK j →
          a ∈ conjClass (uK.subgroupOf T46) ⟨j, hj⟩ := by
      intro j hj h
      rw [show j = ((⟨j, hj⟩ : T46) : Equiv.Perm (Fin 693)) from rfl,
        ← image_conjClass_T46] at h
      obtain ⟨x, hx, hxa⟩ := h
      rwa [← Subtype.ext hxa]
    rcases korbits.1 _ ha ha1' with h | h | h
    · exact Or.inl (hback j1 _ h)
    · exact Or.inr (Or.inl (hback j2 _ h))
    · exact Or.inr (Or.inr (hback j3 _ h))
  orbit_card := by
    have h : ∀ (j : Equiv.Perm (Fin 693)) (hj : j ∈ T46),
        (conjClass (uK.subgroupOf T46) ⟨j, hj⟩).ncard = (conjClass uK j).ncard := by
      intro j hj
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective, image_conjClass_T46]
    obtain ⟨-, h1, h2, h3⟩ := korbits
    exact ⟨(h j1 _).trans h1, (h j2 _).trans h2, (h j3 _).trans h3⟩
  card_S := (card_subgroupOf_T46 uS_le_T46).trans (card_uS.trans (by norm_num))
  A_le_S x hx := uA_le_uS hx
  center_S x hx := by
    have h1 : (∀ s ∈ uS.subgroupOf T46, x * s = s * x) ↔
        ∀ s ∈ uS, (x : Equiv.Perm (Fin 693)) * s = s * x := by
      constructor
      · intro hc s hs
        exact congrArg Subtype.val (hc ⟨s, uS_le_T46 hs⟩ hs)
      · intro hc s hs
        exact Subtype.ext (hc _ hs)
    rw [h1, center_uS (Subgroup.mem_subgroupOf.1 hx)]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  abelian_S X hX hcomm := by
    have hXS : X.map T46.subtype ≤ uS := by
      rintro _ ⟨x, hx, rfl⟩
      exact hX hx
    have hcomm' : ∀ x ∈ X.map T46.subtype, ∀ y ∈ X.map T46.subtype, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hcomm x hx y hy)
    obtain ⟨h1, h2⟩ := abelian_le_uS hXS hcomm'
    rw [Subgroup.card_map_of_injective Subtype.val_injective] at h1 h2
    refine ⟨le_of_le_of_eq h1 (by norm_num), fun h => ?_⟩
    rw [← Subgroup.comap_map_eq_self_of_injective (f := T46.subtype) T46.subtype_injective X,
      h2 (h.trans (by norm_num))]
    rfl
  sq_a₁ := by
    obtain ⟨u, hu, v, hv, h1, h2, h3, h4, h5⟩ := sq_j1
    refine ⟨⟨u, hu⟩, ⟨v, hv⟩, ?_, ?_, Subtype.ext h3, Subtype.ext h4, Subtype.ext h5⟩
    · rw [← Subgroup.orderOf_coe]; exact h1
    · rw [← Subgroup.orderOf_coe]; exact h2
  sq_a₂ := by
    refine ⟨⟨y2, uP_le_T46 sq_j2.1⟩, ?_, Subtype.ext sq_j2.2⟩
    rw [← Subgroup.subgroupOf_sup uA_le_T46 uK_le_T46, Subgroup.mem_subgroupOf, ← uP_eq]
    exact sq_j2.1
  not_sq_a₃ g hg := not_sq_j3 g g.2 (congrArg Subtype.val hg)

end CFSG.EvenSmallLie.UnitarySix
