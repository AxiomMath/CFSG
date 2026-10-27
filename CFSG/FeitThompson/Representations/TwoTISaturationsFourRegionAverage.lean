module

public import CFSG.FeitThompson.Representations.CoprimeOrdersDisjointPuncturedSupports
public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
public import CFSG.FeitThompson.Definitions.PowerOperationOnClassFunctions
public import Mathlib.Basic.Complex.Basic

open MulAction Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] {H K : Subgroup G}

private theorem finsum_mem_const {α : Type*} {M : Type*} [AddCommMonoid M] {s : Set α}
    (hs : s.Finite) (c : M) : ∑ᶠ _ ∈ s, c = s.ncard • c := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, Set.ncard_eq_toFinset_card s hs]

theorem conjAct_smul_set_eq (g : G) (D : Set G) :
    (ConjAct.toConjAct g) • D = MulAut.conj g '' D := by
  ext x; simp [Set.mem_smul_set, ConjAct.smul_def]

theorem conjAct_smul_set_eq' (c : ConjAct G) (D : Set G) :
    c • D = MulAut.conj (ConjAct.ofConjAct c) '' D := conjAct_smul_set_eq _ D

theorem sUnion_orbit_conjAct (D : Set G) :
    ⋃₀ (orbit (ConjAct G) D) = Group.conjugatesOfSet D := by
  ext x
  simp only [Set.mem_sUnion, Group.mem_conjugatesOfSet_iff, MulAction.mem_orbit_iff, isConj_iff]
  constructor
  · rintro ⟨E, ⟨c, rfl⟩, hx⟩
    rw [conjAct_smul_set_eq' c D] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a, ha, ConjAct.ofConjAct c, rfl⟩
  · rintro ⟨a, ha, c, rfl⟩
    exact ⟨MulAut.conj c '' D, ⟨ConjAct.toConjAct c, conjAct_smul_set_eq c D⟩, ⟨a, ha, rfl⟩⟩

theorem index_normalizer_eq_ncard_orbit [Finite G] (D : Set G) :
    (Subgroup.normalizer D).index = (orbit (ConjAct G) D).ncard := by
  have hcomap : (stabilizer (ConjAct G) D).comap
      (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom = Subgroup.normalizer D := by
    ext g
    simp only [Subgroup.mem_comap, mem_stabilizer_iff, Subgroup.mem_normalizer_iff_conj_image_eq,
      MulEquiv.coe_toMonoidHom, conjAct_smul_set_eq]
  rw [← hcomap, Subgroup.index_comap_of_surjective _ (ConjAct.toConjAct (G := G)).surjective,
    MulAction.index_stabilizer]

theorem IsTIWithNormalizer.pairwiseDisjoint_orbit {D : Set G} {L : Subgroup G}
    (h : IsTIWithNormalizer D L) : (orbit (ConjAct G) D).PairwiseDisjoint id := by
  rintro E ⟨c, rfl⟩ F ⟨d, rfl⟩ hEF
  replace hEF : c • D ≠ d • D := hEF
  change Disjoint (id (c • D)) (id (d • D))
  set g := ConjAct.ofConjAct c with hg
  set k := ConjAct.ofConjAct d with hk
  rw [id_eq, id_eq, conjAct_smul_set_eq' c D, conjAct_smul_set_eq' d D, ← hg, ← hk]
  rw [conjAct_smul_set_eq' c D, conjAct_smul_set_eq' d D, ← hg, ← hk] at hEF
  by_cases hgk : g⁻¹ * k ∈ L
  · refine absurd ?_ hEF
    have hcomp : MulAut.conj g '' (MulAut.conj (g⁻¹ * k) '' D) = MulAut.conj k '' D := by
      rw [Set.image_image]
      refine Set.image_congr' fun x => ?_
      simp only [MulAut.conj_apply]
      group
    rw [← hcomp, h.conj_image_eq_of_mem hgk]
  · exact h.disjoint_conj_image_conj_image hgk

theorem IsTIWithNormalizer.finsum_mem_conjugatesOfSet {M : Type*} [AddCommMonoid M] [Finite G]
    {D : Set G} {L : Subgroup G} (h : IsTIWithNormalizer D L) {f : G → M} (hf : IsClassFun f) :
    ∑ᶠ x ∈ Group.conjugatesOfSet D, f x = L.index • ∑ᶠ x ∈ D, f x := by
  have horb : (orbit (ConjAct G) D).Finite := Set.toFinite _
  rw [← sUnion_orbit_conjAct D,
    finsum_mem_sUnion h.pairwiseDisjoint_orbit horb fun E _ => Set.toFinite E]
  have hstep : ∀ E ∈ orbit (ConjAct G) D, ∑ᶠ x ∈ E, f x = ∑ᶠ x ∈ D, f x := by
    rintro E ⟨c, rfl⟩
    change ∑ᶠ x ∈ c • D, f x = _
    rw [conjAct_smul_set_eq' c D, finsum_mem_image ((MulAut.conj _).injective.injOn)]
    exact finsum_mem_congr rfl fun x _ => hf.conj _ _
  rw [finsum_mem_congr rfl hstep, finsum_mem_const horb,
    ← index_normalizer_eq_ncard_orbit D, h.normalizer_eq]

theorem mem_conjugatesOfSet_coe_iff {x : G} :
    x ∈ Group.conjugatesOfSet (H : Set G) ↔ ∃ g : G, g * x * g⁻¹ ∈ H := by
  simp only [Group.mem_conjugatesOfSet_iff, SetLike.mem_coe, isConj_iff]
  constructor
  · rintro ⟨a, haH, c, rfl⟩
    exact ⟨c⁻¹, by simpa [mul_assoc] using haH⟩
  · rintro ⟨g, hg⟩
    exact ⟨g * x * g⁻¹, hg, g⁻¹, by group⟩

theorem one_mem_conjugatesOfSet_coe (H : Subgroup G) :
    (1 : G) ∈ Group.conjugatesOfSet (H : Set G) :=
  mem_conjugatesOfSet_coe_iff.2 ⟨1, by simp⟩

theorem conjugatesOfSet_coe_sdiff_one (H : Subgroup G) :
    Group.conjugatesOfSet (H : Set G) \ {1} = puncturedConjSupport H := by
  ext x
  rw [mem_puncturedConjSupport_iff, Set.mem_sdiff, Set.mem_singleton_iff,
    mem_conjugatesOfSet_coe_iff]

theorem conjugatesOfSet_sdiff_one (H : Subgroup G) :
    Group.conjugatesOfSet ((H : Set G) \ {1}) = Group.conjugatesOfSet (H : Set G) \ {1} := by
  rw [conjugatesOfSet_coe_sdiff_one]
  ext x
  rw [mem_puncturedConjSupport_iff]
  simp only [Group.mem_conjugatesOfSet_iff, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    isConj_iff]
  constructor
  · rintro ⟨a, ⟨haH, ha1⟩, c, rfl⟩
    exact ⟨⟨c⁻¹, by simpa [mul_assoc] using haH⟩, by simpa using ha1⟩
  · rintro ⟨⟨g, hg⟩, hx⟩
    exact ⟨g * x * g⁻¹, ⟨hg, by simpa using hx⟩, g⁻¹, by group⟩

theorem image_conj_sdiff_one (g : G) (s : Set G) :
    MulAut.conj g '' (s \ {1}) = (MulAut.conj g '' s) \ {1} := by
  rw [Set.image_sdiff (MulAut.conj g).injective]; simp

theorem normalizer_sdiff_one (H : Subgroup G) :
    Subgroup.normalizer ((H : Set G) \ {1}) = Subgroup.normalizer (H : Set G) := by
  ext g
  simp only [Subgroup.mem_normalizer_iff_conj_image_eq, image_conj_sdiff_one]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have h1 : (1 : G) ∈ MulAut.conj g '' (H : Set G) := ⟨1, H.one_mem, by simp⟩
  calc MulAut.conj g '' (H : Set G)
      = insert 1 (MulAut.conj g '' (H : Set G) \ {1}) := by
        rw [Set.insert_sdiff_singleton, Set.insert_eq_self.2 h1]
    _ = insert 1 ((H : Set G) \ {1}) := by rw [h]
    _ = (H : Set G) := by
        rw [Set.insert_sdiff_singleton, Set.insert_eq_self.2 (SetLike.mem_coe.2 H.one_mem)]

theorem isTIWithNormalizer_sdiff_one (hH : H ≠ ⊥)
    (hTI : ∀ g : G, g ∉ Subgroup.normalizer (H : Set G) →
      ((H : Set G) \ {1}) ∩ (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = ∅) :
    IsTIWithNormalizer ((H : Set G) \ {1}) (Subgroup.normalizer (H : Set G)) where
  nonempty := by
    obtain ⟨⟨x, hxH⟩, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
    exact ⟨x, hxH, by simpa using hx⟩
  one_notMem := by simp
  normalizer_eq := normalizer_sdiff_one H
  disjoint_conj_image := by
    intro g hg
    have hg' : g⁻¹ ∉ Subgroup.normalizer (H : Set G) := fun hc => hg (by simpa using inv_mem hc)
    refine (Set.disjoint_iff_inter_eq_empty.mpr (hTI g⁻¹ hg')).mono_right (le_of_eq ?_)
    exact Set.image_congr' fun x => by simp

private theorem ncard_coe_subgroup (L : Subgroup G) : (L : Set G).ncard = Nat.card L :=
  (Nat.card_coe_set_eq (L : Set G)).symm

variable [Finite G]

private theorem index_nsmul_div_natCard (L : Subgroup G) (z : ℂ) :
    (L.index • z) / (Nat.card G : ℂ) = z / (Nat.card L : ℂ) := by
  have hcard : (Nat.card G : ℂ) = (L.index : ℂ) * (Nat.card L : ℂ) := by
    rw [← Nat.cast_mul, L.index_mul_card]
  rw [nsmul_eq_mul, hcard, mul_div_mul_left _ _ (by exact_mod_cast L.index_ne_zero_of_finite)]

omit [Group G] in
private theorem finsum_mem_one (s : Set G) : ∑ᶠ _ ∈ s, (1 : ℂ) = (s.ncard : ℂ) := by
  rw [finsum_mem_const (Set.toFinite _), nsmul_eq_mul, mul_one]

private theorem cast_ncard_sdiff_one (L : Subgroup G) :
    ((((L : Set G) \ {1}).ncard : ℂ)) = (Nat.card L : ℂ) - 1 := by
  rw [Set.ncard_sdiff_singleton_of_mem (SetLike.mem_coe.2 L.one_mem), ncard_coe_subgroup,
    Nat.cast_sub Nat.card_pos, Nat.cast_one]

theorem finsum_eq_of_two_ti_saturations {f : G → ℂ} (hf : IsClassFun f)
    (hH : H ≠ ⊥) (hK : K ≠ ⊥)
    (hTIH : ∀ g : G, g ∉ Subgroup.normalizer (H : Set G) →
      ((H : Set G) \ {1}) ∩ (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = ∅)
    (hTIK : ∀ g : G, g ∉ Subgroup.normalizer (K : Set G) →
      ((K : Set G) \ {1}) ∩ (fun x => g⁻¹ * x * g) '' ((K : Set G) \ {1}) = ∅)
    (hHK : (Group.conjugatesOfSet (H : Set G) \ {1}) ∩
      (Group.conjugatesOfSet (K : Set G) \ {1}) = ∅) :
    ∑ᶠ x : G, f x = f 1
      + (Subgroup.normalizer (H : Set G)).index • ∑ᶠ x ∈ (H : Set G) \ {1}, f x
      + (Subgroup.normalizer (K : Set G)).index • ∑ᶠ x ∈ (K : Set G) \ {1}, f x
      + ∑ᶠ x ∈ (Group.conjugatesOfSet (H : Set G) ∪
          Group.conjugatesOfSet (K : Set G))ᶜ, f x := by
  set P := Group.conjugatesOfSet (H : Set G) \ {1} with hP
  set Q := Group.conjugatesOfSet (K : Set G) \ {1} with hQ
  have hone : Group.conjugatesOfSet (H : Set G) ∪ Group.conjugatesOfSet (K : Set G)
      = ({1} : Set G) ∪ (P ∪ Q) := by
    rw [hP, hQ]
    ext x
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
    by_cases hx : x = 1 <;>
      simp [hx, one_mem_conjugatesOfSet_coe H, one_mem_conjugatesOfSet_coe K]
  have h1P : (1 : G) ∉ P := by simp [hP]
  have h1Q : (1 : G) ∉ Q := by simp [hQ]
  have hPQ : Disjoint P Q := Set.disjoint_iff_inter_eq_empty.mpr hHK
  have huniv : (Set.univ : Set G) = (({1} : Set G) ∪ (P ∪ Q)) ∪
      (Group.conjugatesOfSet (H : Set G) ∪ Group.conjugatesOfSet (K : Set G))ᶜ := by
    rw [← hone, Set.union_compl_self]
  have hsatH : ∑ᶠ x ∈ P, f x =
      (Subgroup.normalizer (H : Set G)).index • ∑ᶠ x ∈ (H : Set G) \ {1}, f x := by
    rw [hP, ← conjugatesOfSet_sdiff_one H]
    exact (isTIWithNormalizer_sdiff_one hH hTIH).finsum_mem_conjugatesOfSet hf
  have hsatK : ∑ᶠ x ∈ Q, f x =
      (Subgroup.normalizer (K : Set G)).index • ∑ᶠ x ∈ (K : Set G) \ {1}, f x := by
    rw [hQ, ← conjugatesOfSet_sdiff_one K]
    exact (isTIWithNormalizer_sdiff_one hK hTIK).finsum_mem_conjugatesOfSet hf
  rw [← finsum_mem_univ, huniv,
    finsum_mem_union (by rw [hone]; exact disjoint_compl_right) (Set.toFinite _)
      (Set.toFinite _),
    finsum_mem_union (by
        simp only [Set.disjoint_union_right, Set.disjoint_singleton_left]
        exact ⟨h1P, h1Q⟩) (Set.toFinite _) (Set.toFinite _),
    finsum_mem_union hPQ (Set.toFinite _) (Set.toFinite _), finsum_mem_singleton,
    hsatH, hsatK]
  ring

theorem finsum_div_natCard_eq_of_two_ti_saturations {f : G → ℂ} (hf : IsClassFun f)
    (hH : H ≠ ⊥) (hK : K ≠ ⊥)
    (hTIH : ∀ g : G, g ∉ Subgroup.normalizer (H : Set G) →
      ((H : Set G) \ {1}) ∩ (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = ∅)
    (hTIK : ∀ g : G, g ∉ Subgroup.normalizer (K : Set G) →
      ((K : Set G) \ {1}) ∩ (fun x => g⁻¹ * x * g) '' ((K : Set G) \ {1}) = ∅)
    (hHK : (Group.conjugatesOfSet (H : Set G) \ {1}) ∩
      (Group.conjugatesOfSet (K : Set G) \ {1}) = ∅) :
    (∑ᶠ x : G, f x) / (Nat.card G : ℂ)
      = f 1 / (Nat.card G : ℂ)
        + (∑ᶠ x ∈ (H : Set G) \ {1}, f x) /
            (Nat.card (Subgroup.normalizer (H : Set G)) : ℂ)
        + (∑ᶠ x ∈ (K : Set G) \ {1}, f x) /
            (Nat.card (Subgroup.normalizer (K : Set G)) : ℂ)
        + (∑ᶠ x ∈ (Group.conjugatesOfSet (H : Set G) ∪
            Group.conjugatesOfSet (K : Set G))ᶜ, f x) / (Nat.card G : ℂ) := by
  rw [finsum_eq_of_two_ti_saturations hf hH hK hTIH hTIK hHK, add_div, add_div, add_div,
    index_nsmul_div_natCard, index_nsmul_div_natCard]

theorem ncard_compl_div_natCard_of_two_ti_saturations (hH : H ≠ ⊥) (hK : K ≠ ⊥)
    (hTIH : ∀ g : G, g ∉ Subgroup.normalizer (H : Set G) →
      ((H : Set G) \ {1}) ∩ (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = ∅)
    (hTIK : ∀ g : G, g ∉ Subgroup.normalizer (K : Set G) →
      ((K : Set G) \ {1}) ∩ (fun x => g⁻¹ * x * g) '' ((K : Set G) \ {1}) = ∅)
    (hHK : (Group.conjugatesOfSet (H : Set G) \ {1}) ∩
      (Group.conjugatesOfSet (K : Set G) \ {1}) = ∅) :
    (((Group.conjugatesOfSet (H : Set G) ∪ Group.conjugatesOfSet (K : Set G))ᶜ.ncard : ℂ))
        / (Nat.card G : ℂ)
      = 1 - 1 / (Nat.card G : ℂ)
        - ((Nat.card H : ℂ) - 1) / (Nat.card (Subgroup.normalizer (H : Set G)) : ℂ)
        - ((Nat.card K : ℂ) - 1) / (Nat.card (Subgroup.normalizer (K : Set G)) : ℂ) := by
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have key := finsum_div_natCard_eq_of_two_ti_saturations
    (f := fun _ : G => (1 : ℂ)) (isClassFun_const 1) hH hK hTIH hTIK hHK
  rw [← finsum_mem_univ, finsum_mem_one, finsum_mem_one, finsum_mem_one, finsum_mem_one,
    Set.ncard_univ, cast_ncard_sdiff_one, cast_ncard_sdiff_one, div_self hG] at key
  linear_combination -key

end

end CFSG.FeitThompson
