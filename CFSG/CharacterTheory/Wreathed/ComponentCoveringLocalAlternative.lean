module

public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalActions

public noncomputable section

namespace CFSG.Wreathed.ComponentCoveringLocal

open FullSylowCoveringObstruction

universe u

@[expose] def internalIntersectionSwap {X : Type u} [Group X] (K N : Subgroup X) :
    K.subgroupOf N ≃* N.subgroupOf K where
  toFun b := ⟨⟨b.val.val, b.property⟩, b.val.property⟩
  invFun b := ⟨⟨b.val.val, b.property⟩, b.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem internalIntersectionSwap_coe {X : Type u} [Group X] (K N : Subgroup X)
    (b : K.subgroupOf N) : (internalIntersectionSwap K N b).val.val = b.val.val := rfl

theorem internalIntersectionSwap_symm_coe {X : Type u} [Group X] (K N : Subgroup X)
    (b : N.subgroupOf K) : ((internalIntersectionSwap K N).symm b).val.val = b.val.val := rfl

theorem internalIntersectionSwap_odd_core {X : Type u} [Group X] {K N : Subgroup X}
    {b : K.subgroupOf N} :
    b ∈ CFSG.oddCore (K.subgroupOf N) ↔
      internalIntersectionSwap K N b ∈ CFSG.oddCore (N.subgroupOf K) := by
  have h := CFSG.ComponentClassification.OddCore.equiv_invariant
    (internalIntersectionSwap K N)
  change (CFSG.oddCore (K.subgroupOf N)).map (internalIntersectionSwap K N).toMonoidHom =
    CFSG.oddCore (N.subgroupOf K) at h
  rw [← h]
  exact (Subgroup.mem_map_iff_mem (internalIntersectionSwap K N).injective).symm

theorem odd_core_of_factorizing_subgroup
    {X : Type u} [Group X] [Finite X] (B : Subgroup X)
    (hfactor : CFSG.oddCore X ⊔ B = ⊤) :
    CFSG.oddCore B = (CFSG.oddCore X).subgroupOf B :=
  covering_odd_core_eq_kernel_intersection B hfactor

theorem component_factorization_core_intersection
    {X : Type u} [Group X] [Finite X] (K N : Subgroup X)
    (hcore : CFSG.oddCore (K.subgroupOf N) = (CFSG.oddCore N).subgroupOf (K.subgroupOf N))
    (hfactor : CFSG.oddCore K ⊔ N.subgroupOf K = ⊤) :
    (CFSG.oddCore K).map K.subtype ⊓ N = (CFSG.oddCore N).map N.subtype ⊓ K := by
  have hcoreK := odd_core_of_factorizing_subgroup (N.subgroupOf K) hfactor
  ext g
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hn⟩
    let b : K.subgroupOf N := ⟨⟨k.val, hn⟩, k.property⟩
    have hmem : internalIntersectionSwap K N b ∈ CFSG.oddCore (N.subgroupOf K) := by
      rw [hcoreK]
      exact hk
    have hb := (internalIntersectionSwap_odd_core (K := K) (N := N) (b := b)).mpr hmem
    rw [hcore] at hb
    exact ⟨⟨b.val, hb, rfl⟩, k.property⟩
  · rintro ⟨⟨v, hv, rfl⟩, hk⟩
    let b : K.subgroupOf N := ⟨v, hk⟩
    have hb : b ∈ CFSG.oddCore (K.subgroupOf N) := by
      rw [hcore]
      exact hv
    have hmem := (internalIntersectionSwap_odd_core (K := K) (N := N) (b := b)).mp hb
    rw [hcoreK] at hmem
    exact ⟨⟨(internalIntersectionSwap K N b).val, hmem, rfl⟩, v.property⟩

variable {G : Type} [Group G] [Finite G]

theorem component_order_two_factorization
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal)
    (hcard : Nat.card (coveringBaseQuotient S e K) = 2) :
    CoveringFactorizationBranch n S e K hSK := by
  have hcard' : Nat.card (Subgroup.normalizer (modelBase (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK) : Set K) ⧸
      (Subgroup.centralizer (modelBase (subgroupSylow S K hSK)
        (subgroupCoordinates S e K hSK) : Set K)).subgroupOf
        (Subgroup.normalizer (modelBase (subgroupSylow S K hSK)
          (subgroupCoordinates S e K hSK) : Set K))) = 2 :=
    (Nat.card_congr (subgroupBaseQuotientEquiv S e K hSK).toEquiv).trans hcard
  have hf := base_order_two_original_involution_factorization n hn
    (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) hcard'
  have hfK := hf.1
  rw [subgroupInvolutionCentralizer_eq] at hfK
  have hcore := original_centralizer_odd_core_eq_kernel n S e K hnormal
  exact ⟨hcard, internal_odd_core_factorization_iff_ambient_product.mp hfK, hf.2,
    component_factorization_core_intersection K (involutionCentralizer n S e) hcore hfK⟩

theorem component_cover_full_alternatives
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    (CoveringFactorizationBranch n S e K hSK ∨ CoveringTypeIObstruction n S e K) ∧
      ¬ (CoveringFactorizationBranch n S e K hSK ∧ CoveringTypeIObstruction n S e K) := by
  obtain ⟨hnormal, hodd⟩ := component_cover_image_normal_odd_index
    hnonab n hn S e hfour p f hp hpodd hf hmodel K hSK hcover
  have hv := component_v_quotient_sym3 hnonab n hn S e K hSK hnormal hodd
  refine ⟨?_, covering_branches_mutually_exclusive n S e K hSK⟩
  rcases covering_base_quotient_alternatives n hn S e K hSK with htwo | hsix
  · exact Or.inl (component_order_two_factorization n hn S e K hSK hnormal htwo)
  · obtain ⟨hS, hindex, hclass, hnonfactor⟩ :=
      covering_typeI_obstruction n hn S e K hSK hsix hv
    exact Or.inr ⟨hsix, hS, hindex, hclass, hnonfactor⟩

end CFSG.Wreathed.ComponentCoveringLocal
