module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

open CFSG

variable {X : Type*} [Group X] (p : ℕ)

@[expose] def canonicalPrimeLift (K : Subgroup (X ⧸ pPrimeCore p X)) : Subgroup X :=
  Subgroup.closure {x : X | x ∈ K.comap (QuotientGroup.mk' (pPrimeCore p X)) ∧
    ∃ k : ℕ, orderOf x = p ^ k}

theorem comap_restrict_surjective (K : Subgroup (X ⧸ pPrimeCore p X)) :
    Function.Surjective (((QuotientGroup.mk' (pPrimeCore p X)).comp
      (K.comap (QuotientGroup.mk' (pPrimeCore p X))).subtype).codRestrict K fun x => x.2) := by
  intro k
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (pPrimeCore p X) (k : X ⧸ pPrimeCore p X)
  have hxV : x ∈ K.comap (QuotientGroup.mk' (pPrimeCore p X)) := by
    change QuotientGroup.mk' (pPrimeCore p X) x ∈ K
    rw [hx]
    exact k.2
  exact ⟨⟨x, hxV⟩, Subtype.ext hx⟩

variable [Finite X] [Fact p.Prime]

theorem closure_pElements_eq_map_primeResidual (V : Subgroup X) :
    Subgroup.closure {x : X | x ∈ V ∧ ∃ k : ℕ, orderOf x = p ^ k} =
      (primeResidual p V).map V.subtype := by
  rw [primeResidual_eq_closure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩, rfl⟩
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨y.2, k, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]; exact hk⟩

theorem canonicalPrimeLift_le (K : Subgroup (X ⧸ pPrimeCore p X)) (J : Subgroup X)
    (hJ : J.IsSubnormal) (hJK : J.map (QuotientGroup.mk' (pPrimeCore p X)) = K) :
    canonicalPrimeLift p K ≤ J := by
  let V := K.comap (QuotientGroup.mk' (pPrimeCore p X))
  have hJV : J ≤ V := fun x hx => by
    change QuotientGroup.mk' (pPrimeCore p X) x ∈ K
    rw [← hJK]
    exact Subgroup.mem_map_of_mem _ hx
  have hNV : pPrimeCore p X ≤ V := fun x hx => by
    have h1 : QuotientGroup.mk' (pPrimeCore p X) x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    change QuotientGroup.mk' (pPrimeCore p X) x ∈ K
    rw [h1]
    exact K.one_mem
  let f : V →* K := ((QuotientGroup.mk' (pPrimeCore p X)).comp V.subtype).codRestrict K
    fun x => x.2
  have hf : Function.Surjective f := comap_restrict_surjective p K
  have hkerEq : f.ker = (pPrimeCore p X).subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hker : p.Coprime (Nat.card f.ker) := by
    rw [hkerEq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNV).toEquiv]
    exact pPrimeCore_coprime_card
  have hJ' : Function.Surjective (f.domRestrict (J.subgroupOf V)) := by
    intro k
    have hk : (k : X ⧸ pPrimeCore p X) ∈ J.map (QuotientGroup.mk' (pPrimeCore p X)) :=
      hJK.symm ▸ k.2
    obtain ⟨j, hj, hjk⟩ := Subgroup.mem_map.1 hk
    exact ⟨⟨⟨j, hJV hj⟩, hj⟩, Subtype.ext hjk⟩
  have hindex := coprime_index_of_surjective_restriction p f hf hker (J.subgroupOf V) hJ'
  have hle := primeResidual_le_subnormal_of_coprime_index p (J.subgroupOf V) hJ.subgroupOf hindex
  rw [canonicalPrimeLift, closure_pElements_eq_map_primeResidual]
  calc (primeResidual p V).map V.subtype ≤ (J.subgroupOf V).map V.subtype :=
        Subgroup.map_mono hle
    _ ≤ J := by
        rw [Subgroup.subgroupOf_map_subtype]
        exact inf_le_left

theorem canonicalPrimeLift_isPComponent (K : Subgroup (X ⧸ pPrimeCore p X)) (hK : IsComponent K) :
    IsPComponent p (canonicalPrimeLift p K) ∧
      (canonicalPrimeLift p K).map (QuotientGroup.mk' (pPrimeCore p X)) = K := by
  let V := K.comap (QuotientGroup.mk' (pPrimeCore p X))
  have hVsub : V.IsSubnormal := hK.2.comap _
  have hKcore : pPrimeCore p K = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection p K hK.2,
      pPrimeCore_quotient_pPrimeCore_eq_bot, Subgroup.bot_subgroupOf]
  have hKres : primeResidual p K = ⊤ :=
    primeResidual_eq_top_of_corefree_quasisimple p hK.1 hKcore
  let f : V →* K := ((QuotientGroup.mk' (pPrimeCore p X)).comp V.subtype).codRestrict K
    fun x => x.2
  have hf : Function.Surjective f := comap_restrict_surjective p K
  have hLeq : canonicalPrimeLift p K = (primeResidual p V).map V.subtype :=
    closure_pElements_eq_map_primeResidual p V
  rw [hLeq]
  have hmap : ((primeResidual p V).map V.subtype).map (QuotientGroup.mk' (pPrimeCore p X)) =
      K := by
    have hcomp : (QuotientGroup.mk' (pPrimeCore p X)).comp V.subtype = K.subtype.comp f := rfl
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, primeResidual_map_surjective p f hf, hKres,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨?_, hmap⟩
  have hLsub : ((primeResidual p V).map V.subtype).IsSubnormal := by
    have := primeResidual_characteristic p V
    have hn : (primeResidual p V).Normal := inferInstance
    exact hn.isSubnormal.trans' hVsub
  have hRtop : primeResidual p (primeResidual p V) = ⊤ := by
    have hid := primeResidual_idempotent p V
    refine eq_top_iff.2 fun x _ => ?_
    have hx : (x : V) ∈ (primeResidual p (primeResidual p V)).map (primeResidual p V).subtype :=
      hid.symm ▸ x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    rwa [← Subtype.ext hyx]
  have hLres : primeResidual p ((primeResidual p V).map V.subtype) = ⊤ := by
    let e := (primeResidual p V).equivMapOfInjective V.subtype V.subtype_injective
    rw [← primeResidual_map_equiv p e, hRtop]
    exact Subgroup.map_top_of_surjective _ e.surjective
  have hLq : IsQuasisimple (((primeResidual p V).map V.subtype) ⧸
      pPrimeCore p ((primeResidual p V).map V.subtype)) :=
    (quotient_component_iff_core_quotient p _ hLsub).1 (hmap ▸ hK)
  exact (pComponent_iff_subnormal_generated_quasisimple p _).2 ⟨hLsub, hLres, hLq⟩

theorem canonical_prime_component_lift :
    (∀ K : Subgroup (X ⧸ pPrimeCore p X), IsComponent K →
      IsPComponent p (canonicalPrimeLift p K) ∧
        (canonicalPrimeLift p K).map (QuotientGroup.mk' (pPrimeCore p X)) = K ∧
        (∀ J : Subgroup X, J.IsSubnormal → J.map (QuotientGroup.mk' (pPrimeCore p X)) = K →
          canonicalPrimeLift p K ≤ J) ∧
        ∀ M : Subgroup X, IsPComponent p M →
          M.map (QuotientGroup.mk' (pPrimeCore p X)) = K → M = canonicalPrimeLift p K) ∧
    Set.BijOn (fun L : Subgroup X => L.map (QuotientGroup.mk' (pPrimeCore p X)))
      {L | IsPComponent p L} {K | IsComponent K} := by
  have huniq : ∀ (K : Subgroup (X ⧸ pPrimeCore p X)), IsComponent K → ∀ M : Subgroup X,
      IsPComponent p M → M.map (QuotientGroup.mk' (pPrimeCore p X)) = K →
        M = canonicalPrimeLift p K := by
    intro K hK M hM hMK
    obtain ⟨K', -, hMsub, hMK', hmin⟩ := hM
    have hKK' : K' = K := hMK'.symm.trans hMK
    subst hKK'
    obtain ⟨hL, hLK⟩ := canonicalPrimeLift_isPComponent p K' hK
    have hle := canonicalPrimeLift_le p K' M hMsub hMK
    by_contra hne
    exact hmin _ (lt_of_le_of_ne hle (Ne.symm hne)) hL.choose_spec.2.1 hLK
  refine ⟨fun K hK => ⟨(canonicalPrimeLift_isPComponent p K hK).1,
    (canonicalPrimeLift_isPComponent p K hK).2, fun J hJ hJK => canonicalPrimeLift_le p K J hJ hJK,
    huniq K hK⟩, ?_, ?_, ?_⟩
  · intro M hM
    obtain ⟨K, hK, -, hMK, -⟩ := hM
    change IsComponent (M.map (QuotientGroup.mk' (pPrimeCore p X)))
    rw [hMK]
    exact hK
  · intro M₁ hM₁ M₂ hM₂ h
    obtain ⟨K, hK, -, hM₁K, -⟩ := id hM₁
    have h₂ : M₂.map (QuotientGroup.mk' (pPrimeCore p X)) = K := h.symm.trans hM₁K
    rw [huniq K hK M₁ hM₁ hM₁K, huniq K hK M₂ hM₂ h₂]
  · intro K hK
    exact ⟨canonicalPrimeLift p K, (canonicalPrimeLift_isPComponent p K hK).1,
      (canonicalPrimeLift_isPComponent p K hK).2⟩

end CFSG.ComponentClassification.CatalogueBPrimeJoin
