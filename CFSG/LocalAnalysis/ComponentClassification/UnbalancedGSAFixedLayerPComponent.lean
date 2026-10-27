module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSANestedFixedLayer

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup

namespace FixedLayerPComponent

theorem map_pLayer_mulEquiv {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (p : ℕ) [Fact p.Prime] (e : G ≃* G') : (pLayer G p).map e.toMonoidHom = pLayer G' p := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport p
      Fact.out e).1 L).1 hL)
  · refine sSup_le fun L hL => ?_
    have h := ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport p Fact.out
      e.symm).1 L).1 hL
    have hL' : (L.map e.symm.toMonoidHom).map e.toMonoidHom = L := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id L
      ext x
      simp
    rw [← hL']
    exact Subgroup.map_mono (le_sSup h)

theorem primeResidual_eq_top_of_eq_closure {G : Type*} [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] {T C : Subgroup G} (hTC : T ≤ C)
    (hT : T = closure {x : G | x ∈ C ∧ ∃ k : ℕ, orderOf x = p ^ k}) :
    CatalogueBPrimeJoin.primeResidual p T = ⊤ := by
  have hset : {x : G | x ∈ T ∧ ∃ k : ℕ, orderOf x = p ^ k} =
      {x : G | x ∈ C ∧ ∃ k : ℕ, orderOf x = p ^ k} := by
    ext x
    constructor
    · rintro ⟨hx, hk⟩
      exact ⟨hTC hx, hk⟩
    · rintro ⟨hx, hk⟩
      refine ⟨?_, hk⟩
      rw [hT]
      exact Subgroup.subset_closure ⟨hx, hk⟩
  have hV := CatalogueBPrimeJoin.closure_pElements_eq_map_primeResidual p T
  rw [hset, ← hT] at hV
  apply map_injective T.subtype_injective
  rw [← hV, ← MonoidHom.range_eq_map, range_subtype]

end FixedLayerPComponent

open FixedLayerPComponent NestedFixedLayer

theorem trivial_quotient_action_fixed_layer_is_p_component {H : Type*} [Group H] [Finite H]
    (p : ℕ) [Fact p.Prime] (J : Subgroup H) (hJ : J.IsSubnormal) (B : Subgroup H)
    (hBN : B ≤ normalizer (J : Set H)) (hB : IsPGroup p B)
    (hQ : IsQuasisimple (J ⧸ pPrimeCore p J))
    (hcomm : ⁅J, B⁆ ≤ (pPrimeCore p J).map J.subtype)
    (C : Subgroup H) (hC : C = J ⊓ centralizer (B : Set H))
    (T : Subgroup H) (hT : T = (pLayer C p).map C.subtype) :
    T ⊔ (pPrimeCore p J).map J.subtype = J ∧
      (pPrimeCore p T).map T.subtype = T ⊓ (pPrimeCore p J).map J.subtype ∧
      (∃ e : T ⧸ pPrimeCore p T ≃* J ⧸ pPrimeCore p J,
        ∀ (t : T) (j : J), (t : H) = j → e t = j) ∧
      T = closure {x : H | x ∈ C ∧ ∃ k : ℕ, orderOf x = p ^ k} ∧
      IsPComponent p (T.subgroupOf (centralizer (B : Set H))) ∧
      (J.Normal → (T.subgroupOf (centralizer (B : Set H))).Normal) := by
  have hCJ : C ≤ J := hC ▸ inf_le_left
  have hCZ : C ≤ centralizer (B : Set H) := hC ▸ inf_le_right
  let α : B →* MulAut J := J.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hα : ∀ (b : B) (j : J), ((α b j : J) : H) = (b : H) * j * (b : H)⁻¹ := fun b j =>
    Subgroup.normalizerMonoidHom_apply_apply_coe J _ j
  have htriv : ∀ (b : B) (j : J),
      ((α b j : J) : J ⧸ pPrimeCore p J) = (j : J ⧸ pPrimeCore p J) := by
    intro b j
    rw [eq_comm, QuotientGroup.eq]
    have hmem : ((j⁻¹ * α b j : J) : H) ∈ (pPrimeCore p J).map J.subtype := by
      apply hcomm
      have h := Subgroup.commutator_mem_commutator (inv_mem j.2) b.2
      rw [commutatorElement_def, inv_inv] at h
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hα, ← mul_assoc, ← mul_assoc]
      exact h
    obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.mp hmem
    rwa [show o = j⁻¹ * α b j from Subtype.ext hoeq] at ho
  have hCmem : ∀ j : J, j ∈ C.subgroupOf J ↔ ∀ b : B, α b j = j := by
    intro j
    rw [Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, h⟩ b
      apply Subtype.ext
      rw [hα, h b b.2, mul_inv_cancel_right]
    · intro h
      refine ⟨j.2, fun b hb => ?_⟩
      have h' := congrArg Subtype.val (h ⟨b, hb⟩)
      rw [hα] at h'
      exact mul_inv_eq_iff_eq_mul.mp h'
  set T' : Subgroup J := (pLayer (C.subgroupOf J) p).map (C.subgroupOf J).subtype with hT'
  obtain ⟨h1, h2, e', he'⟩ :=
    fixed_prime_layer_covers_core_quotient p hB α hQ htriv _ hCmem T' hT'
  have h4 := fixed_prime_layer_eq_closure p hB α hQ htriv _ hCmem T' hT'
  have hTT' : T'.map J.subtype = T := by
    rw [hT, hT', Subgroup.map_map]
    let φ : C.subgroupOf J ≃* C := Subgroup.subgroupOfEquivOfLe hCJ
    have hcomp : J.subtype.comp (C.subgroupOf J).subtype = C.subtype.comp φ.toMonoidHom := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, map_pLayer_mulEquiv p φ]
  cases hTT'
  have hJ1 : T'.map J.subtype ⊔ (pPrimeCore p J).map J.subtype = J := by
    rw [← Subgroup.map_sup, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let ψ : T' ≃* T'.map J.subtype := T'.equivMapOfInjective J.subtype J.subtype_injective
  have hψ := pPrimeCore_map_iso p ψ
  have hJ2 : (pPrimeCore p (T'.map J.subtype)).map (T'.map J.subtype).subtype =
      T'.map J.subtype ⊓ (pPrimeCore p J).map J.subtype := by
    rw [← hψ, Subgroup.map_map]
    have hcomp : (T'.map J.subtype).subtype.comp ψ.toMonoidHom = J.subtype.comp T'.subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, h2, Subgroup.map_inf_eq _ _ _ J.subtype_injective]
  have hJ3 : ∃ e : T'.map J.subtype ⧸ pPrimeCore p (T'.map J.subtype) ≃* J ⧸ pPrimeCore p J,
      ∀ (t : T'.map J.subtype) (j : J), (t : H) = j → e t = j := by
    refine ⟨(QuotientGroup.congr (pPrimeCore p T') (pPrimeCore p (T'.map J.subtype)) ψ
      hψ).symm.trans e', fun t j htj => ?_⟩
    have hsymm : (QuotientGroup.congr (pPrimeCore p T') (pPrimeCore p (T'.map J.subtype)) ψ
        hψ).symm (t : T'.map J.subtype ⧸ pPrimeCore p (T'.map J.subtype)) =
        ((ψ.symm t : T') : T' ⧸ pPrimeCore p T') := by
      rw [MulEquiv.symm_apply_eq]
      change (t : T'.map J.subtype ⧸ pPrimeCore p (T'.map J.subtype)) =
        ((ψ (ψ.symm t) : T'.map J.subtype) : T'.map J.subtype ⧸ pPrimeCore p (T'.map J.subtype))
      rw [MulEquiv.apply_symm_apply]
    rw [MulEquiv.trans_apply, hsymm, he']
    congr 1
    have hx : ((ψ (ψ.symm t)) : H) = (((ψ.symm t : T') : J) : H) := rfl
    rw [MulEquiv.apply_symm_apply] at hx
    exact Subtype.ext (hx.symm.trans htj)
  have hJ4 : T'.map J.subtype = closure {x : H | x ∈ C ∧ ∃ k : ℕ, orderOf x = p ^ k} := by
    rw [h4, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
      exact ⟨hy, k, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]; exact hk⟩
    · rintro ⟨hx, k, hk⟩
      exact ⟨⟨x, hCJ hx⟩, ⟨hx, k, by rw [Subgroup.orderOf_mk]; exact hk⟩, rfl⟩
  have hTres : T'.map J.subtype = (CatalogueBPrimeJoin.primeResidual p C).map C.subtype := by
    rw [hJ4, CatalogueBPrimeJoin.closure_pElements_eq_map_primeResidual]
  have hTC : T'.map J.subtype ≤ C := by
    rw [hTres]
    exact map_subtype_le _
  have hnorm : normalizer (C : Set H) ≤ normalizer ((T'.map J.subtype : Subgroup H) : Set H) := by
    rw [hTres]
    exact CatalogueBPrimeJoin.primeResidual_normalizer_le p C
  have hTZ : T'.map J.subtype ≤ centralizer (B : Set H) := hTC.trans hCZ
  refine ⟨hJ1, hJ2, hJ3, hJ4, ?_, ?_⟩
  ·
    rw [CatalogueBPrimeJoin.pComponent_subgroupOf_iff p _ _ hTZ]
    refine ⟨?_, primeResidual_eq_top_of_eq_closure p hTC hJ4, ?_⟩
    · have hCsub : (C.subgroupOf (centralizer (B : Set H))).IsSubnormal := by
        rw [hC, Subgroup.inf_subgroupOf_right]
        exact hJ.subgroupOf
      have hTnorm : ((T'.map J.subtype).subgroupOf (centralizer (B : Set H))).subgroupOf
          (C.subgroupOf (centralizer (B : Set H))) |>.Normal := by
        rw [Subgroup.normal_subgroupOf_iff
          (H := (T'.map J.subtype).subgroupOf (centralizer (B : Set H)))
          (K := C.subgroupOf (centralizer (B : Set H))) fun x hx => hTC hx]
        intro h k hh hk
        exact (Subgroup.mem_normalizer_iff.mp (hnorm (Subgroup.le_normalizer hk)) h).mp hh
      exact Subgroup.IsSubnormal.trans
        (H := (T'.map J.subtype).subgroupOf (centralizer (B : Set H)))
        (K := C.subgroupOf (centralizer (B : Set H))) (fun x hx => hTC hx) hTnorm.isSubnormal
        hCsub
    · obtain ⟨e, -⟩ := hJ3
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ
  ·
    intro hJn
    rw [Subgroup.normal_subgroupOf_iff hTZ]
    intro t z ht hz
    have hzJ : ∀ c, c ∈ J ↔ z * c * z⁻¹ ∈ J := fun c =>
      ⟨fun h => hJn.conj_mem c h z, fun h => by
        have h' := hJn.conj_mem _ h z⁻¹
        simpa [mul_assoc] using h'⟩
    have hzZ := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hz)
    have hzC : z ∈ normalizer (C : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro c
      rw [hC, Subgroup.mem_inf, Subgroup.mem_inf]
      exact and_congr (hzJ c) (hzZ c)
    exact (Subgroup.mem_normalizer_iff.mp (hnorm hzC) t).mp ht

end CFSG.ComponentClassification.UnbalancedGS
