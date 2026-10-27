module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAFixedPrimeLayer
public import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinSubnormal

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup

namespace NestedFixedLayer

theorem pLayer_eq_primeResidual {G Q : Type*} [Group G] [Finite G] [Group Q] (p : ℕ)
    [Fact p.Prime] (f : G →* Q) (hker : p.Coprime (Nat.card f.ker))
    (hcover : Function.Surjective (f.domRestrict (pLayer G p))) :
    pLayer G p = CatalogueBPrimeJoin.primeResidual p G := by
  have hf : Function.Surjective f := fun q => by
    obtain ⟨x, hx⟩ := hcover q
    exact ⟨x, hx⟩
  have := CatalogueBPrimeJoin.pLayer_characteristic (G := G) (p := p)
  have hindex := CatalogueBPrimeJoin.coprime_index_of_surjective_restriction p f hf hker
    (pLayer G p) hcover
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    have htop := CatalogueBPrimeJoin.primeResidual_eq_top_of_pComponent p L hL
    have hmap := CatalogueBPrimeJoin.primeResidual_map_le p L.subtype
    rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact hmap
  · exact CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index p (pLayer G p) hindex

theorem fixed_prime_layer_eq_closure {A X : Type*} [Group A] [Group X] [Finite A]
    [Finite X] (p : ℕ) [Fact p.Prime] (hA : IsPGroup p A) (α : A →* MulAut X)
    (hQ : IsQuasisimple (X ⧸ pPrimeCore p X))
    (htriv : ∀ (a : A) (x : X), ((α a x : X) : X ⧸ pPrimeCore p X) = (x : X ⧸ pPrimeCore p X))
    (C : Subgroup X) (hC : ∀ x : X, x ∈ C ↔ ∀ a : A, α a x = x)
    (T : Subgroup X) (hT : T = (pLayer C p).map C.subtype) :
    T = closure {x : X | x ∈ C ∧ ∃ k : ℕ, orderOf x = p ^ k} := by
  obtain ⟨hTN, -, -⟩ := fixed_prime_layer_covers_core_quotient p hA α hQ htriv C hC T hT
  have hcopN : p.Coprime (Nat.card (QuotientGroup.mk' (pPrimeCore p X)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact pPrimeCore_coprime_card
  have hker := CatalogueBPrimeJoin.coprime_card_restriction_kernel p
    (QuotientGroup.mk' (pPrimeCore p X)) hcopN C
  have hcover : Function.Surjective
      (((QuotientGroup.mk' (pPrimeCore p X)).domRestrict C).domRestrict (pLayer C p)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore p X) q
    have hx : x ∈ T ⊔ pPrimeCore p X := hTN ▸ Subgroup.mem_top x
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
    obtain ⟨t, ht, n, hn, rfl⟩ := hx
    rw [hT] at ht
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp ht
    refine ⟨⟨c, hc⟩, ?_⟩
    change QuotientGroup.mk' (pPrimeCore p X) (c : X) =
      QuotientGroup.mk' (pPrimeCore p X) ((c : X) * n)
    rw [map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff n).mpr hn, mul_one]
  rw [hT, pLayer_eq_primeResidual p _ hker hcover,
    CatalogueBPrimeJoin.closure_pElements_eq_map_primeResidual]

end NestedFixedLayer

open NestedFixedLayer

theorem nested_fixed_prime_layer_covering {A X : Type*} [Group A] [Group X] [Finite A]
    [Finite X] (p : ℕ) [Fact p.Prime] (hA : IsPGroup p A) (α : A →* MulAut X)
    (hQ : IsQuasisimple (X ⧸ pPrimeCore p X))
    (htriv : ∀ (a : A) (x : X), ((α a x : X) : X ⧸ pPrimeCore p X) = (x : X ⧸ pPrimeCore p X))
    (C : Subgroup A → Subgroup X)
    (hC : ∀ (B : Subgroup A) (x : X), x ∈ C B ↔ ∀ b ∈ B, α b x = x)
    (T : Subgroup A → Subgroup X) (hT : ∀ B, T B = (pLayer (C B) p).map (C B).subtype) :
    (∀ B, T B = closure {x : X | x ∈ C B ∧ ∃ k : ℕ, orderOf x = p ^ k}) ∧
      ∀ B D : Subgroup A, B ≤ D → ∃ hle : T D ≤ T B,
        T D ⊔ (pPrimeCore p (T B)).map (T B).subtype = T B ∧
        ∃ (e : T D ⧸ pPrimeCore p (T D) ≃* T B ⧸ pPrimeCore p (T B))
          (eD : T D ⧸ pPrimeCore p (T D) ≃* X ⧸ pPrimeCore p X)
          (eB : T B ⧸ pPrimeCore p (T B) ≃* X ⧸ pPrimeCore p X),
          (∀ t : T D, e t = (Subgroup.inclusion hle t : T B ⧸ pPrimeCore p (T B))) ∧
          (∀ t : T D, eD t = ((t : X) : X ⧸ pPrimeCore p X)) ∧
          (∀ t : T B, eB t = ((t : X) : X ⧸ pPrimeCore p X)) ∧
          ∀ y, eB (e y) = eD y := by
  have hCB : ∀ (B : Subgroup A) (x : X), x ∈ C B ↔ ∀ b : B, (α.comp B.subtype) b x = x :=
    fun B x => (hC B x).trans ⟨fun h b => h b b.2, fun h b hb => h ⟨b, hb⟩⟩
  have key := fun B : Subgroup A => fixed_prime_layer_covers_core_quotient p
    (hA.to_subgroup B) (α.comp B.subtype) hQ (fun b x => htriv b x) (C B) (hCB B) (T B) (hT B)
  have hclosure : ∀ B, T B = closure {x : X | x ∈ C B ∧ ∃ k : ℕ, orderOf x = p ^ k} :=
    fun B => fixed_prime_layer_eq_closure p (hA.to_subgroup B) (α.comp B.subtype) hQ
      (fun b x => htriv b x) (C B) (hCB B) (T B) (hT B)
  refine ⟨hclosure, fun B D hBD => ?_⟩
  have hCDB : C D ≤ C B := fun x hx =>
    (hC B x).mpr fun b hb => (hC D x).mp hx b (hBD hb)
  have hle : T D ≤ T B := by
    rw [hclosure D, hclosure B]
    exact Subgroup.closure_mono fun x hx => ⟨hCDB hx.1, hx.2⟩
  refine ⟨hle, ?_, ?_⟩
  · obtain ⟨hDN, -, -⟩ := key D
    obtain ⟨-, hBcore, -⟩ := key B
    refine le_antisymm (sup_le hle (map_subtype_le _)) fun t ht => ?_
    have hx : t ∈ T D ⊔ pPrimeCore p X := hDN ▸ Subgroup.mem_top t
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
    obtain ⟨d, hd, n, hn, rfl⟩ := hx
    have hnB : n ∈ T B := by
      have h := mul_mem (inv_mem (hle hd)) ht
      rwa [inv_mul_cancel_left] at h
    have hnO : n ∈ (pPrimeCore p (T B)).map (T B).subtype := by
      rw [hBcore]
      exact ⟨hnB, hn⟩
    exact mul_mem (mem_sup_left hd) (mem_sup_right hnO)
  · obtain ⟨-, -, eD, heD⟩ := key D
    obtain ⟨-, -, eB, heB⟩ := key B
    refine ⟨eD.trans eB.symm, eD, eB, fun t => ?_, heD, heB, fun y => ?_⟩
    · rw [MulEquiv.trans_apply, heD, MulEquiv.symm_apply_eq, heB]
      rfl
    · rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

end CFSG.ComponentClassification.UnbalancedGS
