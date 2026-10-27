module

public import CFSG.LocalAnalysis.ComponentClassification.CanonicalPrimeComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinSubnormal
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

open CFSG CFSG.LocalCores

variable {G H : Type*} [Group G] [Group H] {p : ℕ}

theorem primeResidual_map_subtype_primeResidual (V : Subgroup G) :
    primeResidual p ((primeResidual p V).map V.subtype) = ⊤ := by
  have hRtop : primeResidual p (primeResidual p V) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : (x : V) ∈ (primeResidual p (primeResidual p V)).map (primeResidual p V).subtype :=
      (primeResidual_idempotent p V).symm ▸ x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    rwa [← Subtype.ext hyx]
  let e := (primeResidual p V).equivMapOfInjective V.subtype V.subtype_injective
  rw [← primeResidual_map_equiv p e, hRtop]
  exact Subgroup.map_top_of_surjective _ e.surjective

variable [Finite G] [Finite H] [Fact p.Prime]

theorem exists_restrict_core_quotient_equiv (f : G →* H) (L : Subgroup G)
    (hker : ¬ p ∣ Nat.card (f.domRestrict L).ker) :
    ∃ e : L ⧸ pPrimeCore p L ≃* (L.map f) ⧸ pPrimeCore p (L.map f),
      ∀ x : L, e (x : L ⧸ pPrimeCore p L) =
        ((f.subgroupMap L x : L.map f) : (L.map f) ⧸ pPrimeCore p (L.map f)) := by
  have hg : Function.Surjective (f.subgroupMap L) := f.subgroupMap_surjective L
  have hgker : ¬ p ∣ Nat.card (f.subgroupMap L).ker := by
    have heq : (f.subgroupMap L).ker = (f.domRestrict L).ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rwa [heq]
  obtain ⟨hcomap, -⟩ := prime_complement_kernel_core_preimage (f.subgroupMap L) hg hgker
  have hφ : Function.Surjective
      ((QuotientGroup.mk' (pPrimeCore p (L.map f))).comp (f.subgroupMap L)) :=
    (QuotientGroup.mk'_surjective _).comp hg
  have hφker : pPrimeCore p L =
      ((QuotientGroup.mk' (pPrimeCore p (L.map f))).comp (f.subgroupMap L)).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  exact ⟨QuotientGroup.liftEquiv _ hφ hφker, fun x => rfl⟩

theorem prime_complement_quotient_p_component_bijection (f : G →* H)
    (hf : Function.Surjective f) (hker : ¬ p ∣ Nat.card f.ker) :
    Set.BijOn (fun L : Subgroup G => L.map f) {L | IsPComponent p L} {M | IsPComponent p M} ∧
    (∀ M : Subgroup H, IsPComponent p M →
      IsPComponent p (Subgroup.closure {x : G | x ∈ M.comap f ∧ ∃ k : ℕ, orderOf x = p ^ k}) ∧
        (Subgroup.closure {x : G | x ∈ M.comap f ∧ ∃ k : ℕ, orderOf x = p ^ k}).map f = M) ∧
    ∀ L : Subgroup G, IsPComponent p L →
      ∃ e : L ⧸ pPrimeCore p L ≃* (L.map f) ⧸ pPrimeCore p (L.map f),
        ∀ x : L, e (x : L ⧸ pPrimeCore p L) =
          ((f.subgroupMap L x : L.map f) : (L.map f) ⧸ pPrimeCore p (L.map f)) := by
  have hp : p.Prime := Fact.out
  have hcop : p.Coprime (Nat.card f.ker) := hp.coprime_iff_not_dvd.2 hker
  have hres : ∀ V : Subgroup G, ¬ p ∣ Nat.card (f.domRestrict V).ker := fun V =>
    hp.coprime_iff_not_dvd.1 (coprime_card_restriction_kernel p f hcop V)
  have hgen : ∀ L : Subgroup G, primeResidual p L = ⊤ → primeResidual p (L.map f) = ⊤ := by
    intro L hL
    rw [← primeResidual_map_surjective p (f.subgroupMap L) (f.subgroupMap_surjective L), hL]
    exact Subgroup.map_top_of_surjective _ (f.subgroupMap_surjective L)
  have hfwd : ∀ L : Subgroup G, IsPComponent p L → IsPComponent p (L.map f) := by
    intro L hL
    obtain ⟨hLsub, hLgen, hLq⟩ := (pComponent_iff_subnormal_generated_quasisimple p L).1 hL
    obtain ⟨e, -⟩ := exists_restrict_core_quotient_equiv f L (hres L)
    exact (pComponent_iff_subnormal_generated_quasisimple p _).2
      ⟨hLsub.map hf, hgen L hLgen, isQuasisimple_of_mulEquiv e hLq⟩
  have hinv : ∀ M : Subgroup H, IsPComponent p M →
      IsPComponent p (Subgroup.closure {x : G | x ∈ M.comap f ∧ ∃ k : ℕ, orderOf x = p ^ k}) ∧
        (Subgroup.closure {x : G | x ∈ M.comap f ∧ ∃ k : ℕ, orderOf x = p ^ k}).map f = M := by
    intro M hM
    obtain ⟨hMsub, hMgen, hMq⟩ := (pComponent_iff_subnormal_generated_quasisimple p M).1 hM
    rw [closure_pElements_eq_map_primeResidual]
    let g : M.comap f →* M := (f.comp (M.comap f).subtype).codRestrict M fun x => x.2
    have hg : Function.Surjective g := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨⟨x, hy⟩, rfl⟩
    have hmap : ((primeResidual p (M.comap f)).map (M.comap f).subtype).map f = M := by
      have hcomp : f.comp (M.comap f).subtype = M.subtype.comp g := rfl
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, primeResidual_map_surjective p g hg,
        hMgen, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine ⟨?_, hmap⟩
    have hLsub : ((primeResidual p (M.comap f)).map (M.comap f).subtype).IsSubnormal := by
      have := primeResidual_characteristic p (M.comap f)
      have hn : (primeResidual p (M.comap f)).Normal := inferInstance
      exact hn.isSubnormal.trans' (hMsub.comap f)
    obtain ⟨e, -⟩ := exists_restrict_core_quotient_equiv f
      ((primeResidual p (M.comap f)).map (M.comap f).subtype) (hres _)
    have hq : IsQuasisimple ((((primeResidual p (M.comap f)).map (M.comap f).subtype).map f) ⧸
        pPrimeCore p (((primeResidual p (M.comap f)).map (M.comap f).subtype).map f)) :=
      (congrArg (fun X : Subgroup H => IsQuasisimple (X ⧸ pPrimeCore p X)) hmap).mpr hMq
    exact (pComponent_iff_subnormal_generated_quasisimple p _).2
      ⟨hLsub, primeResidual_map_subtype_primeResidual _, isQuasisimple_of_mulEquiv e.symm hq⟩
  refine ⟨⟨fun L hL => hfwd L hL, fun L₁ hL₁ L₂ hL₂ h => ?_, fun M hM => ?_⟩, hinv,
    fun L _ => exists_restrict_core_quotient_equiv f L (hres L)⟩
  · have hL₁sub := ((pComponent_iff_subnormal_generated_quasisimple p L₁).1 hL₁).1
    have hL₂sub := ((pComponent_iff_subnormal_generated_quasisimple p L₂).1 hL₂).1
    exact le_antisymm (le_of_coprime_kernel_map_le p f hf hcop L₁ L₂ hL₁ hL₂sub h.le)
      (le_of_coprime_kernel_map_le p f hf hcop L₂ L₁ hL₂ hL₁sub h.ge)
  · exact ⟨_, (hinv M hM).1, (hinv M hM).2⟩

end CFSG.ComponentClassification.CatalogueBPrimeJoin
