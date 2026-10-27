module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

private theorem gla_i1913_primeCoreOf_map {G G' : Type*} [Group G] [Group G'] (p : ℕ)
    (f : G →* G') (hf : Function.Injective f) (X : Subgroup G) :
    GLAPPrimeCoreOf p (X.map f) = (GLAPPrimeCoreOf p X).map f := by
  have h1 : GLAPPrimeCore p ↥(X.map f) =
      (GLAPPrimeCore p ↥X).map (Subgroup.equivMapOfInjective X f hf).toMonoidHom :=
    (CFSG.pPrimeCore_map_iso p (Subgroup.equivMapOfInjective X f hf)).symm
  have h2 : (X.map f).subtype.comp (Subgroup.equivMapOfInjective X f hf).toMonoidHom =
      f.comp X.subtype := by
    ext x
    rfl
  unfold GLAPPrimeCoreOf
  rw [h1, Subgroup.map_map, h2, Subgroup.map_map]

theorem i1913At_of (h : KD1913) : I1913At := by
  intro K _ _ hK hcat H hH x hxH hx
  haveI : Group.IsPerfect K := Group.isPerfect_def.2 hK.1
  have hinj : Function.Injective
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  have hinner : innerAut (K ⧸ Subgroup.center K) ≤
      H.map (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K) := by
    intro g hg
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hg
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) s
    have hk : MulAut.conj k ∈ innerAut K := MonoidHom.mem_range.2 ⟨k, rfl⟩
    exact Subgroup.mem_map.2 ⟨MulAut.conj k, hH hk,
      CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_conj k⟩
  have hxφ : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K x ∈
      H.map (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K) :=
    Subgroup.mem_map_of_mem _ hxH
  have hord : orderOf
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K x) = 3 :=
    (orderOf_injective _ hinj x).trans hx
  have hY : H.map (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K) ⊓
      Subgroup.centralizer
        ({CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K x} :
          Set (MulAut (K ⧸ Subgroup.center K))) =
      (H ⊓ Subgroup.centralizer ({x} : Set (MulAut K))).map
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K) := by
    ext y
    constructor
    · rintro ⟨hyH, hyC⟩
      obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.1 hyH
      refine Subgroup.mem_map.2 ⟨h', Subgroup.mem_inf.2
        ⟨hh', Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
      apply hinj
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 hyC
    · rintro ⟨h', hmem, rfl⟩
      obtain ⟨hh', hC⟩ := Subgroup.mem_inf.1 hmem
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _ hh',
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have hC' := Subgroup.mem_centralizer_singleton_iff.1 hC
      rw [← map_mul, ← map_mul, hC']
  have key := h (K ⧸ Subgroup.center K) hcat _ hinner _ hxφ hord
  rw [hY, gla_i1913_primeCoreOf_map 3 _ hinj, Subgroup.card_map_of_injective hinj] at key
  exact key

end CFSG.LocalAnalysis.GLTheoremA
