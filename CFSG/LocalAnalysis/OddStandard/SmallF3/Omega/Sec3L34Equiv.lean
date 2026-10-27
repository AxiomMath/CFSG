module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem Sl23PocketIn.map_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {X : Subgroup G} {y : G} {K : Subgroup G} (h : Sl23PocketIn X y K) :
    Sl23PocketIn (X.map e.toMonoidHom) (e y) (K.map e.toMonoidHom) := by
  let A : Subgroup G := X ⊓ centralizer ({y} : Set G)
  have hKA : K ≤ A := h.2.1
  have hKsub : (K.subgroupOf A).IsSubnormal := h.2.2.1
  let ε : ↥A ≃* ↥(A.map e.toMonoidHom) :=
    A.equivMapOfInjective e.toMonoidHom e.injective
  have hA' : A.map e.toMonoidHom =
      X.map e.toMonoidHom ⊓ centralizer ({e y} : Set H) :=
    CFSG.centralizer_inter_map e X y
  have heq : (K.subgroupOf A).map ε.toMonoidHom =
      (K.map e.toMonoidHom).subgroupOf (A.map e.toMonoidHom) := by
    apply Subgroup.map_injective
      (Subgroup.subtype_injective (A.map e.toMonoidHom))
    rw [Subgroup.map_map]
    have hcomp : ((A.map e.toMonoidHom).subtype).comp ε.toMonoidHom =
        e.toMonoidHom.comp A.subtype := by
      ext m
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hKA,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_mono hKA)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem e.toMonoidHom h.1
  · rw [← hA']
    exact Subgroup.map_mono h.2.1
  · have hsn : ((K.subgroupOf A).map ε.toMonoidHom).IsSubnormal :=
      Subgroup.IsSubnormal.map (f := ε.toMonoidHom) ε.surjective hKsub
    rw [heq] at hsn
    rw [← hA']
    exact hsn
  · change IsSL23Mod ↥(K.map e.toMonoidHom)
    exact isSL23Mod_of_mulEquiv
      (K.equivMapOfInjective e.toMonoidHom e.injective) h.2.2.2

theorem isI4PlusIn_top_map_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) {y : G}
    (h : IsI4PlusIn (⊤ : Subgroup G) y) : IsI4PlusIn (⊤ : Subgroup H) (e y) := by
  obtain ⟨hord, K, hK⟩ := h
  refine ⟨?_, K.map e.toMonoidHom, ?_⟩
  · rw [MulEquiv.orderOf_eq e y, hord]
  · have hK' := Sl23PocketIn.map_mulEquiv e hK
    rwa [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hK'

theorem nonempty_omegaGroup_mulEquiv_omegaProj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate)
    (hπ : piOrth Q ∉ omegaGroup hQ) : Nonempty (omegaGroup hQ ≃* omegaProj hQ) := by
  have hinj : Function.Injective ((toProj Q).domRestrict (omegaGroup hQ)) := by
    intro a b hab
    have h1 : toProj Q (a : OGroup Q) = toProj Q (b : OGroup Q) := hab
    have h2 : toProj Q ((a : OGroup Q) * (b : OGroup Q)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 : (a : OGroup Q) * (b : OGroup Q)⁻¹ ∈ piGroup Q :=
      (QuotientGroup.eq_one_iff _).mp h2
    rcases mem_piGroup_iff.mp h3 with h4 | h4
    · apply Subtype.ext
      exact mul_inv_eq_one.mp h4
    · exfalso
      apply hπ
      have hmem : (a : OGroup Q) * (b : OGroup Q)⁻¹ ∈ omegaGroup hQ :=
        (omegaGroup hQ).mul_mem a.2 ((omegaGroup hQ).inv_mem b.2)
      rwa [h4] at hmem
  have hrange : ((toProj Q).domRestrict (omegaGroup hQ)).range = omegaProj hQ := by
    rw [MonoidHom.domRestrict_range, omegaProj]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

end CFSG.OddStandard.SmallF3.Omega
