module

public import CFSG.CGT.PushingUpLit.CGT6.Props
public import CFSG.CGT.PushingUpLit.EightOneRel

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P53

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.EightOneRel
open scoped commutatorElement

section Transport

variable {L L' : Type} [Group L] [Group L']

theorem IsNaturalAltModuleWith.of_mulEquiv (e : L ≃* L') {n : ℕ}
    {φ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin (2 * n + 1))}
    (h : IsNaturalAltModuleWith L n φ) :
    IsNaturalAltModuleWith L' n ((quotPCoreEquiv e).symm.trans φ) := by
  obtain ⟨ψ, h1, h2, h3, h4⟩ := h
  refine ⟨ψ.comp (shortUEquiv e).symm.toMonoidHom, fun u => h1 _, ?_,
    ker_comp_shortUEquiv_symm e ψ h3, ?_⟩
  · intro v hv
    obtain ⟨u, hu⟩ := h2 v hv
    exact ⟨shortUEquiv e u, by simpa using hu⟩
  · exact transport_equivariance e φ ψ
      (fun g m => Multiplicative.ofAdd (permActionTwo (g : Equiv.Perm (Fin (2 * n + 1)))
        (Multiplicative.toAdd m))) h4

end Transport

section Arrow

variable {G G' : Type} [Group G] [Group G']

theorem arrowNat_map_of_injective (f : G →* G') (hf : Function.Injective f) {X L : Subgroup G}
    (h : ArrowNat X L) : ArrowNat (X.map f) (L.map f) := by
  rcases h with rfl | ⟨a, b, φ, F, ⟨ψ⟩, hnat, hF, hU, hXL, hstab⟩
  · exact Or.inl rfl
  · let eX : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
    let eL : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
    refine Or.inr ⟨a, b, (quotPCoreEquiv eL).symm.trans φ, F, ⟨(quotPCoreEquiv eX).symm.trans ψ⟩,
      IsNaturalAltModuleWith.of_mulEquiv eL hnat, hF, ?_, Subgroup.map_mono hXL, ?_⟩
    · rw [EightOneRel.map_shortU_map_subtype f hf, EightOneRel.map_shortU_map_subtype f hf]
      exact Subgroup.map_mono hU
    · have hsub : (X.subgroupOf L).map eL.toMonoidHom = (X.map f).subgroupOf (L.map f) := by
        ext z
        obtain ⟨y, rfl⟩ := eL.surjective z
        refine (Subgroup.mem_map_iff_mem (f := eL.toMonoidHom) eL.injective).trans ?_
        exact (Subgroup.mem_map_iff_mem hf (K := X) (x := (y : G))).symm
      have hq : ((X.subgroupOf L).map eL.toMonoidHom).map
          (QuotientGroup.mk' (pCore 2 ↥(L.map f))) =
          ((X.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))).map
            (quotPCoreEquiv eL).toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
      have hφ : ∀ T : Subgroup (↥L ⧸ pCore 2 ↥L),
          (T.map (quotPCoreEquiv eL).toMonoidHom).map
            ((quotPCoreEquiv eL).symm.trans φ).toMonoidHom = T.map φ.toMonoidHom := by
        intro T
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp
      rw [← hsub, hq, hφ]
      exact hstab

theorem arrowNat_map_subtype {K : Subgroup G} {X L : Subgroup ↥K} (h : ArrowNat X L) :
    ArrowNat (X.map K.subtype) (L.map K.subtype) :=
  arrowNat_map_of_injective K.subtype K.subtype_injective h

end Arrow

variable {G : Type} [Group G] [Finite G]

@[expose] def IsMaximalInClassXGNat (X : Subgroup G) : Prop :=
  InClassXG X ∧ ∀ Y : Subgroup G, InClassXG Y → ArrowNat X Y → Y = X

end CFSG.CGT.PushingUpLit.T2KR.P53
