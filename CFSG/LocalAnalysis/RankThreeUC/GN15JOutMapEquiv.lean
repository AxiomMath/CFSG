module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.GroupTheory.IsComponentOfMap

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

theorem jOutBody_map_mulEquiv {Q R : Type} [Group Q] [Group R] (φ : Q ≃* R) {J : Subgroup Q}
    (h : ∀ L : Subgroup Q, IsComponentOf L ⊤ → ⁅L, J⁆ ≠ ⊥ → ¬ IsMulCommutative (Outer ↥L) →
      ∀ w ∈ Subgroup.normalizer (L : Set Q), ∀ j ∈ J,
        ⁅w, j⁆ ∈ L ⊔ Subgroup.centralizer (L : Set Q)) :
    ∀ L : Subgroup R, IsComponentOf L ⊤ → ⁅L, J.map φ.toMonoidHom⁆ ≠ ⊥ →
      ¬ IsMulCommutative (Outer ↥L) → ∀ w ∈ Subgroup.normalizer (L : Set R),
        ∀ j ∈ J.map φ.toMonoidHom, ⁅w, j⁆ ∈ L ⊔ Subgroup.centralizer (L : Set R) := by
  intro L' hL' hne hnc w hw j hj
  set L : Subgroup Q := L'.map φ.symm.toMonoidHom with hL
  have hmem : ∀ x : Q, x ∈ L ↔ φ x ∈ L' := fun x => by
    rw [hL, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have hLmap : L.map φ.toMonoidHom = L' := by
    ext x
    rw [Subgroup.mem_map_equiv, hmem, MulEquiv.apply_symm_apply]
  have hLc : IsComponentOf L ⊤ := by
    have h1 := CFSG.isComponentOf_map_mulEquiv φ.symm hL'
    rwa [Subgroup.map_top_of_surjective φ.symm.toMonoidHom φ.symm.surjective] at h1
  have hLne : ⁅L, J⁆ ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← hLmap, ← Subgroup.map_commutator, hbot, Subgroup.map_bot]
  let eL : ↥L ≃* ↥L' :=
    (Subgroup.equivMapOfInjective L φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hLmap)
  have hLnc : ¬ IsMulCommutative (Outer ↥L) := by
    intro hc
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    let e := CFSG.ComponentClassification.OuterAutomorphisms.equivalence eL
    have h1 := hc.is_comm.comm (e.symm a) (e.symm b)
    have h2 := congrArg e h1
    simpa [map_mul] using h2
  have hw₀ : φ.symm w ∈ Subgroup.normalizer (L : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmem, hmem]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff.mp hw (φ x)
  have hj₀ : φ.symm j ∈ J := by
    rwa [Subgroup.mem_map_equiv] at hj
  have h0 := h L hLc hLne hLnc _ hw₀ _ hj₀
  have hle : L ⊔ Subgroup.centralizer (L : Set Q) ≤
      (L' ⊔ Subgroup.centralizer (L' : Set R)).comap φ.toMonoidHom := by
    refine sup_le (fun l hl => ?_) (fun c hc => ?_)
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_left ((hmem l).1 hl)
    · rw [Subgroup.mem_comap]
      refine Subgroup.mem_sup_right ?_
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : φ.symm x ∈ L := by rw [hmem, MulEquiv.apply_symm_apply]; exact hx
      have := Subgroup.mem_centralizer_iff.mp hc _ hx'
      have h3 := congrArg φ this
      simpa [map_mul] using h3
  have h1 := hle h0
  rw [Subgroup.mem_comap] at h1
  simpa [map_commutatorElement] using h1

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

end
