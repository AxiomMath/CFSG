module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsGlue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenQuasi
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

@[expose] def GenNormalAllOn (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ) (T : Type) [Group T] [Finite T] (d : TauCeti.ValidLieTypeIndex), OddLie p T d →
    Q d.1 → ∀ x : MulAut T, x ^ p = 1 → x ≠ 1 → CompNormal x

namespace CompNormal

variable {S G : Type*} [Group S] [Group G]

theorem of_congr (e : S ≃* G) {β : MulAut S} (h : CompNormal (MulAut.congr e β)) :
    CompNormal β := by
  intro J hJ t ht
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e β
  have hJ' : IsComponentOf (J.map (e : S →* G)) (fixSubgroup (MulAut.congr e β)) := by
    rw [hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJ
  have ht' : e t ∈ fixSubgroup (MulAut.congr e β) := by
    rw [hfix]
    exact ⟨t, ht, rfl⟩
  have hN : e t ∈ (Subgroup.normalizer (J : Set S)).map e.toMonoidHom := by
    rw [Subgroup.map_equiv_normalizer_eq]
    exact h _ hJ' ht'
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hN
  exact hN

theorem of_conj (γ : MulAut S) {β : MulAut S} (h : CompNormal (γ * β * γ⁻¹)) : CompNormal β := by
  refine of_congr (γ : S ≃* S) ?_
  have hc : MulAut.congr (γ : S ≃* S) β = γ * β * γ⁻¹ := by
    ext x
    rfl
  rw [hc]
  exact h

end CompNormal

theorem compNormal_of_normal_quasisimple {S : Type*} [Group S] [Finite S] {β : MulAut S}
    {N : Subgroup S} (hNC : N ≤ fixSubgroup β) [(N.subgroupOf (fixSubgroup β)).Normal]
    (hNq : CFSG.IsQuasisimple ↥N)
    (hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ N.subgroupOf (fixSubgroup β))) :
    CompNormal β := by
  have hNc : IsComponentOf N (fixSubgroup β) :=
    ⟨hNC, CFSG.Open.IsSubnormal.step hNC inferInstance (CFSG.Open.IsSubnormal.refl _),
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hNq⟩
  have heq : ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) → K = N := fun K hK =>
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.eq_of_isComponentOf_of_perfect_le hNc
      (fun P hPC hP =>
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_of_solvable_quotient hNC
          hsol hPC hP) hK
  exact compNormal_of_unique β fun K K' hK hK' => (heq K hK).trans (heq K' hK').symm

theorem compNormal_of_isSimpleGroup {S : Type*} [Group S] [Finite S] {β : MulAut S}
    (hs : IsSimpleGroup ↥(fixSubgroup β)) (hnc : ∃ a b : ↥(fixSubgroup β), a * b ≠ b * a) :
    CompNormal β := by
  haveI : ((fixSubgroup β).subgroupOf (fixSubgroup β)).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  haveI : Subsingleton (↥(fixSubgroup β) ⧸ (fixSubgroup β).subgroupOf (fixSubgroup β)) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (a⁻¹ * b).2)
  exact compNormal_of_normal_quasisimple le_rfl
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnc)
    inferInstance

section Plane

theorem genPlaneCompOn_of_normalAll (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    {Q : TauCeti.LieTypeIndex → Prop} (h : GenNormalAllOn Q) : GenPlaneCompOn Q := by
  intro p T _ _ d hd hQ P hP hcard J
  obtain ⟨e⟩ := hd.iso
  haveI := (CFSG.Assembly.lie_finite_simple d).2
  exact not_forall_glaPComponent_of_compNormal hS (genCompQuasiOn_holds' Q) hd hQ
    e.isSimpleGroup hP hcard (fun x hx hx1 => h p T d hd hQ x (hP.2 x hx) hx1) J

end Plane

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
