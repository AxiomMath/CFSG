module

public import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport
public import CFSG.HardMathSupport.Cooperstein.Proving.PCoreSup
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.Open CFSG.AGLEmbedding

theorem isQuasisimple_of_mulEquiv' {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hc, hs⟩ := hA
  have hcomm : commutator B = ⊤ := by
    rw [_root_.commutator_def, ← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective,
      ← Subgroup.map_commutator, ← _root_.commutator_def, hc]
  have hcen : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B :=
    Subgroup.map_center_eq e
  let e' := QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e hcen
  exact ⟨hcomm, e'.symm.isSimpleGroup⟩

variable {G : Type} [Group G] {X L S : Subgroup G}

theorem isTwoPrimeComponent_sup (hL : IsTwoPrimeComponent X L) (hSX : S ≤ X) (hS : IsPGroup 2 S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) : IsTwoPrimeComponent (L ⊔ S) L := by
  have hTnorm : L ⊔ S ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hSL
  have hLn : (L.subgroupOf (L ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hTnorm
  have hpc : (CFSG.pCore 2 ↥(L ⊔ S)).Normal := CFSG.pCore_normal
  have hbarN : (barM (L ⊔ S) L).Normal :=
    hLn.map (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ S))) (QuotientGroup.mk'_surjective _)
  have hsub : CFSG.Open.IsSubnormal L (L ⊔ S) :=
    CFSG.Open.IsSubnormal.step le_sup_left hLn (CFSG.Open.IsSubnormal.refl _)
  have hbarTop : CFSG.Open.IsSubnormal (barM (L ⊔ S) L) ⊤ :=
    CFSG.Open.IsSubnormal.step le_top
      (by haveI := hbarN; exact inferInstance) (CFSG.Open.IsSubnormal.refl _)
  have hLY : L ≤ L ⊔ S := le_sup_left
  have hh : L ⊓ CFSG.Open.pCoreOf 2 X = L ⊓ CFSG.Open.pCoreOf 2 (L ⊔ S) :=
    hL.inf_twoCore.trans (inf_pCoreOf_sup hL hSX hS hSL).symm
  have hqs : CFSG.Open.IsQuasisimple ↥(barM (L ⊔ S) L) :=
    isQuasisimple_of_mulEquiv' (barMEquiv hL.le hLY hh) hL.component.2.2
  exact
    { le := le_sup_left
      subnormal := hsub
      perfect := hL.perfect
      component := ⟨le_top, hbarTop, hqs⟩ }

end CFSG.HardMathSupport.Cooperstein.Proving

end
