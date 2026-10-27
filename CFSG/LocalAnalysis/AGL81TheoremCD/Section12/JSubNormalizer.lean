module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G]

theorem map_conj_mem_weakBlockSet {M H L : Subgroup G} {g : G} (hg : g ∈ H ⊓ M)
    (hL : L ∈ weakBlockSet M H) : L.map (MulAut.conj g).toMonoidHom ∈ weakBlockSet M H :=
  IsWeakSBlock.map_conj hL hg.2
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H hg.1)

theorem inf_le_normalizer_jSub (M H : Subgroup G) :
    H ⊓ M ≤ Subgroup.normalizer (jSub M H : Set G) := fun _ hg =>
  CFSG.Walter.mem_normalizer_sSup_of_map_mem (fun _ hL => map_conj_mem_weakBlockSet hg hL)
    fun _ hL => map_conj_mem_weakBlockSet (inv_mem hg) hL

@[expose] def twoPrimeLayer (M : Subgroup G) : Subgroup G :=
  sSup {L | IsTwoPrimeComponent M L}

theorem twoPrimeLayer_le (M : Subgroup G) : twoPrimeLayer M ≤ M :=
  sSup_le fun _ hL => hL.le

theorem le_normalizer_twoPrimeLayer (M : Subgroup G) :
    M ≤ Subgroup.normalizer (twoPrimeLayer M : Set G) := fun _ hg =>
  CFSG.Walter.mem_normalizer_sSup_of_map_mem (fun _ hL => IsTwoPrimeComponent.map_conj hg hL)
    fun _ hL => IsTwoPrimeComponent.map_conj (inv_mem hg) hL

theorem jSub_le_twoPrimeLayer (M H : Subgroup G) : jSub M H ≤ twoPrimeLayer M :=
  sSup_le_sSup fun _ hL => hL.toIsTwoPrimeComponent

theorem twoPrimeLayer_le_normalizer_jSub [Finite G] (M H : Subgroup G) :
    twoPrimeLayer M ≤ Subgroup.normalizer (jSub M H : Set G) := by
  refine sSup_le fun L' hL' x hx => ?_
  have hN : ∀ L ∈ weakBlockSet M H, x ∈ Subgroup.normalizer (L : Set G) := by
    intro L hL
    have hL2 : IsTwoPrimeComponent M L := hL.toIsTwoPrimeComponent
    by_cases h : L' = L
    · subst h
      exact Subgroup.le_normalizer hx
    · have hcen : barM M L' ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL'.component
            hL2.component fun he => h (hL'.eq_of_barM_eq hL2 he))
      exact hL2.le_normalizer (S := L')
        (fun _ hy => Subgroup.centralizer_le_normalizer _ (hcen hy)) hL'.le hx
  have hmap : ∀ y : G, (∀ L ∈ weakBlockSet M H, y ∈ Subgroup.normalizer (L : Set G)) →
      ∀ L ∈ weakBlockSet M H, L.map (MulAut.conj y).toMonoidHom ∈ weakBlockSet M H := by
    intro y hy L hL
    have h : L.map (MulAut.conj y).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hy L hL)
    rw [h]
    exact hL
  exact CFSG.Walter.mem_normalizer_sSup_of_map_mem (hmap x hN)
    (hmap x⁻¹ fun L hL => inv_mem (hN L hL))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
