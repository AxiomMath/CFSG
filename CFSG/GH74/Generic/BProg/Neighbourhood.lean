module

public import CFSG.GH74.Generic.BProg.Frozen
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

structure NbhdData (G : Type) [Group G] (x c : G) (L : Subgroup G) : Prop where
  noAlt : NoAltJ2 G
  ex : ∃ (Iw A : Subgroup G) (y : G) (Lb : Subgroup (CentralizerBar x)),
    IsJ2Circ x Iw ∧ IsSource2 x Iw A ∧ IsAdmPair x Iw A y Lb ∧ c ∈ closure ({x, y} : Set G) ∧ c ≠ 1 ∧
      L ≤ centralizer ({c} : Set G) ∧
      L ≤ ⨆ g ∈ L, (liftAt x y Lb).map (MulAut.conj g).toMonoidHom

theorem comm_of_nbhdData (hA : Stage2Allow) {G : Type} [Group G] [Finite G] (hHyp : Hyp2 G)
    {x c : G} {L : Subgroup G} (h : NbhdData G x c L) :
    ∀ a ∈ L, ∀ w ∈ pPrimeCoreOf 2 (centralizer ({c} : Set G)), a * w = w * a := by
  obtain ⟨Iw, A, y, Lb, hcirc, hsrc, hadm, hc, hc1, hLC, hgen⟩ := h.ex
  have hss : NbhdSemisimple x y Lb := hA G hHyp h.noAlt x Iw hcirc A hsrc y Lb hadm
  have hcomm := hss c hc hc1
  have hle : L ≤ centralizer ((pPrimeCoreOf 2 (centralizer ({c} : Set G)) : Subgroup G) : Set G) := by
    refine hgen.trans (iSup₂_le fun g hg => ?_)
    rintro _ ⟨l, hl, rfl⟩ w hw
    have hgc : g ∈ centralizer ({c} : Set G) := hLC hg
    have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ pPrimeCoreOf 2 (centralizer ({c} : Set G)) :=
      CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore
        (Subgroup.inv_mem _ hgc) hw
    have h1 : ⁅l, g⁻¹ * w * g⁻¹⁻¹⁆ ∈
        ⁅liftAt x y Lb, pPrimeCoreOf 2 (centralizer ({c} : Set G))⁆ :=
      Subgroup.commutator_mem_commutator hl hw'
    rw [hcomm, Subgroup.mem_bot] at h1
    have h2 : l * (g⁻¹ * w * g⁻¹⁻¹) = (g⁻¹ * w * g⁻¹⁻¹) * l :=
      commutatorElement_eq_one_iff_mul_comm.1 h1
    show w * (g * l * g⁻¹) = (g * l * g⁻¹) * w
    calc w * (g * l * g⁻¹) = g * ((g⁻¹ * w * g⁻¹⁻¹) * l) * g⁻¹ := by group
      _ = g * (l * (g⁻¹ * w * g⁻¹⁻¹)) * g⁻¹ := by rw [h2]
      _ = (g * l * g⁻¹) * w := by group
  intro a ha w hw
  exact (Subgroup.mem_centralizer_iff.1 (hle ha) w hw).symm

end CFSG.GH74.Generic.BProg
