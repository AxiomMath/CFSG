module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs

import CFSG.GH74.GLS.Bg.Pu5.BalBBasic
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
import CFSG.GH74.GLS.Bg.Pu5.Statements

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS.Stage1.Thm4
open CFSG.GH74.GLS.Bg.Pu5 CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

theorem zStar_le_zStar_kz_of_mem_rigidSet
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x : G} {K : Subgroup G}
    (hK : K ∈ RigidSet fullQ x) :
    zStar K ≤ zStar (Kz fullQ x) := by
  let C : Subgroup G := centralizer ({x} : Set G)
  let P : Subgroup G := Kz fullQ x
  have hPC : P ≤ C := by
    change sSup (RigidSet fullQ x) ≤ centralizer ({x} : Set G)
    exact sSup_le fun L hL => hL.1.1.2.2.1
  have hKP : K ≤ P := by
    change K ≤ sSup (RigidSet fullQ x)
    exact le_sSup hK
  intro a ha
  change a ∈ K ∧ a ∈ centralizerSection K (pPrimeCoreOf 2 K) at ha
  have haP : a ∈ P := hKP ha.1
  have hKcomp : IsPCompIn 2 C K := by
    change IsPCompIn 2 (centralizer ({x} : Set G)) K
    exact hK.1.1.2.2
  have hN : ∀ g ∈ C, g ∈ normalizer (pPrimeCoreOf 2 C : Set G) := by
    intro g hg
    exact mem_normalizer_pPrimeCoreOf (le_normalizer hg)
  have hS : ∀ L ∈ RigidSet fullQ x, L ≤ C := by
    intro L hL
    change L ≤ centralizer ({x} : Set G)
    exact hL.1.1.2.2.1
  have hgen : ∀ L ∈ RigidSet fullQ x, ∀ l ∈ L, ⁅l, a⁆ ∈ pPrimeCoreOf 2 C := by
    intro L hL l hl
    by_cases hLK : L = K
    · subst L
      exact pPrimeCoreOf_le_of_isPCompIn hKcomp (ha.2.2.2 l hl)
    · have hLcomp : IsPCompIn 2 C L := by
        change IsPCompIn 2 (centralizer ({x} : Set G)) L
        exact hL.1.1.2.2
      have hKL : K ≤ cSec L :=
        le_cSec_of_ne hKcomp hLcomp (Ne.symm hLK)
      have haSec : a ∈ cSec L := hKL ha.1
      have hcommL : ⁅l, a⁆ ∈ pPrimeCoreOf 2 L := by
        change a ∈ centralizerSection L (pPrimeCoreOf 2 L) at haSec
        exact haSec.2.2 l hl
      exact pPrimeCoreOf_le_of_isPCompIn hLcomp hcommL
  have hcommC : ∀ p ∈ P, ⁅p, a⁆ ∈ pPrimeCoreOf 2 C := by
    change ∀ p ∈ sSup (RigidSet fullQ x), ⁅p, a⁆ ∈ pPrimeCoreOf 2 C
    exact commutator_mem_of_le_sSup hN hS hgen
  have hcommP : ∀ p ∈ P, ⁅p, a⁆ ∈ P := by
    intro p hp
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hp haP) (P.inv_mem hp)) (P.inv_mem haP)
  have hcommOP : ∀ p ∈ P, ⁅p, a⁆ ∈ pPrimeCoreOf 2 P := by
    intro p hp
    exact inf_pPrimeCoreOf_le hPC ⟨hcommP p hp, hcommC p hp⟩
  have hz : a ∈ zStar P := by
    change a ∈ P ∧ a ∈ centralizerSection P (pPrimeCoreOf 2 P)
    exact ⟨haP, le_normalizer haP,
      mem_normalizer_pPrimeCoreOf (le_normalizer haP), hcommOP⟩
  change a ∈ zStar P
  exact hz

end CFSG.GH74.GLS.NT44

end
