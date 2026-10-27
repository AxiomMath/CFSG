
module

public import CFSG.Quasithin.Background.C1GNC128
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.ConvICommute

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

namespace L246

variable {G : Type} [Group G] [Finite G]

variable {X T L : Subgroup G}

structure BlockCore (X T L : Subgroup G) : Prop where
  charTwo : CharTwo X
  sylow : IsSylowTwoOf T X
  block : IsBlock2 X L
  normJ : thompsonJ T ≤ Subgroup.normalizer (L : Set G)
  uV : blockU L ≤ VZ T X
  notC : ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T X : Set G)

namespace BlockCore

variable (D : BlockCore X T L)

include D

theorem red : IsTwoReducedIn X (VZ T X) := C1GN.isTwoReducedIn_VZ D.charTwo D.sylow

theorem elem : IsElemAbelian 2 (VZ T X) := D.red.2.2.1

theorem XN : X ≤ Subgroup.normalizer (VZ T X : Set G) := D.red.2.1

omit [Finite G] in
theorem LX : L ≤ X := D.block.2.1

omit [Finite G] in
theorem TX : T ≤ X := D.sylow.1

theorem LN : L ≤ Subgroup.normalizer (VZ T X : Set G) := D.LX.trans D.XN

theorem VT : VZ T X ≤ T :=
  (conjClosure_isTwoReducedIn_of_charTwo D.sylow D.charTwo (le_refl (quasithinOmegaOneCenter T))).1.trans
    (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf D.sylow))

theorem exists_offender : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
    ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T X : Set G) := by
  by_contra hcon
  push Not at hcon
  apply D.notC
  have hV := D.elem
  let Dsub : Subgroup ↥(Subgroup.normalizer (VZ T X : Set G)) :=
    (Subgroup.centralizer (autI hV L : Set (MulAut (IntMod (VZ T X) hV)))).comap (convI hV)
  have hJ : thompsonJ T ≤ Dsub.map (Subgroup.normalizer (VZ T X : Set G)).subtype := by
    refine iSup₂_le fun A hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (VZ T X : Set G) := D.XN (D.TX (hA.1 ha))
    refine ⟨⟨a, haN⟩, ?_, rfl⟩
    show convI hV ⟨a, haN⟩ ∈ Subgroup.centralizer (autI hV L : Set (MulAut (IntMod (VZ T X) hV)))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨l, hlL, rfl⟩ := (mem_autI hV).1 hh
    have hcomm : ⁅(l : G), a⁆ ∈ Subgroup.centralizer (VZ T X : Set G) :=
      hcon A hA (Subgroup.commutator_mem_commutator hlL ha)
    exact (ConvI.convI_comm_iff hV l.2 haN).2 hcomm
  rw [Subgroup.commutator_le]
  intro l hl j hj
  obtain ⟨⟨j', hj'N⟩, hjD, rfl⟩ := hJ hj
  have hlN : l ∈ Subgroup.normalizer (VZ T X : Set G) := D.LN hl
  have h1 : convI hV ⟨j', hj'N⟩ ∈
      Subgroup.centralizer (autI hV L : Set (MulAut (IntMod (VZ T X) hV))) := hjD
  have h2 := Subgroup.mem_centralizer_iff.1 h1 (convI hV ⟨l, hlN⟩) (convI_mem_autI hV hl hlN)
  exact (ConvI.convI_comm_iff hV hlN hj'N).1 h2

omit [Finite G] D in
theorem le_J {A : Subgroup G} (hA : IsMaxElemAbelian T A) : A ≤ thompsonJ T :=
  le_iSup₂_of_le A hA le_rfl

omit [Finite G] in
theorem A_le_normalizer {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    A ≤ Subgroup.normalizer (L : Set G) := (le_J hA).trans D.normJ

theorem not_le_centralizer {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAc : ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T X : Set G)) :
    ¬ A ≤ Subgroup.centralizer (VZ T X : Set G) := by
  intro hAC
  apply hAc
  have hV := D.elem
  rw [Subgroup.commutator_le]
  intro l hl a ha
  have haN : a ∈ Subgroup.normalizer (VZ T X : Set G) := D.XN (D.TX (hA.1 ha))
  have hlN : l ∈ Subgroup.normalizer (VZ T X : Set G) := D.LN hl
  have hc : convI hV ⟨a, haN⟩ = 1 := (convI_eq_one_iff hV _).2 (hAC ha)
  exact (ConvI.convI_comm_iff hV hlN haN).1 (by rw [hc]; simp)

theorem isFFStarOffender {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAc : ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T X : Set G)) :
    IsFFStarOffender (autI D.elem X) (autI D.elem A) := by
  have hFF : IsFFOffender T (VZ T X) A := ⟨hA, D.not_le_centralizer hA hAc⟩
  have h1 := offenderImages_isFFStarOffender D.elem D.VT (D.TX.trans D.XN) ⟨A, hFF, rfl⟩
  exact ⟨h1.1.trans (autI_mono D.elem D.TX), h1.2.1, h1.2.2.1, h1.2.2.2⟩

end BlockCore

end L246

end CFSG.QuasithinUnique
