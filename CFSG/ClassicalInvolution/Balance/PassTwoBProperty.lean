module

public import CFSG.ClassicalInvolution.LocalComponent.Layer
public import CFSG.ClassicalInvolution.SmallCases.SingleComponent
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
open scoped commutatorElement

section Transport

variable {X : Type*} [Group X]

theorem subgroupOf_map_subtype_self (W : Subgroup X) (M : Subgroup ↥W) :
    (M.map W.subtype).subgroupOf W = M :=
  Subgroup.comap_map_eq_self_of_injective W.subtype_injective M

theorem isTwoComponent_data_map [Finite X] {W : Subgroup X} {M : Subgroup ↥W}
    (hM : TwoComponents.IsTwoComponent M) :
    IsSubnormal (M.map W.subtype) W ∧ commutator ↥(M.map W.subtype) = ⊤ ∧
      CFSG.Open.IsQuasisimple (↥(M.map W.subtype) ⧸
        componentClassificationOddCore ↥(M.map W.subtype)) := by
  let e : M ≃* ↥(M.map W.subtype) := M.equivMapOfInjective W.subtype W.subtype_injective
  refine ⟨?_, ?_, ?_⟩
  · refine (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff
      (Subgroup.map_subtype_le M)).mp ?_
    rw [subgroupOf_map_subtype_self]
    exact hM.1
  · have hperf : Group.IsPerfect ↥M := ⟨TwoComponents.perfect hM⟩
    have : Group.IsPerfect ↥(M.map W.subtype) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Group.IsPerfect.commutator_eq_top
  · exact Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore ↥(M.map W.subtype))
        (componentClassificationOddCore ↥M) e.symm (OddCore.equiv_invariant e.symm))
      (TwoComponents.quasisimple_quotient hM)

end Transport

section Level

variable {X : Type} [Group X] [Finite X]

theorem isQuasisimple_of_map_le_component {Q : Subgroup X} {t : X}
    (hQB : ∀ M₁ : Subgroup ↥(Q ⊓ Subgroup.centralizer ({t} : Set X)),
      TwoComponents.IsTwoComponent M₁ → CFSG.Open.IsQuasisimple M₁)
    {W : Subgroup X} (hW : W = Subgroup.centralizer ({t} : Set X)) {M : Subgroup ↥W}
    (hM : TwoComponents.IsTwoComponent M) (hMQ : M.map W.subtype ≤ Q) :
    CFSG.Open.IsQuasisimple M := by
  obtain ⟨hsub, hperf, hq⟩ := isTwoComponent_data_map hM
  have hMC : M.map W.subtype ≤ Q ⊓ Subgroup.centralizer ({t} : Set X) := fun x hx =>
    ⟨hMQ hx, by
      have hxW : x ∈ W := Subgroup.map_subtype_le M hx
      rwa [hW] at hxW⟩
  have hsubC : IsSubnormal (M.map W.subtype) (Q ⊓ Subgroup.centralizer ({t} : Set X)) := by
    have h := isSubnormal_inf hsub (Q ⊓ Subgroup.centralizer ({t} : Set X))
    rwa [inf_eq_left.mpr hMC, inf_eq_right.mpr (inf_le_right.trans hW.ge)] at h
  have h2 := hQB _ (isTwoComponent_subgroupOf_of_perfect_of_le hMC hsubC hperf hq)
  let e : M ≃* ↥(M.map W.subtype) := M.equivMapOfInjective W.subtype W.subtype_injective
  exact Components.quasisimple_of_equiv
    (e.trans (Subgroup.subgroupOfEquivOfLe hMC).symm) h2

end Level

section Main

variable {X : Type} [Group X] [Finite X]

theorem isQuasisimple_or_commutator_eq_bot_of_mem_component (hLB : L2PrimeBalance)
    (hO : componentClassificationOddCore X = ⊥) {Q : Subgroup X} (hQ : IsComponentOf Q ⊤) {t : X}
    (htQ : t ∈ Q) (ht2 : t * t = 1)
    (hQB : ∀ M₁ : Subgroup ↥(Q ⊓ Subgroup.centralizer ({t} : Set X)),
      TwoComponents.IsTwoComponent M₁ → CFSG.Open.IsQuasisimple M₁)
    {L : Subgroup X} (hLQ : L ≤ Q) {W : Subgroup X}
    (hW : W = Subgroup.centralizer ({t} : Set X)) (M : Subgroup ↥W)
    (hM : TwoComponents.IsTwoComponent M) :
    CFSG.Open.IsQuasisimple M ∨ ⁅M.map W.subtype, L⁆ = ⊥ := by
  have hlayer : M.map W.subtype ≤ Layer.subgroup X :=
    twoComponent_le_layer_of_l2PrimeBalance hLB hO ht2 hW hM
  have htlayer : t ∈ Layer.subgroup X := Layer.component_le hQ htQ
  obtain ⟨L', hL', hML'⟩ := exists_isComponentOf_ge_of_isTwoComponent htlayer hW hM hlayer
  by_cases hLQ' : L' = Q
  · subst hLQ'
    exact Or.inl (isQuasisimple_of_map_le_component hQB hW hM hML')
  · right
    have hcomm := LocalComponents.commute_of_ne L' Q hL' hQ hLQ'
    exact le_bot_iff.mp ((Subgroup.commutator_mono hML' hLQ).trans hcomm.le)

end Main

end CFSG.ClassicalInvolution.Balance
