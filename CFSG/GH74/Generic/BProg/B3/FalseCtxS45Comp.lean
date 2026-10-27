module

public import CFSG.GH74.Generic.BProg.B3.ObsPump

public section

namespace CFSG.GH74.Generic.BProg.B3.FalseCtxS45Comp

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification Subgroup

section Conj

variable {G : Type} [Group G]

theorem map_conj_self {X : Subgroup G} {g : G} (hg : g ∈ X) :
    X.map (MulAut.conj g).toMonoidHom = X := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact X.mul_mem (X.mul_mem hg hw) (X.inv_mem hg)
  · intro hz
    refine ⟨g⁻¹ * z * g, X.mul_mem (X.mul_mem (X.inv_mem hg) hz) hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

variable [Finite G]

theorem isPCompIn_conj {X K : Subgroup G} (h : IsPCompIn 2 X K) {g : G} (hg : g ∈ X) :
    IsPCompIn 2 X (K.map (MulAut.conj g).toMonoidHom) := by
  have := Stage1.Thm2.Recip.isPCompIn_map_conj h g
  rwa [map_conj_self hg] at this

end Conj

section Commute

variable {G : Type} [Group G] [Finite G] {a : G} {J J' : Subgroup G}

theorem false_of_commutator_self_eq_bot {Q : Type} [Group Q] {C : Subgroup Q}
    (hc : CFSG.IsComponent C) (h : ⁅C, C⁆ = ⊥) : False := by
  have h1 : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp hc.1.1
  have h2 : C = ⊥ := h1.symm.trans h
  have : Nontrivial ↥C := CFSG.LocalCores.isQuasisimple_nontrivial hc.1
  exact (Subgroup.nontrivial_iff_ne_bot C).mp this h2

theorem isComponent_bar (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J) :
    CFSG.IsComponent (PumpCalc.bar a J) :=
  PumpCalc.isComponent_bar hJ

theorem pCompIn_eq_or_commute (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J)
    (hJ' : IsPCompIn 2 (centralizer ({a} : Set G)) J') :
    J = J' ∨ ⁅PumpCalc.bar a J, PumpCalc.bar a J'⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CFSG.IsComponent (PumpCalc.bar a J) := isComponent_bar hJ
  have hc' : CFSG.IsComponent (PumpCalc.bar a J') := isComponent_bar hJ'
  rcases CFSG.LocalCores.component_subnormal_subgroup hc hc'.2 with h1 | h1
  · left
    rcases CFSG.LocalCores.component_subnormal_subgroup hc' hc.2 with h2 | h2
    · have heq : PumpCalc.bar a J = PumpCalc.bar a J' := le_antisymm h1 h2
      have h3 := UnbalancedLayer.pComponent_eq_of_map_eq hJ.2 hJ'.2 heq
      have h4 := (Subgroup.subgroupOf_inj).1 h3
      rwa [inf_of_le_left hJ.1, inf_of_le_left hJ'.1] at h4
    · exfalso
      exact false_of_commutator_self_eq_bot hc
        (le_bot_iff.mp (h2 ▸ Subgroup.commutator_mono h1 le_rfl))
  · right
    exact h1

theorem eq_of_le (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J)
    (hJ' : IsPCompIn 2 (centralizer ({a} : Set G)) J') (h : J ≤ J') : J = J' := by
  rcases pCompIn_eq_or_commute hJ hJ' with h1 | h1
  · exact h1
  · exfalso
    have hle : PumpCalc.bar a J ≤ PumpCalc.bar a J' := Subgroup.map_mono (fun x hx => h hx)
    exact false_of_commutator_self_eq_bot (isComponent_bar hJ)
      (le_bot_iff.mp (h1 ▸ Subgroup.commutator_mono le_rfl hle))

theorem le_cSec_of_ne (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J)
    (hJ' : IsPCompIn 2 (centralizer ({a} : Set G)) J') (hne : J ≠ J') :
    J' ≤ centralizerSection J (pPrimeCoreOf 2 J) := by
  intro q hq
  have hqY : q ∈ centralizer ({a} : Set G) := hJ'.1 hq
  refine ObsPump.mem_cSec_of_bar_comm hJ hqY fun l hl => ?_
  have hcomm := (pCompIn_eq_or_commute hJ hJ').resolve_left hne
  have hqb : barMk ↥(centralizer ({a} : Set G)) ⟨q, hqY⟩ ∈ PumpCalc.bar a J' :=
    ⟨⟨q, hqY⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  have hl' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hl
  exact Subgroup.mem_centralizer_iff.mp hl' _ hqb

theorem eq_of_not_le_cSec (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J)
    {K : Subgroup G} (hK : IsPCompIn 2 (centralizer ({a} : Set G)) K)
    (h : ¬ K ≤ centralizerSection J (pPrimeCoreOf 2 J)) : J = K := by
  by_contra hne
  exact h (le_cSec_of_ne hJ hK hne)

end Commute

end CFSG.GH74.Generic.BProg.B3.FalseCtxS45Comp
