module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.L64

open Subgroup CFSG CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Layer

variable {N : Type} [Group N]

theorem layer_comm_le (P : Subgroup N) : ⁅layer N, P⁆ ≤ layer N :=
  have : (layer N).Normal :=
    Subgroup.normal_of_characteristic _ (h := CFSG.LocalCores.layer_characteristic)
  Subgroup.commutator_le_left _ _

variable [Finite N]

theorem layer_le_comm_sup_centralizer (P : Subgroup N) :
    layer N ≤ ⁅layer N, P⁆ ⊔ (layer N ⊓ centralizer (P : Set N)) := by
  have hEn : (layer N).Normal :=
    Subgroup.normal_of_characteristic _ (h := CFSG.LocalCores.layer_characteristic)
  have hMsub : (⁅layer N, P⁆).IsSubnormal :=
    Subgroup.IsSubnormal.step _ (layer N) (layer_comm_le P) hEn.isSubnormal
      (Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left _ _))
  refine sSup_le fun J hJ => ?_
  rcases CFSG.LocalCores.component_subnormal_subgroup hJ hMsub with h | h
  · exact h.trans le_sup_left
  · refine le_sup_of_le_right (le_inf (CFSG.LocalCores.component_le_layer hJ) ?_)
    have hJP : ⁅J, P⁆ ≤ ⁅layer N, P⁆ :=
      Subgroup.commutator_mono (CFSG.LocalCores.component_le_layer hJ) le_rfl
    have h1 : ⁅⁅J, P⁆, J⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      calc ⁅⁅J, P⁆, J⁆ ≤ ⁅⁅layer N, P⁆, J⁆ := Subgroup.commutator_mono hJP le_rfl
        _ = ⁅J, ⁅layer N, P⁆⁆ := Subgroup.commutator_comm _ _
        _ = ⊥ := h
        _ ≤ ⊥ := le_rfl
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.perfect_double_commutator hJ.1.1 h1)

end Layer

section Ambient

variable {G : Type} [Group G]

variable [Finite G]

theorem Em_le_comm_sup_centralizer {N P : Subgroup G} (hP : P ≤ N) :
    Em N ≤ ⁅Em N, P⁆ ⊔ (Em N ⊓ centralizer (P : Set G)) := by
  have hPN : (P.subgroupOf N).map N.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP]
  have hC : (centralizer ((P.subgroupOf N : Subgroup N) : Set N)).map N.subtype ≤
      centralizer (P : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpP : (⟨p, hP hp⟩ : N) ∈ P.subgroupOf N := hp
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx _ hpP)
  have h := Subgroup.map_mono (f := N.subtype) (layer_le_comm_sup_centralizer (P.subgroupOf N))
  rw [Subgroup.map_sup, Subgroup.map_commutator, hPN] at h
  refine h.trans (sup_le_sup_left ?_ _)
  exact (Subgroup.map_inf_le _ _ _).trans (inf_le_inf_left _ hC)

end Ambient

end CFSG.GH74.GLS.Stage2.Bender.Thm1.L64
