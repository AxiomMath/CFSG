module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrComp
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A B : Type} [Group A] [Group B] {f : A →* B}

theorem isSubnormal_coverDerived (K : Subgroup B) (hK : K.IsSubnormal) :
    (coverDerived f K).IsSubnormal := by
  have h1 : (K.comap f).IsSubnormal := hK.comap f
  have hle : coverDerived f K ≤ K.comap f := coverDerived_le K
  have hnorm : ((coverDerived f K).subgroupOf (K.comap f)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h k hh hk
    exact conj_mem_coverDerived K hk hh
  exact Subgroup.IsSubnormal.trans hle hnorm.isSubnormal h1

namespace OddCentralCover

variable (h : OddCentralCover f)
include h

theorem isComponent_coverDerived {K : Subgroup B} (hK : CFSG.IsComponent K) :
    CFSG.IsComponent (coverDerived f K) :=
  ⟨h.isQuasisimple_coverDerived hK.1, isSubnormal_coverDerived K hK.2⟩

theorem layer_le_map_layer : CFSG.layer B ≤ (CFSG.layer A).map f := by
  rw [CFSG.layer.eq_sSup]
  refine sSup_le fun K hK => ?_
  intro b hb
  obtain ⟨a, ha, hab⟩ := h.exists_mem_coverDerived hK.1 hb
  exact ⟨a, CFSG.LocalCores.component_le_layer (h.isComponent_coverDerived hK) ha, hab⟩

theorem exists_involution_layer_lift {u : B} (hu : u ∈ CFSG.layer B) (huu : u * u = 1) :
    ∃ a : A, a ∈ CFSG.layer A ∧ a * a = 1 ∧ f a = u := by
  obtain ⟨a₀, ha₀, hfa₀⟩ := h.layer_le_map_layer hu
  have hpow := h.pow_card_ker (a := a₀) (by rw [hfa₀]; exact huu)
  exact ⟨a₀ ^ Nat.card f.ker, Subgroup.pow_mem _ ha₀ _, hpow.1, by rw [hpow.2, hfa₀]⟩

end OddCentralCover

end CFSG.OddStandard.SmallF3.Omega
