module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplCoord
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplDef

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

namespace S8Data

variable {P : Type} [Group P] {V1 V2 : Subgroup P} {φ1 φ2 : (Fin 5 → ZMod 2) → P}
  {α β : P →* S8A5}

theorem swap (h : S8Data V1 V2 φ1 φ2 α β) : S8Data V2 V1 φ2 φ1 β α where
  coord1 := h.coord2
  coord2 := h.coord1
  comm := fun x hx y hy => (h.comm y hy x hx).symm
  disj := by rw [inf_comm]; exact h.disj
  act1 := h.act2
  act2 := h.act1
  ker := fun g hb ha => by rw [sup_comm]; exact h.ker g ha hb
  surj := fun a b => by
    obtain ⟨g, hg1, hg2⟩ := h.surj b a
    exact ⟨g, hg2, hg1⟩

theorem normal1 (h : S8Data V1 V2 φ1 φ2 α β) : V1.Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨v, hv, rfl⟩ := h.coord1.surj x hx
  rw [h.act1 g v hv]
  exact h.coord1.mem _ (s8_isEvenVec_permVec _ hv)

theorem normal2 (h : S8Data V1 V2 φ1 φ2 α β) : V2.Normal :=
  h.swap.normal1

theorem alpha_V1 (h : S8Data V1 V2 φ1 φ2 α β) {x : P} (hx : x ∈ V1) : α x = 1 := by
  apply s8_fin_faithful
  intro v hv
  have h2 : x * φ1 v * x⁻¹ = φ1 v := by
    rw [h.coord1.comm_mem hx (h.coord1.mem v hv)]; group
  apply h.coord1.eq_of_eq' (s8_isEvenVec_permVec _ hv) hv
  rw [← h.act1 x v hv, h2]

theorem beta_V1 (h : S8Data V1 V2 φ1 φ2 α β) {x : P} (hx : x ∈ V1) : β x = 1 := by
  apply s8_fin_faithful
  intro v hv
  have h2 : x * φ2 v * x⁻¹ = φ2 v := by
    rw [h.comm x hx _ (h.coord2.mem v hv)]; group
  apply h.coord2.eq_of_eq' (s8_isEvenVec_permVec _ hv) hv
  rw [← h.act2 x v hv, h2]

theorem alpha_V2 (h : S8Data V1 V2 φ1 φ2 α β) {x : P} (hx : x ∈ V2) : α x = 1 :=
  h.swap.beta_V1 hx

theorem beta_V2 (h : S8Data V1 V2 φ1 φ2 α β) {x : P} (hx : x ∈ V2) : β x = 1 :=
  h.swap.alpha_V1 hx

theorem cent_V2 (h : S8Data V1 V2 φ1 φ2 α β) : centralizer (V2 : Set P) = β.ker := by
  ext g
  rw [mem_centralizer_iff, MonoidHom.mem_ker]
  constructor
  · intro hg
    apply s8_fin_faithful
    intro v hv
    have h2 : g * φ2 v * g⁻¹ = φ2 v := by
      rw [← hg (φ2 v) (h.coord2.mem v hv)]; group
    apply h.coord2.eq_of_eq' (s8_isEvenVec_permVec _ hv) hv
    rw [← h.act2 g v hv, h2]
  · intro hg y hy
    obtain ⟨v, hv, rfl⟩ := h.coord2.surj y hy
    have h2 := h.act2 g v hv
    rw [hg, show ((1 : S8A5) : Equiv.Perm (Fin 5)) = 1 from rfl, s8_permVec_one] at h2
    rw [← mul_inv_eq_iff_eq_mul.mpr h2.symm]
    group

theorem cent_V1 (h : S8Data V1 V2 φ1 φ2 α β) : centralizer (V1 : Set P) = α.ker :=
  h.swap.cent_V2

theorem ker_inf (h : S8Data V1 V2 φ1 φ2 α β) : α.ker ⊓ β.ker = V1 ⊔ V2 := by
  apply le_antisymm
  · intro g hg
    exact h.ker g (MonoidHom.mem_ker.mp hg.1) (MonoidHom.mem_ker.mp hg.2)
  · refine sup_le (fun x hx => ⟨?_, ?_⟩) (fun x hx => ⟨?_, ?_⟩)
    · exact MonoidHom.mem_ker.mpr (h.alpha_V1 hx)
    · exact MonoidHom.mem_ker.mpr (h.beta_V1 hx)
    · exact MonoidHom.mem_ker.mpr (h.alpha_V2 hx)
    · exact MonoidHom.mem_ker.mpr (h.beta_V2 hx)

theorem H_normal (h : S8Data V1 V2 φ1 φ2 α β) : (s8H V2).Normal := by
  unfold s8H
  rw [h.cent_V2]
  haveI : β.ker.Normal := MonoidHom.normal_ker β
  exact Subgroup.commutator_normal _ _

theorem H_le_cent (h : S8Data V1 V2 φ1 φ2 α β) : s8H V2 ≤ centralizer (V2 : Set P) := by
  unfold s8H
  rw [h.cent_V2]
  haveI : β.ker.Normal := MonoidHom.normal_ker β
  exact Subgroup.commutator_le_left _ _

end S8Data

end CFSG.OddStandard.SmallF3.Omega
