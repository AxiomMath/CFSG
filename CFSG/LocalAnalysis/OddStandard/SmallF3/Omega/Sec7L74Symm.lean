module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74Props
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem inv_conj_inv_cancel (g x : G) : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by
  group

theorem orderOf_conj_inv (g x : G) : orderOf (g⁻¹ * x * g) = orderOf x := by
  rw [show g⁻¹ * x * g = (MulAut.conj g⁻¹) x by simp [MulAut.conj_apply], MulEquiv.orderOf_eq]

theorem Sec74Ass.orderOf_s [Finite G] {t : G} {L S : Subgroup G} {z g : G}
    (h : Sec74Ass G t L S z g) : orderOf (g⁻¹ * t * g) = 2 := by
  rw [orderOf_conj_inv]
  exact h.ctx.involution

theorem Sec74Ass.s_mem_normalizer [Finite G] (h36 : Asc82Lemma36) {t : G} {L S : Subgroup G}
    {z g : G} (h : Sec74Ass G t L S z g) : g⁻¹ * t * g ∈ normalizer (L : Set G) :=
  h.ctx.cent_le_normalizer h36 _ h.comm

theorem Sec74Ass.symm [Finite G] {t : G} {L S : Subgroup G} {z g : G}
    (h : Sec74Ass G t L S z g) :
    Sec74Ass G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g) (g⁻¹ * z * g) g⁻¹ where
  ctx := h.ctx.conjugate g
  comm := by
    rw [inv_conj_inv_cancel]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp h.comm).symm
  ne := by
    rw [inv_conj_inv_cancel]
    exact fun h' => h.ne h'.symm
  not1 := by
    intro hc
    apply h.not1
    have h1 : IsConj t (g⁻¹ * t * g) := isConj_iff.mpr ⟨g⁻¹, by group⟩
    have h2 : IsConj (g⁻¹ * t * g * (g⁻¹ * z * g)) (t * z) :=
      isConj_iff.mpr ⟨g, by group⟩
    exact (h1.trans hc).trans h2

end CFSG.OddStandard.SmallF3.Omega
