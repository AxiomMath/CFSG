module

public import CFSG.GF2Type.Aschbacher1976Full.WidthCore

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

instance Fz_subgroupOf_normal (z : G) : ((Fz z).subgroupOf (Hz z)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using Aschbacher1976Full.Width.Fz_conj_mem g.2 hn

@[expose] abbrev Qbar (z : G) : Type := ↥(Hz z) ⧸ (Fz z).subgroupOf (Hz z)

@[expose] def qmk (z : G) : ↥(Hz z) →* Qbar z := QuotientGroup.mk' _

theorem qmk_eq_one_iff (z : G) (h : ↥(Hz z)) : qmk z h = 1 ↔ (h : G) ∈ Fz z := by
  simp [qmk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem qmk_surjective (z : G) : Function.Surjective (qmk z) := QuotientGroup.mk'_surjective _

theorem ker_qmk (z : G) : (qmk z).ker = (Fz z).subgroupOf (Hz z) := by
  ext h
  rw [MonoidHom.mem_ker, qmk_eq_one_iff, Subgroup.mem_subgroupOf]

end CFSG.GF2Type.Aschbacher1976Full.HS
