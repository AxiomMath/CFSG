module

public import CFSG.LargeExtraspecial.S3cMain
public import CFSG.LargeExtraspecial.S4Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Loc

open Subgroup CFSG.LargeExtraspecial.S4

variable {X : Type} [Group X] [Finite X] {T : Setting X}

theorem hyp4_of_w4 (hTI : WeaklyClosedTITransitive.{0}) (hn : 4 ≤ T.width) {g : X}
    (haQ : g * T.z * g⁻¹ ∈ T.QG) (hne : g * T.z * g⁻¹ ≠ T.z) (hno : ¬ T.HasTypeAInL g)
    (hirr : ¬ T.IsReducible) : Hyp4 T g where
  conj_mem := haQ
  conj_ne := hne
  fixSub_eq := by
    rw [← T.fixLbar_eq_span hTI hn haQ hne hno hirr]
    ext v
    rw [mem_fixSub, Setting.mem_fixLbar]
  two_lt_width := by omega

theorem cons311_of_w4 (hTI : WeaklyClosedTITransitive.{0}) (hn : 4 ≤ T.width) {g : X}
    (haQ : g * T.z * g⁻¹ ∈ T.QG) (hne : g * T.z * g⁻¹ ≠ T.z) (hno : ¬ T.HasTypeAInL g)
    (hirr : ¬ T.IsReducible) : Cons311 T g := by
  obtain ⟨hL, hX, -, -, hC⟩ := (T.lemma_3_11_two hTI (by omega) haQ hne hno).resolve_left hirr
  exact {
    weaklyClosed := fun h hh hle => T.lemma_3_11_weaklyClosed (by omega) haQ hne hno hh hle
    card_Lbar := hL
    card_QG_inf_Qa := hX
    comm_le := fun x hx s hs => T.sub_mem_clSub_of_mem_Lbar haQ hne hs hx.1
      (mem_centralizer_singleton_iff.mp hx.2)
    faithful := hC }

end CFSG.LargeExtraspecial.S14.W4Loc
