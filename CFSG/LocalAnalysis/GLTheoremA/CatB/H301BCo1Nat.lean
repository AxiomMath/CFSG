module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenTr
public import CFSG.Sporadic.Co1Patterson.NativeSetting
public import CFSG.Sporadic.Co1Patterson.GenerationClasses

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Sporadic.Co1Patterson CFSG.Blueprint CFSG.LargeExtraspecial

section Data


@[expose] noncomputable def co1R : Subgroup NativeSporadic.Co1 :=
  twoAQC.map (Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1)).subtype

@[expose] def UCo1 : Prop :=
  ∀ F X : Subgroup NativeSporadic.Co1, F ≤ Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1) →
    X ≤ Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1) → IsElemAbelian 3 F →
    Nat.card F = 3 ^ 4 → IsPGroup 2 X → F ≤ Subgroup.normalizer (X : Set NativeSporadic.Co1) →
    X ≤ co1R


theorem twoCentralData_co1 (hU : UCo1) : TwoCentralData 4 aNC co1R :=
  TwoCentralData.of_normal nativeSetting.z_ne_one twoAQC_normal
    ((Bridge.timmesfeldIsExtraspecial_iff (↥twoAQC)).2 twoAQC_extraspecial) twoAQC_centralizer_le
    (card_twoAQC.trans (by norm_num)) hU

end Data

section Classes


set_option maxRecDepth 100000 in
theorem isConj_aNC_of_dvd {s : NativeSporadic.Co1} (hs : orderOf s = 2)
    (h81 : 3 ^ 4 ∣ Nat.card (Subgroup.centralizer ({s} : Set NativeSporadic.Co1))) :
    IsConj s aNC := by
  have hcls₀ :=
    exists_involution_classes (Y := NativeSporadic.Co1) (MulEquiv.refl NativeSporadic.Co1)
  obtain ⟨a, b, c, hcls, -, -, -, -, -, -, hCa, hCb, hCc⟩ := hcls₀
  have hcardconj : ∀ {x y : NativeSporadic.Co1}, IsConj x y →
      Nat.card (Subgroup.centralizer ({x} : Set NativeSporadic.Co1)) =
        Nat.card (Subgroup.centralizer ({y} : Set NativeSporadic.Co1)) := by
    intro x y h
    obtain ⟨g, rfl⟩ := isConj_iff.1 h
    rw [CFSG.Sporadic.Co1Block.card_centralizer_equiv (MulAut.conj g) x, MulAut.conj_apply]
  have haA : IsConj a aNC := by
    rcases hcls aNC orderOf_aNC with h | h | h
    · exact h
    · have := hcardconj h
      rw [hCb, card_centralizer_aNC] at this
      norm_num at this
    · have := hcardconj h
      rw [hCc, card_centralizer_aNC] at this
      norm_num at this
  rcases hcls s hs with h | h | h
  · exact h.symm.trans haA
  · exfalso
    rw [← hcardconj h, hCb] at h81
    norm_num at h81
  · exfalso
    rw [← hcardconj h, hCc] at h81
    norm_num at h81

end Classes

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
