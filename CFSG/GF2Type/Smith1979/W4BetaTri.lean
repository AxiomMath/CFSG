module

public import CFSG.GF2Type.Smith1979.W4Beta
public import CFSG.GF2Type.Smith1979.W4TIA9

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.Open

section BetaTrichotomy


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G} {g : G}

theorem beta_trichotomy (hw : S.width = 4) (hno : S11.NoA2All S) (hirr : ¬ S.IsReducible)
    (H : Hyp4 S g) (C : Cons311 S g) :
    StatedClassicalModel (M0 S g) .PSL 2 2 3 ∨ Nonempty (S.Mbar ≃* alternatingGroup (Fin 9)) ∨
    ∃ (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      OmegaCase H C ht ht1 hVQ ∧ finrank (ZMod 2) (Vt S g t) = 4 := by
  rcases beta_dichotomy hw hno hirr H C with ⟨hTI, h8 | he⟩ | hΩ
  · exact Or.inl h8
  · obtain ⟨e⟩ := he
    have I : Smith1980Orth.TimInputs := Smith1980Orth.timInputs_holds
    have htop := M0_eq_top_of_A9 H C hirr hw (normTrans_LM0 I.hF2 H C hTI hirr) e
    refine Or.inr (Or.inl ⟨?_⟩)
    exact (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e
  · exact Or.inr (Or.inr hΩ)

end BetaTrichotomy

end CFSG.GF2Type.Smith1979.W4As
