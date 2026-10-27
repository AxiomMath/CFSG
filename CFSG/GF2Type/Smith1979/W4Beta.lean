module

public import CFSG.GF2Type.Smith1979.W4AsSurvMain
public import CFSG.GF2Type.Smith1979.W4AsLin
public import CFSG.GF2Type.Smith1980Orth.Final

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.Open

section BetaDichotomy


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G} {g : G}

theorem beta_dichotomy (hw : S.width = 4) (hno : S11.NoA2All S) (hirr : ¬ S.IsReducible)
    (H : Hyp4 S g) (C : Cons311 S g) :
    ((∀ h : S.M, S.Lbar ((h : G) * g) ⊓ S.Lbar g = ⊥ ∨ S.Lbar ((h : G) * g) = S.Lbar g) ∧
      (StatedClassicalModel (M0 S g) .PSL 2 2 3 ∨
        Nonempty (M0 S g ≃* alternatingGroup (Fin 9)))) ∨
    ∃ (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      OmegaCase H C ht ht1 hVQ ∧ finrank (ZMod 2) (Vt S g t) = 4 := by
  have I : Smith1980Orth.TimInputs := Smith1980Orth.timInputs_holds
  have hNo : NoA2 S g := fun α h1 h2 h3 => hno g H.conj_mem H.conj_ne ⟨α, h1, h2, h3⟩
  by_cases hTI : ∀ h : S.M, S.Lbar ((h : G) * g) ⊓ S.Lbar g = ⊥ ∨ S.Lbar ((h : G) * g) = S.Lbar g
  · exact Or.inl ⟨hTI, (S4.lemma_4_2 I.hF2 I.hBen I.hTI H C hNo hTI hirr).2⟩
  · right
    by_cases hΩ : ∀ t ∈ S.Lbar g, t ≠ 1 → V S g t ≤ S.Qa g
    · obtain ⟨t, ht, ht1, hR⟩ := exists_Rbar_ne_of_not_TI hTI
      exact (false_of_lin_only (s11_1Stmt_w4 layerSurvivorsW4_holds) hw hno hirr H C hΩ
        ⟨t, ht, ht1, hR⟩).elim
    · push Not at hΩ
      obtain ⟨t, ht, ht1, hVQ⟩ := hΩ
      have hR : Rbar S g t ≠ S.Lbar g := fun h => hVQ (S11.V_le_Qa_of_Rbar_eq H C h)
      rcases classify_four hw H hNo C ht ht1 hR with ⟨hL, -⟩ | ⟨hVQ', hΩ', h4⟩
      · exact absurd hL.le_Qa hVQ
      · exact ⟨t, ht, ht1, hVQ', hΩ', h4⟩

end BetaDichotomy

end CFSG.GF2Type.Smith1979.W4As
