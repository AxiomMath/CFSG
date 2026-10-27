module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.G2
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.PSLFamily
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Sp
public import CFSG.Quasithin.Background.C126RFCases
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

@[expose] def IsRestIndex : TauCeti.LieTypeIndex → Prop
  | .twistedA _ q | .D _ q | .twistedD _ q => q.p = 2
  | _ => False

@[expose] def G2Case (Y : Type) [Group Y] : Prop :=
  ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), d.1 = .G2 q ∧ q.p = 2 ∧
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def BCase (Y : Type) [Group Y] : Prop :=
  ∃ (d : TauCeti.ValidLieTypeIndex) (r : ℕ) (q : TauCeti.PrimePower), d.1 = .B r q ∧ q.p = 2 ∧
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def RestCase (Y : Type) [Group Y] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsRestIndex d.1 ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def LieInputRest : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], RestCase Y → SimpleStmt Y

theorem isClassicalTwoOrG2_cases {Y : Type} [Group Y] [Finite Y]
    (h : IsClassicalTwoOrG2 Y) :
    (∃ n f, StatedClassicalModel Y .PSL n 2 f) ∨ RestCase Y ∨ CFSG.Quasithin.IsAlt 6 Y ∨
      CFSG.Quasithin.IsPSU 3 3 1 Y ∨ G2Case Y ∨ BCase Y := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · obtain ⟨d, hv⟩ := d
    cases d with
    | A r q =>
      change q.p = 2 at hd
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hd] at h
      exact Or.inl ⟨_, _, h⟩
    | twistedA r q => exact Or.inr (Or.inl ⟨⟨_, hv⟩, hd, ⟨e⟩⟩)
    | B r q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨_, hv⟩, r, q, rfl, hd, ⟨e⟩⟩))))
    | C r q => exact hd.elim
    | D r q => exact Or.inr (Or.inl ⟨⟨_, hv⟩, hd, ⟨e⟩⟩)
    | twistedD r q => exact Or.inr (Or.inl ⟨⟨_, hv⟩, hd, ⟨e⟩⟩)
    | G2 q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨_, hv⟩, q, rfl, hd, ⟨e⟩⟩))))
    | _ => exact hd.elim
  · rcases hn with rfl | rfl | rfl
    · exact Or.inl ⟨2, 2, CFSG.Quasithin.C126.isPSL_two_two_two_of_alternating_five Y ⟨e⟩⟩
    · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
    · rcases (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff Y).2
        ⟨e⟩ with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact Or.inl ⟨4, 1, h⟩
      all_goals exact absurd h0 (by norm_num)
  · rcases hd with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
    · obtain ⟨d, hv⟩ := d
      have hdq' : d = .A 1 q := hdq
      subst hdq'
      have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hpe := (Nat.Prime.pow_eq_iff Nat.prime_seven).mp
        ((TauCeti.PrimePower.card_def q).symm.trans hq)
      rw [hpe.1, hpe.2] at hm
      exact Or.inl ⟨3, 1, CFSG.HardMathSupport.Cooperstein.StructureLie.isPSL_three_two_of_statedPSL_two_seven hm⟩
    · obtain ⟨dd, hv⟩ := d
      have hdq' : dd = .twistedA 2 q := hdq
      subst hdq'
      obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_three hq
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp, hf] at h
      exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem lieInputSimple_of_rest
    (hSpL : SpLeviOb) (hSpC : SpCentOb) (hrest : LieInputRest) : LieInputSimple := by
  intro Y _ _ hcl R hR
  rcases isClassicalTwoOrG2_cases hcl with ⟨n, f, h⟩ | hrc | h6 | hu | ⟨d, q, hd, hp, ⟨e⟩⟩ | ⟨d, r, q, hd, hp, ⟨e⟩⟩
  · exact simpleStmt_of_psl h R hR
  · exact hrest Y hrc R hR
  · exact simpleStmt_of_alt_six hcl h6 R hR
  · exact simpleStmt_of_psu_three_three hcl hu R hR
  · exact simpleStmt_of_g2_index hcl hd hp e R hR
  · exact simpleStmt_of_B_index hSpL hSpC hcl hd hp e R hR

theorem lieInputStatement_of_rest
    (hSpL : SpLeviOb) (hSpC : SpCentOb) (hrest : LieInputRest) : LieInputStatement :=
  lieInputStatement_of_simple (lieInputSimple_of_rest hSpL hSpC hrest)

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
