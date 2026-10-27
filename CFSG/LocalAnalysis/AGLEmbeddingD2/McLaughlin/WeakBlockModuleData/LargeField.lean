module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPureAssembly

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Open CFSG.QuasithinUnique

@[expose] def LieField : TauCeti.LieTypeIndex → ℕ
  | .A _ q | .twistedA _ q | .B _ q | .C _ q | .D _ q | .twistedD _ q | .G2 q => q.card
  | _ => 0

@[expose] def LargeFieldParabolic : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (Lb P : Subgroup Q), CFSG.Open.IsQuasisimple ↥Lb →
    ∀ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2Index d.1 → 4 ≤ LieField d.1 →
      Nonempty (↥Lb ⧸ Subgroup.center ↥Lb ≃* (TauCeti.CFSGIndex.lie d).Group) →
      IsParabolicTwo Lb P → ¬ IsSylowTwoOf (pCoreOf 2 P) Lb →
        ∃ J : Subgroup Q, J ≤ P ∧ ⁅J, J⁆ = J ∧ 3 ∣ Nat.card J

variable {G : Type} [Group G] [Finite G]

theorem lieField_lt_four_of_nineThreeTwo (hLF : LargeFieldParabolic) {M S L : Subgroup G}
    (hL : IsWeakSBlock M S L) (h2 : NineThreeTwo M S L)
    (hSyl : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L))
    (hsolv : BlockPLThreeSolv M S L) (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2Index d.1)
    (e : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* (TauCeti.CFSGIndex.lie d).Group) :
    LieField d.1 < 4 := by
  by_contra hq
  obtain ⟨-, hpar, hcore⟩ := h2
  obtain ⟨J, hJP, hJperf, hJ3⟩ := hLF (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L)
    (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) hL.component.2.2 d hd (by omega) ⟨e⟩ hpar
    (by rw [← hcore]; exact hSyl)
  exact hsolv J hJP hJperf hJ3

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
