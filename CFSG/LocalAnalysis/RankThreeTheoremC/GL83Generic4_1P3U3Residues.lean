module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Residues

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83GenericPrimeThreeU3Prop34 (G : Type) [Group G] [Finite G] : Prop :=
  GenericU3At G fun p P _ x J => U3Prop34 p P J x

@[expose] def GL83GenericPrimeThreeU3Fusion (G : Type) [Group G] [Finite G] : Prop :=
  GenericU3At G fun _ P _ x _ =>
    (P : Subgroup G) ≤ centralizer ({x} : Set G) ∧ LineWeaklyClosed x (P : Subgroup G)

@[expose] def GL83GenericPrimeThreeU3Lemma43 (G : Type) [Group G] [Finite G] : Prop :=
  GenericU3At G fun p P M x J => U3Prop34 p P J x → U3PointLemma43 p P M J x

@[expose] def GL83GenericPrimeThreeTypes2 (G : Type) [Group G] [Finite G] : Prop :=
  GenericRedThreeAt G fun Q _ =>
    Nonempty (Q ≃* PSL(2, GaloisField 3 2)) ∨
    IsoLie Q (.A 1 ⟨2, 3, by norm_num, by norm_num⟩)

theorem GL83GenericPrimeThreeTypes3.of_two (h2 : GL83GenericPrimeThreeTypes2 G)
    (hU : GL83GenericPrimeThreeU3 G) : GL83GenericPrimeThreeTypes3 G :=
  GenericRedThreeAt.mono (fun _ _ hQ => by
    rcases hQ with hQ | hQ | hQ
    · exact Or.inl (Or.inl hQ)
    · exact Or.inr hQ
    · exact Or.inl (Or.inr hQ)) (h2.union hU)

end CFSG.LocalAnalysis.RankThreeTheoremC
