module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Finish

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

structure KFactsL34 : Prop where
  twoSignalizer : KFactL34TwoSignalizer
  three : KFactL34Three
  unitary : KFactL34Unitary
  borel : KFactL34Borel
  graph : KFactL34Graph
  outThree : KFactL34OutThree
  sylowCentralizer : KFactL34SylowCentralizer
  threeExponent : KFactL34ThreeExponent

@[expose] def GL83GenericPrimeThreeL34Prop34 (G : Type) [Group G] [Finite G] : Prop :=
  GenericL34At G fun p P _ x J => L34Prop34 p P J x

@[expose] def GL83GenericPrimeThreeL34Lemma42 (G : Type) [Group G] [Finite G] : Prop :=
  GenericL34At G fun p P M x J => L34Prop34 p P J x → L34PointLemma42 p P M x

@[expose] def GL83GenericPrimeThreeL34Lemma43 (G : Type) [Group G] [Finite G] : Prop :=
  GenericL34At G fun p P M x J => L34Prop34 p P J x → L34PointLemma43 p P M x

@[expose] def GL83GenericPrimeThreeL34Remark (G : Type) [Group G] [Finite G] : Prop :=
  GenericL34At G fun p P M _ J => L34Remark p P M J

theorem GL83GenericPrimeThreeL34.of_parts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hK3 : KFactL34Unitary)
    (hK4 : KFactL34Borel) (hK5 : KFactL34Graph) (hK6 : KFactL34OutThree)
    (hK8 : KFactL34SylowCentralizer) (hK9 : KFactL34ThreeExponent)
    (h34 : GL83GenericPrimeThreeL34Prop34 G) (h42 : GL83GenericPrimeThreeL34Lemma42 G)
    (h43 : GL83GenericPrimeThreeL34Lemma43 G) (hrem : GL83GenericPrimeThreeL34Remark G) :
    GL83GenericPrimeThreeL34 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  have hJ : IsL34Normal M x J := ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker,
    hQ⟩
  have h34' := h34 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
  exact l34_false_of_config hS hU0 hD1 hInn hWC hK1 hK2 hK3 hK4 hK5 hK6 hK8 hK9 hp hM hgen hJ
    ⟨h34', h42 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ h34',
      h43 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ h34',
      hrem 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ⟩

@[expose] def GL83GenericPrimeThreeTypes3 (G : Type) [Group G] [Finite G] : Prop :=
  GenericRedThreeAt G fun Q _ =>
    Nonempty (Q ≃* PSL(2, GaloisField 3 2)) ∨
    (∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.exponent = 1 ∧ IsoLie Q (.twistedA 2 q)) ∨
    IsoLie Q (.A 1 ⟨2, 3, by norm_num, by norm_num⟩)

theorem GL83GenericPrimeThreeTypes4.of_three (h3 : GL83GenericPrimeThreeTypes3 G)
    (h34 : GL83GenericPrimeThreeL34 G) : GL83GenericPrimeThreeTypes4 G :=
  GenericRedThreeAt.mono (fun _ _ hQ => by
    rcases hQ with hQ | hQ | hQ | hQ
    · exact Or.inl (Or.inl hQ)
    · exact Or.inl (Or.inr (Or.inl hQ))
    · exact Or.inr hQ
    · exact Or.inl (Or.inr (Or.inr hQ))) (h3.union h34)

end CFSG.LocalAnalysis.RankThreeTheoremC
