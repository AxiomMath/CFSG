module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinAbs
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeOut
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Cl4E0
public import CFSG.LargeExtraspecial.DW2AOut
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating
open CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

@[expose] def SmallExitD4At (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G)
    (hS : Setup p L J A d b),
    catalogIs (PSimple p L) (onLie P) →
    ¬ CFSG.LocalAnalysis.GLTheoremA.I171.I171LieShapeAt p L → InducesInnerMod p L b →
    catalogIs (PSimple p J) (onLie fun i : TauCeti.LieTypeIndex =>
      ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2) →
    MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J) →
    InducesInnerMod p J b

abbrev ExcSmallExitD4 : Prop :=
  SmallExitD4At fun i : TauCeti.LieTypeIndex =>
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.isExcUntwistedIdx i ∧ i.characteristic = 2

abbrev TwE6SmallExitD4 : Prop :=
  SmallExitD4At fun i : TauCeti.LieTypeIndex =>
    (∃ q : TauCeti.PrimePower, i = .twistedE6 q) ∧ i.characteristic = 2

theorem isPGroup_outer_of_card_360
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) (hchev : IsChevSimple 2 S) (hcard : Nat.card S = 360) :
    IsPGroup 2 (Outer S) := by
  have hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  rcases CFSG.LocalAnalysis.GLTheoremA.I1416Rows.chev_card_dvd_241920_cases hb hnab hchev
      (by rw [hcard]; norm_num) (by rw [hcard]; norm_num) with h60 | h168 | ⟨-, ⟨e⟩⟩ | h504
  · omega
  · omega
  · exact CFSG.LargeExtraspecial.DW.isPGroup_outer_alt6 e
  · exact absurd h504.1 (by omega)

theorem isPGroup_outer_of_ambiguous_two {S : Type} [Group S]
    (h : catalogIs S (ambiguousChev 2)) : IsPGroup 2 (Outer S) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases CFSG.StandardType.ChevTwo.ambiguousChev_two_cases hi with
    ⟨h5, rfl⟩ | ⟨h6, rfl⟩ | ⟨h8, rfl⟩ | ⟨q, hv, hq7, rfl⟩ | ⟨q, hv, hq3, rfl⟩
  · have hA5 := alternating_five_unique_Sylow_two_containment_and_solvable_normalizer
    have hdvd : Nat.card (Outer (alternatingGroup (Fin 5))) ∣ 2 := hA5.2.2.2.2.2.2
    exact (IsPGroup.of_card_dvd_pow (p := 2) (n := 1) hdvd).of_equiv
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm
  · exact CFSG.LargeExtraspecial.DW.isPGroup_outer_alt6 e
  · have hdvd : Nat.card (Outer S) ∣ 2 :=
      outer_card_dvd_two_of_equiv_outside_six (G := S) (n := 8) (by norm_num) e
    exact IsPGroup.of_card_dvd_pow (p := 2) (n := 1) hdvd
  · have hmodel : StatedClassicalModel S .PSL 2 q.p q.exponent :=
      CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    have hq' : q.p ^ q.exponent = 7 := by
      rw [← TauCeti.PrimePower.card_def]
      exact hq7
    obtain ⟨hp7, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq'
    rw [hp7, he1] at hmodel
    exact IsPGroup.of_card_dvd_pow (p := 2) (n := 1)
      (CFSG.AGLEmbedding.card_outer_dvd_two_of_psl_seven hmodel)
  · have hmodel : StatedClassicalModel S .PSU 3 q.p q.exponent :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    have hq' : q.p ^ q.exponent = 3 := by
      rw [← TauCeti.PrimePower.card_def]
      exact hq3
    obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp hq'
    rw [hp3, he1] at hmodel
    have hcard : Nat.card (Outer S) = 2 := CFSG.Quasithin.S143.InspW2.card_outer_u33 hmodel
    exact IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])

theorem isPGroup_outer_of_tits
    {S : Type} [Group S] (hv : (TauCeti.LieTypeIndex.tits).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) : IsPGroup 2 (Outer S) := by
  have hR : CFSG.Blueprint.ReeTitsModel (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group .Tits 2 1 :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_tits_of_lie hv (MulEquiv.refl _)
  exact (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier _ 2 1 hR).1.of_equiv
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm

section SmallExit


theorem smallExit_of_D4At {P : TauCeti.LieTypeIndex → Prop} (hD4 : SmallExitD4At P)
    {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G)
    (hS : Setup p L J A d b) (hcatL : catalogIs (PSimple p L) (onLie P))
    (hshape : ¬ CFSG.LocalAnalysis.GLTheoremA.I171.I171LieShapeAt p L)
    (hInnerL : InducesInnerMod p L b)
    (hCatJ : catalogIs (PSimple p J) (ambiguousChev 2) ∨
      catalogIs (PSimple p J) (onLie fun i : TauCeti.LieTypeIndex =>
        (∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2) ∨ i = .tits) ∨
      Nat.card (PSimple p J) = 360)
    (hLast : MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J) ∨
      Nat.card (PSimple p J) = 360) :
    InducesInnerMod p J b := by
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.odd
  have hpOdd : Odd p := hp.odd_of_ne_two hp2
  have hbp : b ^ p = 1 := hS.elem.2 b hS.b_mem
  have hpow : MI.indAut p J b hS.b_norm ^ p = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.l154_indAut_pow_eq_one hS.b_norm hbp
  refine (MI.indAut_mem_inner_iff hp hS.pcomp hS.b_norm).1 ?_
  by_cases h360 : Nat.card (PSimple p J) = 360
  · obtain ⟨hsimple, hnab⟩ := chev_pSimple_simple_nonabelian hp hS.pcomp
    haveI := hsimple
    exact CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer
      (isPGroup_outer_of_card_360 hnab hS.chevJ h360) hpOdd hpow
  · rcases hCatJ with hamb | hdt | h360'
    · exact CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer
        (isPGroup_outer_of_ambiguous_two hamb) hpOdd hpow
    · obtain ⟨i, hi, ⟨e⟩⟩ := hdt
      rcases i with _ | _ | ⟨d, hv⟩ | _
      · exact absurd hi (by simp [onLie])
      · exact absurd hi (by simp [onLie])
      · rcases hi with ⟨q, rfl, hq2⟩ | rfl
        · rcases hLast with hmem | hbad
          · exact (MI.indAut_mem_inner_iff hp hS.pcomp hS.b_norm).2
              (hD4 p L J A d b hS hcatL hshape hInnerL
                ⟨(TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩ : TauCeti.CFSGIndex),
                  ⟨q, rfl, hq2⟩, ⟨e⟩⟩ hmem)
          · exact absurd hbad h360
        · exact CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer
            (isPGroup_outer_of_tits hv e) hpOdd hpow
      · exact absurd hi (by simp [onLie])
    · exact absurd h360' h360

theorem excSmallExit_of (hD4 : ExcSmallExitD4) : ExcSmallExit :=
  fun p L J A d b hS => smallExit_of_D4At hD4 p L J A d b hS

theorem twE6SmallExit_of (hD4 : TwE6SmallExitD4) : TwE6SmallExit :=
  fun p L J A d b hS => smallExit_of_D4At hD4 p L J A d b hS

end SmallExit

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
