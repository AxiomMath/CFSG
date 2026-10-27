module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Good
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescCTwo
public import CFSG.LocalAnalysis.GLTheoremA.S9.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Lie TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def TD4Alt : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), KHyp p K B →
    Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3 → TD4Exc p K B →
    KConcl p K B ∨ ∃ D J : Subgroup Y, DescData p K B D J

@[expose] def TD4Res : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), 2 < q.card → ¬ 3 ∣ q.card →
    IsChevSimple 2 (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group → GoodSubAt 3 ⟨.trialityD4 q, hv⟩ 2

theorem td4Alt_of_goodSub (h : TD4Res) : TD4Alt := by
  intro p hp hp2 Y _ _ K B hK hc hT
  obtain ⟨rfl, -, hC, hcat, -⟩ := hT
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | trialityD4 q =>
      obtain ⟨hq2c, hq3⟩ := hi
      haveI : Finite (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := Finite.of_equiv _ e.toEquiv
      have hchev : IsChevSimple 2 (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group :=
        (CFSG.LocalAnalysis.GLTheoremA.S9.isChevSimple_congr e).1 hK.chev
      left
      exact kConcl_of_goodSub hp hp2 hK ⟨.trialityD4 q, hv⟩ e (k := 2) (by norm_num)
        (h q hv hq2c hq3 hchev) (by simpa using hC)
    | _ => exact hi.elim

@[expose] def LpEpsNoGoodTwoLocal (p : ℕ) (d : ValidLieTypeIndex) : Prop :=
  lpEpsIdx p d.1 → ∀ D : Subgroup (MulAut (CFSGIndex.lie d).Group), IsElemAbelian p D →
    Nat.card D = p ^ 2 → D ≤ innAutDerived (CFSGIndex.lie d).Group →
    innAutDerived (CFSGIndex.lie d).Group ⊓ Subgroup.centralizer (D : Set (MulAut (CFSGIndex.lie d).Group)) = D →
    (¬ ∃ β ∈ D, β ≠ 1 ∧ ∃ P : Subgroup (CFSGIndex.lie d).Group, P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧
      p ∣ Nat.card P) →
    ∀ T : Subgroup (CFSGIndex.lie d).Group, IsPGroup 2 T → T ≠ ⊥ →
      (∀ α ∈ D, T.map α.toMonoidHom = T) → False

section SLevel

variable (d : ValidLieTypeIndex) [Finite (CFSGIndex.lie d).Group]

theorem exists_good_element_of_pair' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN2 : KD264OuterIdx) (hN3 : KD264InnGood) (hPL : KD264PL p)
    (hchar : p ≠ d.1.characteristic) (hdvd : p ∣ Nat.card (CFSGIndex.lie d).Group)
    (h3 : ¬ (p = 3 ∧
      ((∃ q : PrimePower, (d.1 = .A 1 q ∨ d.1 = .twistedA 2 q) ∧ q.card = 8) ∨
        (∃ q : PrimePower, d.1 = .trialityD4 q))))
    (h5 : ¬ (p = 5 ∧ d.1 = .suzuki 2)) (hgf2 : ¬ (p = 3 ∧ ov2Idx d.1))
    (htits : ¬ (p = 5 ∧ d.1 = .tits)) (hlp : LpEpsNoGoodTwoLocal p d)
    {D : Subgroup (MulAut (CFSGIndex.lie d).Group)} (hD : IsElemAbelian p D)
    (hD2 : Nat.card D = p ^ 2) {T : Subgroup (CFSGIndex.lie d).Group} (hT2 : IsPGroup 2 T)
    (hT : T ≠ ⊥) (hDT : ∀ α ∈ D, T.map α.toMonoidHom = T) :
    ∃ a ∈ D, a ≠ 1 ∧ GLAPLayer p (fixSubgroup a) ≠ ⊥ := by
  by_cases hDi : D ≤ innAutDerived (CFSGIndex.lie d).Group
  · by_cases hgood : ∃ β ∈ D, β ≠ 1 ∧ ∃ P : Subgroup (CFSGIndex.lie d).Group,
        P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P
    · obtain ⟨β, hβD, hβ1, P, hPfix, hPperf, hpP⟩ := hgood
      have hβp : β ^ p = 1 := hD.2 β hβD
      obtain ⟨J, hJ, hJp⟩ := hPL d hchar β hβp hβ1 P hPfix hPperf hpP
      exact ⟨β, hβD, hβ1, layer_ne_bot_of_component d hp hJ hJp⟩
    · rcases hN3 d p hp hp2 hchar hgf2 htits D hD hD2 hDi with h | ⟨hlpe, hself⟩
      · exact absurd h hgood
      · exact (hlp hlpe D hD hD2 hDi hself hgood T hT2 hT hDT).elim
  · obtain ⟨b, hbD, hbi⟩ := SetLike.not_le_iff_exists.1 hDi
    have hb1 : b ≠ 1 := fun h => hbi (h ▸ (innAutDerived _).one_mem)
    have hbp : b ^ p = 1 := hD.2 b hbD
    obtain ⟨J, hJ, hJp, -⟩ := hN2 d p hp hp2 hchar hdvd h3 h5 b hbp hbi
    exact ⟨b, hbD, hb1, layer_ne_bot_of_component d hp hJ hJp⟩

end SLevel

theorem goodSub_one_of_inputs' (d : ValidLieTypeIndex) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN2 : KD264OuterIdx) (hN3 : KD264InnGood) (hPL : KD264PL p) (hchar : p ≠ d.1.characteristic)
    (h3 : ¬ (p = 3 ∧
      ((∃ q : PrimePower, (d.1 = .A 1 q ∨ d.1 = .twistedA 2 q) ∧ q.card = 8) ∨
        (∃ q : PrimePower, d.1 = .trialityD4 q))))
    (h5 : ¬ (p = 5 ∧ d.1 = .suzuki 2)) (hgf2 : ¬ (p = 3 ∧ ov2Idx d.1))
    (htits : ¬ (p = 5 ∧ d.1 = .tits)) (hlp : LpEpsNoGoodTwoLocal p d) : GoodSubAt p d 1 := by
  intro _ hdvd A hA hcard T hT2 hT hAT
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, hDA, hDcard⟩ := exists_sub_card_pow (n := 2) hp hA (by simpa using hcard)
  obtain ⟨a, haD, ha1, hgood⟩ := exists_good_element_of_pair' d hp hp2 hN2 hN3 hPL hchar hdvd h3 h5
    hgf2 htits hlp (isElemAbelian_mono hA hDA) hDcard hT2 hT fun α hα => hAT α (hDA hα)
  have hap : orderOf a = p := orderOf_eq_prime ((isElemAbelian_mono hA hDA).2 a haD) ha1
  refine ⟨Subgroup.zpowers a, Subgroup.zpowers_le.2 (hDA haD), ?_, ?_⟩
  · rw [Nat.card_zpowers, hap, pow_one]
  · unfold IsGood
    rw [iInf_fixSubgroup_zpowers]
    exact hgood

@[expose] def LinearRes : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.A 2 q).Valid), q.p = 2 → Even q.exponent →
    LpEpsNoGoodTwoLocal 3 ⟨.A 2 q, hv⟩ ∧ GoodSubAt 3 ⟨.A 2 q, hv⟩ 2

@[expose] def UnitaryRes : Prop :=
  (∀ (q : PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid), q.p = 2 → Odd q.exponent →
    q.card ≠ 8 → LpEpsNoGoodTwoLocal 3 ⟨.twistedA 2 q, hv⟩ ∧ GoodSubAt 3 ⟨.twistedA 2 q, hv⟩ 2) ∧
  (∀ (q : PrimePower) (hv : (LieTypeIndex.twistedA 3 q).Valid), q.card = 8 →
    GoodSubAt 3 ⟨.twistedA 3 q, hv⟩ 2) ∧
  (∀ (q : PrimePower) (hv : (LieTypeIndex.twistedA 5 q).Valid), q.card = 2 →
    GoodSubAtLow 3 ⟨.twistedA 5 q, hv⟩ 1 ∧ GoodSubAtLow 3 ⟨.twistedA 5 q, hv⟩ 2)

@[expose] def SymplecticRes : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid), q.p = 2 → q.card = 8 →
    TwoLocalRankLE1 3 (CFSGIndex.lie ⟨.B 2 q, hv⟩).Group

@[expose] def G2Res : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 → q.card = 8 →
    TwoLocalRankLE1 3 (CFSGIndex.lie ⟨.G2 q, hv⟩).Group

@[expose] def ReeTitsRes : Prop :=
  (∀ (hv : (LieTypeIndex.reeF4 1).Valid), TwoLocalRankLE1 3 (CFSGIndex.lie ⟨.reeF4 1, hv⟩).Group) ∧
  (∀ (hv : (LieTypeIndex.reeF4 2).Valid), TwoLocalRankLE1 5 (CFSGIndex.lie ⟨.reeF4 2, hv⟩).Group)

end CFSG.LocalAnalysis.GLTheoremA.HDesc
