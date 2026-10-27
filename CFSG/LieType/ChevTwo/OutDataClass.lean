module

public import CFSG.LieType.ChevTwo.Defs
public import CFSG.LieType.ChevTwo.OutDataGen
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.PSL2TwoNilpotent
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.Quasithin.Vol2.GoldschmidtTDOutLin
import CFSG.Quasithin.Vol2.GoldschmidtTDOutSp
import CFSG.Quasithin.Vol2.GoldschmidtTDOutExc
import CFSG.Quasithin.Vol2.GoldschmidtTDOutAlt
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Symplectic
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrModel
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import Certificates.Certificate119
public import Certificates.Certificate122

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open (StatedClassicalModel StatedLieTag)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)
open CFSG.Quasithin.H13.OutTwoNilp (outTwoNilpotent_of_twoNilpotent_outer
  twoNilpotent_outer_of_odd_diagonal twoNilpotent_outer_of_three twoNilpotent_outer_of_psl_two
  twoNilpotent_outer_of_psp_two twoNilpotent_outer_of_G2 twoNilpotent_outer_of_alt)
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower (outerComm_statedProj_sp OuterComm)
open TauCeti

private theorem odd_gcd_two_pow_sub {n f : ℕ} {ε : ℤ} (hf : 1 ≤ f) (hε : Odd ε) :
    Odd (Int.gcd n (((2 : ℕ) : ℤ) ^ f - ε)) := by
  have hm : Odd (((2 : ℕ) : ℤ) ^ f - ε) := by
    have h2 : Even (((2 : ℕ) : ℤ) ^ f) := by
      rw [Nat.cast_ofNat]
      exact (Int.even_pow.mpr ⟨even_two, by omega⟩)
    exact h2.sub_odd hε
  have hd : Int.gcd n (((2 : ℕ) : ℤ) ^ f - ε) ∣ (((2 : ℕ) : ℤ) ^ f - ε).natAbs :=
    Int.natCast_dvd.mp (Int.gcd_dvd_right ..)
  exact Odd.of_dvd_nat (Int.natAbs_odd.mpr hm) hd

private theorem twoNilpotent_outer_of_psl_psu_even {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {t : StatedLieTag} {n f : ℕ} (ht : t = .PSL ∨ t = .PSU)
    (hm : StatedClassicalModel S t n 2 f) : TwoNilpotent (Outer S) := by
  have hf : 1 ≤ f := hm.1.2.1
  rcases ht with rfl | rfl
  · exact twoNilpotent_outer_of_odd_diagonal hna (ε := 1) (Or.inl ⟨rfl, rfl⟩) hm
      (odd_gcd_two_pow_sub hf odd_one)
  · exact twoNilpotent_outer_of_odd_diagonal hna (ε := -1) (Or.inr ⟨rfl, rfl⟩) hm
      (odd_gcd_two_pow_sub hf ⟨-1, by norm_num⟩)

private theorem twoNilpotent_outer_of_psp_even {S : Type} [Group S] [Finite S] {n f : ℕ}
    (hm : StatedClassicalModel S .PSp n 2 f) : TwoNilpotent (Outer S) := by
  obtain ⟨-, hf, hn2, hne⟩ := hm.1
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have hn' : n = 2 := by omega
    subst hn'
    have hf2 : 2 ≤ f := by
      by_contra hlt
      have : f = 1 := by omega
      subst this
      exact hne (by norm_num)
    exact twoNilpotent_outer_of_psp_two hf2 hm
  · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hm
    exact twoNilpotent_outer_of_commutator_mem_inner
      (OuterComm.of_mulEquiv eK (outerComm_statedProj_sp h3 K))

private theorem twoNilpotent_outer_of_G2_index
    (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p = 2) {Y : Type} [Group Y]
    [Finite Y] (e : Y ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : TwoNilpotent (Outer Y) := by
  haveI : Finite (CFSGIndex.lie ⟨.G2 q, hv⟩).Group := Finite.of_equiv Y e.toEquiv
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨e0⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp2
    (GaloisField q.p q.exponent) hK
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2
      q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩, GaloisField q.p q.exponent, inferInstance,
      inferInstance, ?_, ⟨e0.symm⟩⟩
    · rw [← PrimePower.card_def]
      exact hq3
    · rw [hK, PrimePower.card_def]
  rw [hp2] at hce
  have hf2 : 2 ≤ q.exponent := by
    have h3 : 3 ≤ 2 ^ q.exponent := hce.1.2.2.2
    by_contra hlt
    have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [h1] at h3
    norm_num at h3
  exact TwoNilpotent.of_mulEquiv (equivalence e).symm (twoNilpotent_outer_of_G2 hf2 hce)

private theorem twoNilpotent_outer_of_small_index {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hna : ∃ a b : Y, a * b ≠ b * a) (d : ValidLieTypeIndex)
    (hd : (∃ q : PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
      (∃ q : PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q))
    (e : Y ≃* (CFSGIndex.lie d).Group) : TwoNilpotent (Outer Y) := by
  obtain ⟨d1, hv⟩ := d
  rcases hd with ⟨q, hq, hd1⟩ | ⟨q, hq, hd1⟩
  · simp only at hd1
    subst hd1
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    have hq' : q.p ^ q.exponent = 7 := by rw [← PrimePower.card_def]; exact hq
    obtain ⟨hp7, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq'
    rw [hp7, he1] at h
    exact twoNilpotent_outer_of_psl_two hna h
  · simp only at hd1
    subst hd1
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    have hq' : q.p ^ q.exponent = 3 := by rw [← PrimePower.card_def]; exact hq
    obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp hq'
    rw [hp3, he1] at h
    exact twoNilpotent_outer_of_three hna (Or.inr ⟨rfl, rfl⟩) h

theorem outTwoNilp_of_isClassicalTwoOrG2_of_orth
    (hP : ∀ (X : Type) [Group X] (n m : ℕ), StatedClassicalModel X .POmegaPlus n 2 m →
      TwoNilpotent (Outer X))
    (hM : ∀ (X : Type) [Group X] (n m : ℕ), StatedClassicalModel X .POmegaMinus n 2 m →
      TwoNilpotent (Outer X))
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (h : CFSG.AGLEmbedding.IsClassicalTwoOrG2 S) : OutTwoNilpConcl S := by
  haveI := hs
  refine outTwoNilpotent_of_twoNilpotent_outer ?_
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · rcases CFSG.AGLEmbedding.ParabAutIrr.classical_model_or_g2 d hd e with
      ⟨t, n, f, ht, hm⟩ | ⟨q, hq, hq2, hdq⟩
    · rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact twoNilpotent_outer_of_psl_psu_even hna (Or.inl rfl) hm
      · exact twoNilpotent_outer_of_psl_psu_even hna (Or.inr rfl) hm
      · exact twoNilpotent_outer_of_psp_even hm
      · exact hP _ _ _ hm
      · exact hM _ _ _ hm
    · subst hdq
      exact twoNilpotent_outer_of_G2_index q hq hq2 e
  · rcases hn with rfl | rfl | rfl <;>
      exact twoNilpotent_outer_of_alt (by norm_num) (by norm_num) e
  · exact twoNilpotent_outer_of_small_index hna d hd e

end CFSG.LieType.ChevTwo
