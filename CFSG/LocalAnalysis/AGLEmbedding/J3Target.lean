module

public import CFSG.LocalAnalysis.AGLEmbedding.J3Facts
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.Schreier.PairJ3Faithful
public import CFSG.Sporadic.Schreier.PairOuter
public import CFSG.RankThree.Asc83Table.J3
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint

theorem card_sylow_three_of_card_eq {L : Type*} [Group L] [Finite L]
    (hcard : Nat.card L = 50232960) (S : Sylow 3 L) : Nat.card (S : Subgroup L) = 3 ^ 5 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [S.card_eq_multiplicity, hcard, show (50232960 : ℕ) = 3 ^ 5 * 206720 by norm_num,
    Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 206720)]
  simp

theorem nonabelian_of_card_eq {L : Type*} [Group L] [Finite L] [IsSimpleGroup L]
    (hcard : Nat.card L = 50232960) : ∃ a b : L, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 L) := inferInstance
  have hS := card_sylow_three_of_card_eq hcard S
  have hSn : (S : Subgroup L).Normal :=
    ⟨fun x hx g => by rw [hcomm g x, mul_inv_cancel_right]; exact hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S : Subgroup L) with h1 | h1
  · rw [h1, Subgroup.card_bot] at hS
    norm_num at hS
  · rw [h1, Subgroup.card_top, hcard] at hS
    norm_num at hS

theorem card_dvd_of_isPGroup_mulAut {L : Type*} [Group L] [Finite L]
    (hcard : Nat.card L = 50232960) (hOut : Nat.card (Outer L) ≤ 2)
    (S : Subgroup (MulAut L)) (hS : IsPGroup 3 S) : Nat.card S ∣ 3 ^ 5 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut L) := MulEquiv.finite_left
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hAut : Nat.card (MulAut L) = Nat.card (Outer L) * Nat.card (inner L) :=
    (inner L).card_eq_card_quotient_mul_card_subgroup
  have hInn : Nat.card (inner L) ∣ Nat.card L := Subgroup.card_range_dvd _
  have hdvd : Nat.card S ∣ 3 ^ 5 * (Nat.card (Outer L) * 206720) := by
    refine (Subgroup.card_subgroup_dvd_card S).trans ?_
    rw [hAut]
    refine (Nat.mul_dvd_mul_left _ hInn).trans ?_
    rw [hcard]
    exact ⟨1, by ring⟩
  have hpos : 0 < Nat.card (Outer L) := Nat.card_pos
  have hcop : Nat.Coprime 3 (Nat.card (Outer L) * 206720) := by
    obtain h1 | h2 : Nat.card (Outer L) = 1 ∨ Nat.card (Outer L) = 2 := by omega
    · rw [h1]
      norm_num
    · rw [h2]
      norm_num
  rw [hk] at hdvd ⊢
  exact (Nat.Coprime.pow_left k hcop).dvd_of_dvd_mul_right hdvd

theorem isSolvable_of_card_le_two_of_finite {A : Type*} [Group A] [Finite A]
    (h : Nat.card A ≤ 2) : Group.IsSolvable A := by
  have h0 : 0 < Nat.card A := Nat.card_pos
  obtain h1 | h2 : Nat.card A = 1 ∨ Nat.card A = 2 := by omega
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp h1).1
    infer_instance
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic A := isCyclic_of_prime_card h2
    exact Group.isSolvable_of_comm fun a b => (IsCyclic.isMulCommutative.is_comm).comm a b

theorem kFactJ3OuterRank_of
    (hbr : Nonempty (NativeSporadic.Carrier .J3 ≃* (TauCeti.CFSGIndex.sporadic .J3).Group))
    (hOut : Nat.card (Outer NativeSporadic.J3) ≤ 2)
    (hrank : CFSG.pRank 3 NativeSporadic.J3 = 3) : KFactJ3OuterRank := by
  intro J _ _ ⟨e⟩
  obtain ⟨b⟩ := hbr
  let f := e.trans b.symm
  have : Finite NativeSporadic.J3 := Finite.of_equiv J f.toEquiv
  refine ⟨CFSG.Sporadic.Schreier.outer_card_le_of_equiv hOut f, ?_⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (G' := NativeSporadic.J3) (p := 3)
    (by norm_num) f, ← CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact hrank

theorem kFactJ3OuterRank_closed
    (hbr : Nonempty (NativeSporadic.Carrier .J3 ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) :
    KFactJ3OuterRank :=
  kFactJ3OuterRank_of hbr
    (CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.j3_outer_card_le
      CFSG.Sporadic.Schreier.j3PermEquiv)
    CFSG.RankThree.Asc83Table.J3.native_J3.1

theorem stmtJ3Target_of
    (hbr : Nonempty (NativeSporadic.Carrier .J3 ≃* (TauCeti.CFSGIndex.sporadic .J3).Group))
    (hOR : KFactJ3OuterRank) : StmtJ3Target ∧ StmtJ3TargetCard := by
  have key : ∀ (L : Type) [Group L] [Finite L],
      Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) →
        JStarTarget 3 (3 ^ 5) L ∧ JStarTargetCard 3 5 (3 ^ 5) L := by
    intro L _ _ he
    obtain ⟨e⟩ := he
    obtain ⟨b⟩ := hbr
    let f := e.trans b.symm
    have := CFSG.Sporadic.J3.isSimpleGroup_J3
    have hsimple : IsSimpleGroup L := MulEquiv.isSimpleGroup (H := NativeSporadic.J3) f
    have hcard : Nat.card L = 50232960 := by
      rw [Nat.card_congr f.toEquiv]
      exact CFSG.Sporadic.J3.card_J3
    obtain ⟨hOut, hrank⟩ := hOR L ⟨e⟩
    have : Finite (MulAut L) := MulEquiv.finite_left
    refine ⟨⟨hsimple, nonabelian_of_card_eq hcard, hrank.ge,
      isSolvable_of_card_le_two_of_finite hOut, ⟨19, by norm_num, by norm_num, ?_, ?_⟩⟩,
      ⟨card_sylow_three_of_card_eq hcard, card_dvd_of_isPGroup_mulAut hcard hOut⟩⟩
    · rw [hcard]
      norm_num
    · intro k hk hkB
      have hk5 : k ≤ 5 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hkB
      interval_cases k <;> norm_num
  exact ⟨fun L _ _ he => (key L he).1, fun L _ _ he => (key L he).2⟩

end CFSG.AGLEmbedding
