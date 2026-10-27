module

public import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.Assembly.OpenBridges
import CFSG.RankThree.PartTwo.Census.Exceptional.E6Two
import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open TauCeti
  CFSG.RankThree.PartTwo.Census.Exceptional CFSG.TauCetiBridge

@[expose] def LargeExceptionalTwoCase (G : Type) [Group G] : Prop :=
  ∃ (t : StatedLieTag) (f : ℕ),
    (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨ (t = .F4 ∧ 2 ≤ f)) ∧
      ChevalleyExceptionalModel G t 2 f

section Certified

set_option linter.unusedSectionVars false


variable {G : Type} [Group G] [Finite G]

theorem four_le_twoLocalOddRank_E6_model {f : ℕ} (h : ChevalleyExceptionalModel G .E6 2 f) :
    4 ≤ CFSG.twoLocalOddRank G := by
  obtain ⟨hadm, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
  let q : PrimePower := ⟨2, f, Nat.prime_two, hadm.2.1⟩
  have hv : (LieTypeIndex.E6 q).Valid := by simp
  obtain ⟨b⟩ := Even.chevalleyBridgesAll.e6 q hv K (by rw [hK, PrimePower.card_def q])
  have : Finite (ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) := Finite.of_equiv G (e.trans b).toEquiv
  rw [CFSG.RankThree.PartOne.Census3.twoLocalOddRank_eq_of_mulEquiv (e.trans b)]
  exact four_le_twoLocalOddRank_E6 q hv

theorem four_le_twoLocalOddRank_E7_model {f : ℕ} (h : ChevalleyExceptionalModel G .E7 2 f) :
    4 ≤ CFSG.twoLocalOddRank G := by
  obtain ⟨hadm, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
  let q : PrimePower := ⟨2, f, Nat.prime_two, hadm.2.1⟩
  have hv : (LieTypeIndex.E7 q).Valid := by simp
  obtain ⟨b⟩ := Even.chevalleyBridgesAll.e7 q hv K (by rw [hK, PrimePower.card_def q])
  have : Finite (ValidLieTypeIndex.Group ⟨.E7 q, hv⟩) := Finite.of_equiv G (e.trans b).toEquiv
  rw [CFSG.RankThree.PartOne.Census3.twoLocalOddRank_eq_of_mulEquiv (e.trans b)]
  exact four_le_twoLocalOddRank_E7 q hv

theorem four_le_twoLocalOddRank_E8_model {f : ℕ} (h : ChevalleyExceptionalModel G .E8 2 f) :
    4 ≤ CFSG.twoLocalOddRank G := by
  obtain ⟨hadm, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
  let q : PrimePower := ⟨2, f, Nat.prime_two, hadm.2.1⟩
  have hv : (LieTypeIndex.E8 q).Valid := by simp
  obtain ⟨b⟩ := Even.chevalleyBridgesAll.e8 q hv K (by rw [hK, PrimePower.card_def q])
  have : Finite (ValidLieTypeIndex.Group ⟨.E8 q, hv⟩) := Finite.of_equiv G (e.trans b).toEquiv
  rw [CFSG.RankThree.PartOne.Census3.twoLocalOddRank_eq_of_mulEquiv (e.trans b)]
  exact four_le_twoLocalOddRank_E8 q hv

theorem four_le_twoLocalOddRank_F4_model {f : ℕ} (hf2 : 2 ≤ f)
    (h : ChevalleyExceptionalModel G .F4 2 f) : 4 ≤ CFSG.twoLocalOddRank G := by
  obtain ⟨hadm, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
  let q : PrimePower := ⟨2, f, Nat.prime_two, hadm.2.1⟩
  have hv : (LieTypeIndex.F4 q).Valid := by simp
  obtain ⟨b⟩ := Even.chevalleyBridgesAll.f4 q hv K (by rw [hK, PrimePower.card_def q])
  have : Finite (ValidLieTypeIndex.Group ⟨.F4 q, hv⟩) := Finite.of_equiv G (e.trans b).toEquiv
  rw [CFSG.RankThree.PartOne.Census3.twoLocalOddRank_eq_of_mulEquiv (e.trans b)]
  exact four_le_twoLocalOddRank_F4 q hv (by simp only [q]; omega)

theorem four_le_twoLocalOddRank_twistedE6_model {f : ℕ}
    (h : ChevalleyExceptionalModel G .twistedE6 2 f) : 4 ≤ CFSG.twoLocalOddRank G := by
  obtain ⟨hadm, hm⟩ := h
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
  let q : PrimePower := ⟨2, f, Nat.prime_two, hadm.2.1⟩
  have hv : (LieTypeIndex.twistedE6 q).Valid := by simp
  obtain ⟨b⟩ := Even.chevalleyBridgesAll.twistedE6 q hv K (by rw [hK, PrimePower.card_def q]) σ
    (fun x => by rw [PrimePower.card_def q]; exact hσ x)
  have : Finite (ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :=
    Finite.of_equiv G (e.trans b).toEquiv
  rw [CFSG.RankThree.PartOne.Census3.twoLocalOddRank_eq_of_mulEquiv (e.trans b)]
  exact four_le_twoLocalOddRank_twistedE6 q hv

theorem four_le_twoLocalOddRank_of_largeExceptionalTwoCase (h : LargeExceptionalTwoCase G) :
    4 ≤ CFSG.twoLocalOddRank G := by
  obtain ⟨t, f, ht, hm⟩ := h
  rcases ht with rfl | rfl | rfl | rfl | ⟨rfl, hf⟩
  · exact four_le_twoLocalOddRank_E6_model hm
  · exact four_le_twoLocalOddRank_E7_model hm
  · exact four_le_twoLocalOddRank_E8_model hm
  · exact four_le_twoLocalOddRank_twistedE6_model hm
  · exact four_le_twoLocalOddRank_F4_model hf hm

theorem not_standing_of_largeExceptionalTwoCase (hS : Standing G)
    (h : LargeExceptionalTwoCase G) : False := by
  have h4 := four_le_twoLocalOddRank_of_largeExceptionalTwoCase h
  have h3 := hS.rank
  rw [← CFSG.Assembly.evenRank_eq_open,
    CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h3
  omega

end Certified

end CFSG.LocalAnalysis.RankThreeUC
