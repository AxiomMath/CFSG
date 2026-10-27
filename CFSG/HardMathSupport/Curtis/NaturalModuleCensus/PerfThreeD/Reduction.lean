module

public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeLinear
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.Model
import CFSG.LargeExtraspecial.DW2AOutOrth
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Curtis.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def IdxD8 : TauCeti.LieTypeIndex → Prop
  | .D r q => r = 4 ∧ q.p = 2 ∧ q.card = 2
  | _ => False

@[expose] def FixPerfThreeTrialityD : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (u : Y), FixPerfThreeHyp L J u →
    u ∉ L ⊔ Subgroup.centralizer (L : Set Y) → IsLieOf IdxD8 (↥L ⧸ Subgroup.center ↥L) → False

theorem isClassicalOrG2Index_of_idxD {i : TauCeti.LieTypeIndex} (h : IdxD i) :
    IsClassicalOrG2Index i := by
  cases i <;> first | exact h | exact h.elim

theorem false_of_perfThreeCent {Y : Type} [Group Y] {L J : Subgroup Y}
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {l : ↥L} (hlfix : ∀ g : ↥L, g * l = l * g → g ∈ J.subgroupOf L)
    (h : PerfThreeCent (QuotientGroup.mk' (Subgroup.center ↥L) l)) : False := by
  obtain ⟨P, hPc, hPp, hP3⟩ := h
  obtain ⟨W, hW, hWc, hPW⟩ := exists_perfect_centralizer_dvd_of_central_quotient
    (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _).le hPp hPc
  have hWJ : W ≤ J.subgroupOf L := fun w hw =>
    hlfix w ((Subgroup.mem_centralizer_iff.1 (hWc hw) l (Set.mem_singleton _)).symm)
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (coprime_card_of_perf_subgroupOf hperf W hWJ hW) (hP3.trans hPW)

section Core


theorem exists_model_of_fixPerfThreeHyp_idxD {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    {u : Y} (h : FixPerfThreeHyp L J u) (hX : IsLieOf IdxD (↥L ⧸ Subgroup.center ↥L)) :
    ∃ r : ℕ, 4 ≤ r ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus r 2 1 ∧
      (r = 4 → IsLieOf IdxD8 (↥L ⧸ Subgroup.center ↥L)) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  have hidx2 := isClassicalOrG2IndexTwo_of_fixPerfThreeHyp h ⟨d, hv⟩
    (isClassicalOrG2Index_of_idxD hd) e
  cases d
  case D r q =>
    have hp2 : q.p = 2 := hd
    have hcard : q.card = 2 := hidx2
    have hexp : q.exponent = 1 := by
      have hpos := q.exponent_pos
      by_contra hne
      have h2 : 2 ≤ q.exponent := by omega
      have : 2 ^ 2 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
      rw [TauCeti.PrimePower.card_def, hp2] at hcard
      omega
    have hr : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp2 e
    rw [hp2, hexp] at hmodel
    refine ⟨r, hr, hmodel, fun hr4 => ?_⟩
    exact ⟨⟨_, hv⟩, ⟨hr4, hp2, hidx2⟩, ⟨e⟩⟩
  all_goals exact hd.elim

end Core

theorem mem_sup_centralizer_of_model_pomegaPlus {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hq : Group.IsPerfect ↥L) {r : ℕ} (hr : 5 ≤ r)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus r 2 1) {u : Y}
    (hnorm : u ∈ Subgroup.normalizer (L : Set Y)) (hpow : u ^ 3 = 1) :
    u ∈ L ⊔ Subgroup.centralizer (L : Set Y) := by
  have hLie : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus r 2 1 :=
    Or.inl ⟨by decide, hmodel⟩
  have h2 := CFSG.LargeExtraspecial.DW.isPGroup_outer_POmegaPlus hr hLie
  have hout : ¬ 3 ∣ Nat.card (Outer ↥L) := fun h3 => by
    have h3' := h3.trans (card_outer_dvd_card_outer_centerQuotient ↥L)
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    rw [hn] at h3'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3'
    omega
  exact mem_sup_centralizer_of_not_dvd_card_outer (p := 3) (k := 1) Nat.prime_three hout hnorm
    (by simpa using hpow)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
