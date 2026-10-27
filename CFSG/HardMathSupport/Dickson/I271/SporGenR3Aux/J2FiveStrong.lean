module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.NoSigStrong
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.J2Five

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Yardstones.Md0ec50421ce4
open Subgroup CFSG.RankThree.PartOne CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.RankThree.PartTwo.Sec4

section J2


theorem sporStrong_J2_five (hOut : SporadicOuterLeTwo) : SporStrong .J2 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b₀ : NativeSporadic.J2 ≃* Spor .J2 := b
  exact sporStrong_of_noSig_model hOut Nat.prime_five (by norm_num) (by decide)
    (j2PermEquiv.symm.trans b₀)
    (fun R Y hR hR9 hY3 hRY => j2Five_noSig R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hY3) hRY) b₀ offPair_J2

theorem coprime_five_of_le_two {n : ℕ} (h : n ≤ 2) (hpos : 0 < n) : Nat.Coprime 5 n := by
  interval_cases n <;> norm_num

theorem j2P_elemAbelian_twentyfive :
    ∃ E₀ : Subgroup ↥j2P, IsElemAbelian 5 E₀ ∧ Nat.card E₀ = 5 ^ 2 := by
  obtain ⟨⟨hQP, hQcomm, hQexp, hQcard, -⟩, -⟩ := R3E_J2_full_five_centralizer_structure
  refine ⟨j2FiveQ.subgroupOf j2P, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · exact Subtype.ext (Subtype.ext (hQcomm _ x.2 _ y.2))
  · have h1 := Monoid.pow_exponent_eq_one (⟨(x : Equiv.Perm (Fin 315)), hx⟩ : ↥j2FiveQ)
    rw [hQexp] at h1
    have h2 : ((x : Equiv.Perm (Fin 315))) ^ 5 = 1 := congrArg Subtype.val h1
    exact Subtype.ext (by simpa using h2)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQcard]
    norm_num

theorem rkAut_j2P_five (hOut : SporadicOuterLeTwo) : RkAut 5 ↥j2P := by
  have hsimple : IsSimpleGroup NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hfin : Finite NativeSporadic.J2 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.J2.card_J2]; norm_num)
  have g : ↥j2P ≃* NativeSporadic.J2 := j2PermEquiv.symm
  haveI : Finite ↥j2P := Finite.of_equiv _ g.symm.toEquiv
  have hsimpleP : IsSimpleGroup ↥j2P := g.isSimpleGroup_congr.2 hsimple
  have hnabP : ∃ a c : ↥j2P, a * c ≠ c * a := by
    by_contra hc
    push Not at hc
    letI : CommGroup ↥j2P := { (inferInstance : Group ↥j2P) with mul_comm := hc }
    have hp := IsSimpleGroup.prime_card (α := ↥j2P)
    rw [Nat.card_congr g.toEquiv, CFSG.Sporadic.J2.card_J2] at hp
    norm_num at hp
  have hZP : Subgroup.center ↥j2P = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥j2P) with h | h
    · exact h
    · exfalso
      obtain ⟨a, c, hac⟩ := hnabP
      exact hac (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top c) a)
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b₀ : NativeSporadic.J2 ≃* Spor .J2 := b
  have hoP : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥j2P) ≤ 2 :=
    hOut _ hsimpleP hnabP .J2 ⟨g.trans b₀⟩
  exact rkAut_of_simple Nat.prime_five hZP (coprime_five_of_le_two hoP Nat.card_pos)
    j2P_elemAbelian_twentyfive

theorem rkAut_J2_five (hOut : SporadicOuterLeTwo) {T : Type} [Group T]
    (e : T ≃* NativeSporadic.Carrier .J2) : RkAut 5 T :=
  rkAut_of_equiv (j2PermEquiv.symm.trans e.symm) (rkAut_j2P_five hOut)

end J2

end CFSG.HardMathSupport.Dickson.I271
