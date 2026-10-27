module

public import CFSG.RankThree.PartOne.KS.J2
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.LinesGood
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Open CFSG.RankThree.PartOne CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint

theorem j2Five_noSig :
    ∀ Ê : Subgroup (MulAut ↥j2P), IsElemAbelian 5 Ê → Nat.card Ê = 5 ^ 2 → NoSig 5 Ê := by
  obtain ⟨⟨hQP, hQcomm, -, hQcard, hsyl⟩, hlines, hrec, hrec50, hrec300⟩ :=
    R3E_J2_full_five_centralizer_structure
  have hgood : ∀ i : Fin 6,
      PrimePowOK 5 (Nat.card (j2R ⊓ centralizer ({j2FiveLine i} : Set (Equiv.Perm (Fin 315))) :
        Subgroup (Equiv.Perm (Fin 315)))) := by
    intro i
    rw [← (hrec i).1]
    by_cases hi0 : i.val = 0 ∨ i.val = 1 ∨ i.val = 4
    · rw [(hrec50 i hi0).1]
      exact primePowOK_five_50
    · have hi1 : i.val = 2 ∨ i.val = 3 ∨ i.val = 5 := by
        have := i.2
        omega
      rw [(hrec300 i hi1).1]
      exact primePowOK_five_300
  refine noSig_planes_of_autModel j2_autModel j2_card_le Nat.prime_five (by norm_num) hsyl ?_
    (good_of_lines Nat.prime_five j2_autModel.le hsyl hlines.1
      (fun j => ⟨j, ⟨1, j2R.one_mem, by simp⟩, hgood j⟩))
  ·
    intro E hEQ hEel hEcard
    have hEQ' : E = j2FiveQ :=
      Subgroup.eq_of_le_of_card_ge hEQ (by rw [hEcard, hQcard]; norm_num)
    subst hEQ'
    obtain ⟨hC0, hQC0, hQeq0, -⟩ := hrec 0
    refine PFree.of_isPGroup (j2FiveQ_isPGroup.to_le ?_)
    intro x hx
    have hxC0 : x ∈ j2FiveC ((0 : Fin 6) : ℕ) := by
      rw [hC0]
      exact ⟨hx.1, Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_iff.1 hx.2 _ (j2FiveLine_mem_Q 0)⟩
    have : x ∈ centralizer (j2FiveQ : Set _) ⊓ j2FiveC ((0 : Fin 6) : ℕ) := ⟨hx.2, hxC0⟩
    rw [hQeq0] at this
    exact this

theorem sporPlaneKill_J2_five
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .J2 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b₀ : NativeSporadic.J2 ≃* Spor .J2 := b
  exact sporPlaneKill_of_noSig_model hOut Nat.prime_five (by norm_num) (by decide)
    (j2PermEquiv.symm.trans b₀)
    (fun R Y hR hR9 hY3 hRY => j2Five_noSig R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hY3) hRY) b₀ offPair_J2

theorem sporPair_J2_five
    (hOut : SporadicOuterLeTwo) : SporPair .J2 5 :=
  sporPair_of_planeKill (sporPlaneKill_J2_five hOut)

end CFSG.HardMathSupport.Dickson.I271
