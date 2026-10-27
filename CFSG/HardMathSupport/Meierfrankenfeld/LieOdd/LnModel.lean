module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsOdd
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Assembly.LowTwoRank TauCeti
open scoped MatrixGroups

theorem exists_psln_model_of_lie_A {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.A r q, hv⟩).Group) (hp : q.p ≠ 2)
    (hr : 2 ≤ r) :
    Nat.card (Subgroup.center L) ∣ Nat.gcd (r + 1) (q.p ^ q.exponent - 1) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.p ^ q.exponent ∧
        Nonempty (L ⧸ Subgroup.center L ≃*
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (r + 1) K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hmod := CFSG.HardMathSupport.Cooperstein.Coordinator.statedClassicalModel_PSL_of_lieA hv e
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hmod
  have : Fintype K := Fintype.ofFinite K
  let e'' : L ⧸ Subgroup.center L ≃* PSL(r + 1, K) :=
    e'.trans (projectiveSpecialLinearGroupEquivStatedProj (r + 1) K).symm
  have hp3 : 3 ≤ q.p := by
    have := q.prime_p.two_le
    omega
  have hq3 : 3 ≤ q.p ^ q.exponent :=
    hp3.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  have hcard : Fintype.card K = q.p ^ q.exponent := by
    rw [Fintype.card_eq_nat_card, hK]
  have hodd : Odd (q.p ^ q.exponent) := (q.prime_p.eq_two_or_odd'.resolve_left hp).pow
  have h4 : q.p ^ q.exponent ≠ 4 := by
    intro h
    rw [h] at hodd
    exact absurd hodd (by decide)
  obtain ⟨-, ⟨φ⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_three_le
    (k := K) (n := r + 1) (by omega) (by rw [hcard]; exact hq3)
    (by rw [hcard]; exact fun h => h4 h.2)
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e''
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier PSL(r + 1, K)) =
      Nat.gcd (r + 1) (q.p ^ q.exponent - 1) := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd, hcard, Nat.card_zmod]
  refine ⟨hM ▸ hdvd, K, inferInstance, inferInstance, hK, ⟨e''.trans ?_⟩⟩
  exact QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center (r + 1) K).symm

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
