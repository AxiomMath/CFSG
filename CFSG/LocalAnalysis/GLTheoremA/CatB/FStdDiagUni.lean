module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagUniData
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagUniLift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagUniOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsUniBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsUniLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamUni)
open CFSG.LocalAnalysis.GLTheoremA.K1419
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU nonempty_quotientCenter_equiv_statedProj)

theorem fstdUni_center_bot {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    {I : Subgroup G} {M : Subgroup H} (hle : Nat.card ↥I ≤ Nat.card ↥M)
    (hq : Nat.card (↥I ⧸ Subgroup.center ↥I) = Nat.card (↥M ⧸ Subgroup.center ↥M))
    (hM : Subgroup.center ↥M = ⊥) : Subgroup.center ↥I = ⊥ := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥I)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥M)
  have hMz : Nat.card ↥(Subgroup.center ↥M) = 1 := by
    rw [hM]
    exact Subgroup.card_bot
  rw [hMz, mul_one] at h2
  have hpos : 0 < Nat.card (↥I ⧸ Subgroup.center ↥I) := Nat.card_pos
  have hz0 : 0 < Nat.card ↥(Subgroup.center ↥I) := Nat.card_pos
  have hz : Nat.card ↥(Subgroup.center ↥I) = 1 := by
    by_contra hne
    have hgt : 1 < Nat.card ↥(Subgroup.center ↥I) := by omega
    have := Nat.mul_lt_mul_of_pos_left hgt hpos
    omega
  exact Subgroup.eq_bot_of_card_eq _ hz

theorem smallFam_uni : SmallFam FamUni := by
  intro S _ _ labK α I hFam hcen hα3 hα1 hin hI hsmall
  have hI3 := fstdLin_glaPComponent hI hsmall
  obtain ⟨K, hK, hKf, k, d, τ, hτ, A, u, J', hτQ, hKcard, hd, hdQ, hA, hu, hpow, hAns, hJ',
    ⟨ePQ⟩, hJcard⟩ := fstdUniData hcen hFam hα3 hα1 hin hI3
  obtain ⟨hA3, -⟩ := k1419ClsUniLift hτ hτQ hKcard hd hdQ A hA u hu hpow J' hJ'
  obtain ⟨M, hM, ⟨ePS⟩, hMcard⟩ := fstdUniLift hτ hτQ hKcard hd A hA hA3 u hu J' hJ'
  obtain ⟨c, hc⟩ := hA3
  have h2 : (2 : K) = 0 := Y10GInnUni.two_eq_zero_of_card (K := K) (n := k) hKcard
  have hodd : Odd (orderOf A) :=
    Y10GInnLin.odd_orderOf_of_pow_scalar h2 (by omega : 1 ≤ d) A (by norm_num : Odd 3) hc
  have hord : ((orderOf A : ℕ) : K) ≠ 0 := Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd
  have hMgu := Y10GInnUni.isComponentOf_centralizer_gu_of_su hτ A hM
  obtain ⟨_, _, _, _, _, htype⟩ := k1419ClsUniBlock hτ hτQ hKcard A hA hord M hMgu
  obtain ⟨eI⟩ := fstdLin_pSimple_equiv hI.2.2 hsmall
  have eIM : (↥I ⧸ Subgroup.center ↥I) ≃* (↥M ⧸ Subgroup.center ↥M) :=
    eI.symm.trans ((QuotientGroup.congr _ _ ePQ (Subgroup.map_center_eq ePQ)).trans ePS)
  have hqcard : Nat.card (↥I ⧸ Subgroup.center ↥I) = Nat.card (↥M ⧸ Subgroup.center ↥M) :=
    Nat.card_congr eIM.toEquiv
  have hIM : Nat.card ↥I ≤ Nat.card ↥M := by
    rw [← hJcard]
    exact hMcard
  rcases htype with ⟨a, dd, E, hEf, hEfin, τ', hτ', P, ha2, hτ'Q, hEcard, ⟨eM⟩, -⟩ |
      ⟨b, e, E, hEf, hEfin, X, Y, P, P', hb2, hEcard, ⟨eM⟩, -⟩
  ·
    have hτ'm : ∀ x : E, τ' x = x ^ 2 ^ (k * dd) := by
      intro x
      rw [pow_mul]
      exact hτ'Q x
    have hEm : Nat.card E = (2 ^ (k * dd)) ^ 2 := by
      rw [pow_mul]
      exact hEcard
    have eMq : (↥M ⧸ Subgroup.center ↥M) ≃*
        (↥(heldSU a E τ' hτ') ⧸ Subgroup.center ↥(heldSU a E τ' hτ')) :=
      QuotientGroup.congr _ _ eM (Subgroup.map_center_eq eM)
    have hcardMq := Nat.card_congr eMq.toEquiv
    have hsm : Nat.card (↥(heldSU a E τ' hτ') ⧸ Subgroup.center ↥(heldSU a E τ' hτ')) = 25920 ∨
        Nat.card (↥(heldSU a E τ' hτ') ⧸ Subgroup.center ↥(heldSU a E τ' hτ')) = 360 := by
      rw [← hcardMq, ← hqcard]
      exact hsmall
    obtain ⟨hZ, hq25⟩ := fstdUni_block τ' hτ' ha2 hτ'm hEm hsm
    have hZM : Subgroup.center ↥M = ⊥ := by
      have hcz : Nat.card ↥(Subgroup.center ↥M) =
          Nat.card ↥(Subgroup.center ↥(heldSU a E τ' hτ')) :=
        Nat.card_congr (Subgroup.centerCongr eM).toEquiv
      rw [hZ, Subgroup.card_bot] at hcz
      exact Subgroup.eq_bot_of_card_eq _ hcz
    refine ⟨fstdUni_center_bot hIM hqcard hZM, fun h360 => ?_⟩
    have h25 : Nat.card (↥I ⧸ Subgroup.center ↥I) = 25920 := by
      rw [hqcard, hcardMq]
      exact hq25
    omega
  ·
    exfalso
    have hEcard' : Nat.card E = 2 ^ (k * (2 * e)) := by
      rw [pow_mul]
      exact hEcard
    obtain ⟨eψ⟩ := nonempty_quotientCenter_equiv_statedProj eM
    obtain ⟨h1, h2'⟩ := fstdLin_card_psl_ne hb2 hEcard'
    have hc := Nat.card_congr eψ.toEquiv
    rcases hsmall with h | h
    · exact h1 (hc.symm.trans (hqcard.symm.trans h))
    · exact h2' (hc.symm.trans (hqcard.symm.trans h))

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
