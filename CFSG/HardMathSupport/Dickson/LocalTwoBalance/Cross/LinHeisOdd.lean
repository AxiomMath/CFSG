module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisFinal

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCLinPlane
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm

theorem linHeisenbergBalanceOdd_holds :
    ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 3 ≤ n → ∀ p : ℕ, p.Prime → p ≠ 2 →
      p ∣ Nat.card F - 1 → n ≠ p → ∀ A B : GL (Fin n) F, ¬ (A * B = B * A) →
        conjAut n F A * conjAut n F B = conjAut n F B * conjAut n F A →
        conjAut n F A ^ p = 1 → conjAut n F B ^ p = 1 →
        ∀ H : Subgroup (MulAut (projectiveSL n F)), innerAut (projectiveSL n F) ≤ H →
          localDeltaIn p H (Subgroup.closure {conjAut n F A, conjAut n F B}) = ⊥ := by
  intro n F _ _ hn p hp hp2 hpq hnp A B hAB hcomm hAp hBp H hH
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨z, hz⟩ := exists_comm_scalar hn hcomm
  obtain ⟨a, ha⟩ := exists_pow_scalar hn hAp
  obtain ⟨b, hb⟩ := exists_pow_scalar hn hBp
  have hzp : z ^ p = 1 := comm_scalar_pow_eq_one hn hz hb
  have hz1 : z ≠ 1 := by
    intro h
    apply hAB
    rw [hz, h, map_one, one_mul]
  obtain ⟨S, T, c, w, hS, hT, hST, hwp, hw1, hSD, hTD⟩ := exists_split_pair hn hp hp2 hz hzp hz1 ha hb
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hpF : ¬ p ∣ Nat.card F := by
    intro hd
    have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hd hpq
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpK : (p : F) ≠ 0 := natCast_ne_zero_of_not_dvd_card hp hpF
  have hF4 : 3 < Nat.card F := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  have hwF : (w : F) ^ p = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hwp
    simpa using this
  have hw1F : (w : F) ≠ 1 := fun h => hw1 (Units.ext h)
  have hωprim : IsPrimitiveRoot (w : F) p := IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hwF hw1F)
  obtain ⟨hS1, hT1⟩ := conjAut_ne_one_of_comm_scalar hn hST hw1
  refine eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 ?_
  set 𝒢 : Subgroup (SpecialLinearGroup (Fin n) F) := (fixSub g).comap (proj n F) with h𝒢
  have hSb : ∀ (hsq : Squarefree (minpoly F (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F))))
      (h : primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F))), GoodBlock h →
      blockImage hsq h ≤ 𝒢.map SpecialLinearGroup.toGL := fun hsq h hgood =>
    blockImage_le_map_fixSub hn hp hp2 rfl hH hg hSD hS1 hgood hωprim
  have hTb : ∀ (hsq : Squarefree (minpoly F (Matrix.toLin' (T : Matrix (Fin n) (Fin n) F))))
      (h : primaryFactors (Matrix.toLin' (T : Matrix (Fin n) (Fin n) F))), GoodBlock h →
      blockImage hsq h ≤ 𝒢.map SpecialLinearGroup.toGL := fun hsq h hgood =>
    blockImage_le_map_fixSub hn hp hp2 rfl hH hg hTD hT1 hgood hωprim
  have htop : 𝒢 = ⊤ := heis_eq_top hp hp2 hωprim hpK hF4 (by omega) hnp hS hT (toLin'_rel hST) 𝒢
    hSb hTb
  exact eq_one_of_comap_fixSub_eq_top htop

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
