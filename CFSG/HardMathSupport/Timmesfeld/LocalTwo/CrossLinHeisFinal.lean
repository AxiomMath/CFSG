module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisPair

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCLinPlane
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm

theorem conjAut_ne_one_of_comm_scalar {n : ℕ} {F : Type} [Field F] [Finite F] (hn : 3 ≤ n)
    {X Y : GL (Fin n) F} {w : Fˣ} (h : X * Y = GeneralLinearGroup.scalar (Fin n) w * (Y * X))
    (hw : w ≠ 1) : conjAut n F X ≠ 1 ∧ conjAut n F Y ≠ 1 := by
  have key : ∀ {U V : GL (Fin n) F} {w : Fˣ},
      U * V = GeneralLinearGroup.scalar (Fin n) w * (V * U) → w ≠ 1 → conjAut n F U ≠ 1 := by
    intro U V w h hw hU
    obtain ⟨s, hs⟩ := eq_scalar_of_conjAut_eq_one hn hU
    apply hw
    have h1 : U * V = V * U := by
      rw [← hs]
      exact GeneralLinearGroup.scalar_commute s V
    rw [h1] at h
    have h2 : GeneralLinearGroup.scalar (Fin n) w = 1 := by
      have := mul_right_cancel (a := GeneralLinearGroup.scalar (Fin n) w) (b := V * U)
        (c := 1) (by rw [one_mul]; exact h.symm)
      exact this
    exact (scalar_eq_one_iff (by omega)).1 h2
  refine ⟨key h hw, key (U := Y) (V := X) (w := w⁻¹) ?_ (by simpa using hw)⟩
  rw [map_inv, h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem linHeisenbergBalance_holds : LinHeisenbergBalance := by
  intro n F _ _ hn p hp hp5 hpq hnp A B hAB hcomm hAp hBp H hH
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
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

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
