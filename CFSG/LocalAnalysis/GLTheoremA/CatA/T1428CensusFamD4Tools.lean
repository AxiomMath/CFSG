module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamCQ
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsFine
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.CatDistinct CFSG.HardMathSupport.Solomon.Coordinator.LieComp

@[expose] def NotL2 (r : ℕ) (X : Type) [Group X] : Prop :=
  ¬ catalogIs (X ⧸ Subgroup.center X) (S10.isL2n r)

theorem isComponentProperty_notL2 (r : ℕ) : IsComponentProperty (NotL2 r) where
  of_mulEquiv := fun {X Y} _ _ e h => by
    intro hY
    exact (show ¬ catalogIs (X ⧸ Subgroup.center X) (S10.isL2n r) from h)
      ((catalogIs_congr (QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e
        (Subgroup.map_center_eq e))).2 hY)

theorem false_of_SL_three_centerQuot_isL2n {E : Type} [Field E] [Finite E] {e : ℕ} (he : 1 ≤ e)
    (hE : Nat.card E = 2 ^ e) (hperf : commutator (Matrix.SpecialLinearGroup (Fin 3) E) = ⊤)
    {T : Type} [Group T] [Finite T] (g : Matrix.SpecialLinearGroup (Fin 3) E →* T)
    (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) E)) {r : ℕ} (hr : Odd r)
    (hL : catalogIs (T ⧸ Subgroup.center T) (S10.isL2n r)) : False := by
  have hform := card_centerQuot_mul_gcd_SL (by norm_num : 2 ≤ 3) hperf g hg hker
  have h2 := catalogIs_isL2n_card_of_odd hr hL
  rw [h2, hE] at hform
  have h3 : (3 : ℕ) * (3 - 1) / 2 = 3 := by norm_num
  have hIcc : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  rw [h3, hIcc, Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)] at hform
  have hodd2 : Odd ((2 ^ r) ^ 2 - 1) := odd_pow_two_pow_sub_one hr.pos (by norm_num)
  have hG : Odd (Nat.gcd 3 (2 ^ e - 1)) :=
    Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left _ _)
  have hB : Odd (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1)) :=
    (odd_pow_two_pow_sub_one he (by norm_num)).mul (odd_pow_two_pow_sub_one he (by norm_num))
  have hform' : 2 ^ r * (((2 ^ r) ^ 2 - 1) * Nat.gcd 3 (2 ^ e - 1)) =
      2 ^ (e * 3) * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1)) := by
    rw [pow_mul, ← mul_assoc]
    exact hform
  obtain ⟨hre, hAB⟩ := two_pow_mul_odd_inj (hodd2.mul hG) hB hform'
  have ha : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hGpos : 1 ≤ Nat.gcd 3 (2 ^ e - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h2r : (2 ^ r) = (2 ^ e) ^ 3 := by rw [hre, pow_mul]
  rw [h2r] at hAB
  generalize 2 ^ e = a at *
  generalize Nat.gcd 3 (a - 1) = G at *
  have hb1 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hc1 : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hbc : a ^ 2 ≤ a ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hc8 : 8 ≤ a ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ a ^ 3 := Nat.pow_le_pow_left ha 3
  have hc2 : 1 ≤ (a ^ 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hlow : (a ^ 3) ^ 2 - 1 ≤ ((a ^ 3) ^ 2 - 1) * G := Nat.le_mul_of_pos_right _ hGpos
  have hhi : (a ^ 2 - 1) * (a ^ 3 - 1) < (a ^ 3) ^ 2 - 1 := by
    generalize a ^ 2 = b at *
    generalize a ^ 3 = c at *
    zify [hb1, hc1, hc2]
    nlinarith
  omega

end CFSG.LocalAnalysis.GLTheoremA.T1428
