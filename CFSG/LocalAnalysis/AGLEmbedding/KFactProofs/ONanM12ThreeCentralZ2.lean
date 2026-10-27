module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanThreeCentralZ2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12HeisData

public section

namespace CFSG.AGLEmbedding.KFactProofs.M12Z2

open CFSG.Blueprint CFSG.CGT.PushingUpLit.CGT6M CFSG.Sporadic.Bridge

set_option maxRecDepth 100000 in
theorem m12HeisA_eq_word : wordProd m12Gen m12HeisWordA = m12HeisA := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12HeisB_eq_word : wordProd m12Gen m12HeisWordB = m12HeisB := by decide +kernel

theorem m12HeisA_mem : m12HeisA ∈ NativeSporadic.M12 :=
  m12HeisA_eq_word ▸ wordProd_mem m12Gen_mem _

theorem m12HeisB_mem : m12HeisB ∈ NativeSporadic.M12 :=
  m12HeisB_eq_word ▸ wordProd_mem m12Gen_mem _

theorem m12HeisH_mem : m12HeisH ∈ NativeSporadic.M12 := wordProd_mem m12Gen_mem _

set_option maxRecDepth 100000 in
theorem m12Heis_pow_three : m12HeisA ^ 3 = 1 ∧ m12HeisB ^ 3 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12Heis_not_comm : m12HeisA * m12HeisB ≠ m12HeisB * m12HeisA := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12Heis_conj : m12HeisC * m12HeisH = m12HeisH * m12HeisA := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12Heis_nodup : (heisList m12HeisA m12HeisB m12HeisC).Nodup := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12Heis_stable_bool :
    ((heisList m12HeisA m12HeisB m12HeisC).all fun x =>
      decide (m12HeisA * x ∈ heisList m12HeisA m12HeisB m12HeisC) &&
        decide (m12HeisB * x ∈ heisList m12HeisA m12HeisB m12HeisC)) = true := by
  decide +kernel

theorem m12Heis_stable : ∀ x ∈ heisList m12HeisA m12HeisB m12HeisC,
    m12HeisA * x ∈ heisList m12HeisA m12HeisB m12HeisC ∧
      m12HeisB * x ∈ heisList m12HeisA m12HeisB m12HeisC := by
  intro x hx
  simpa using List.all_eq_true.1 m12Heis_stable_bool x hx

set_option maxRecDepth 100000 in
theorem m12Heis_centre_bool :
    ((heisList m12HeisA m12HeisB m12HeisC).all fun y =>
      !(decide (m12HeisA * y = y * m12HeisA) && decide (m12HeisB * y = y * m12HeisB)) ||
        decide (y = 1 ∨ y = m12HeisC ∨ y = m12HeisC⁻¹)) = true := by
  decide +kernel

theorem m12Heis_centre : ∀ y ∈ heisList m12HeisA m12HeisB m12HeisC,
    m12HeisA * y = y * m12HeisA → m12HeisB * y = y * m12HeisB →
      y = 1 ∨ y = m12HeisC ∨ y = m12HeisC⁻¹ := by
  intro y hy hya hyb
  have := List.all_eq_true.1 m12Heis_centre_bool y hy
  simpa [hya, hyb] using this

end CFSG.AGLEmbedding.KFactProofs.M12Z2

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.AGLEmbedding.KFactProofs.M12Z2 CFSG.Blueprint

theorem step1917Z2KM12 : Step1917Z2KM12 :=
  threeCentralZ2_of_heisList (M := NativeSporadic.M12) (m := 3520) (by norm_num)
    (by rw [CFSG.Sporadic.Schreier.m12_card]; norm_num) m12HeisA_mem m12HeisB_mem m12HeisH_mem
    m12Heis_pow_three.1 m12Heis_pow_three.2 m12Heis_nodup m12Heis_stable m12Heis_centre
    m12Heis_conj m12Heis_not_comm

end CFSG.RankThree.PartTwo.Sec19
