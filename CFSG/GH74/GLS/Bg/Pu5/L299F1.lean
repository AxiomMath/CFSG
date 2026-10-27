module

public import CFSG.GH74.GLS.Bg.Pu5.L299FAB
public import CFSG.GH74.GLS.Bg.Pu5.L299FStatements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec6

theorem l299f1_of (h44 : II4_44) (hquat : II4_4_quat) (hAut : II4_Aut) (h296 : L296) : L299F1 := by
  intro G _ _ z t S hC hcard K hK hQ4 hQnc
  obtain ⟨v, w, -, -, -, hvt, hvv, hww, -, -, hvw, htw⟩ :=
    four_data h44 hquat hAut h296 hC hcard hK hQ4 hQnc
  have hz2 : z * z = 1 := hC.z_mul_self
  have hvinv : v⁻¹ = v * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hvv, hz2])
  refine ⟨v * w, ?_, ?_⟩
  · have h1 : t * (v * w) * t⁻¹ = v * w := by
      calc t * (v * w) * t⁻¹ = (t * v * t⁻¹) * (t * w * t⁻¹) := by group
        _ = (v * z) * (z * w) := by rw [hvt, htw, hvinv]
        _ = v * (z * z) * w := by group
        _ = v * w := by rw [hz2, mul_one]
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  · calc v * w * (v * w) = v * (w * v) * w := by group
      _ = v * (v * w) * w := by rw [← hvw]
      _ = (v * v) * (w * w) := by group
      _ = z := by rw [hvv, hww, mul_one]

end CFSG.GH74.GLS.Bg.Pu5
