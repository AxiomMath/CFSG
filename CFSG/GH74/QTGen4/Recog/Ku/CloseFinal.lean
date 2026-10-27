module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Recognition.HSTypeS6

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

variable {G : Type} [Group G]

theorem kuClose_mul_comm_of_inv {a b y : G} (ha : a * y * a⁻¹ = y⁻¹)
    (hb : b * y * b⁻¹ = y⁻¹) : a * b * y = y * (a * b) := by
  have ha' : a * y = y⁻¹ * a := by
    rw [← ha, inv_mul_cancel_right]
  have hb' : b * y = y⁻¹ * b := by
    rw [← hb, inv_mul_cancel_right]
  have h1 : y * a * y = a := by
    rw [mul_assoc, ha', ← mul_assoc, mul_inv_cancel, one_mul]
  have h2 : y * a = a * y⁻¹ := by
    calc y * a = y * a * y * y⁻¹ := by rw [mul_inv_cancel_right]
      _ = a * y⁻¹ := by rw [h1]
  calc a * b * y = a * (b * y) := by rw [mul_assoc]
    _ = a * (y⁻¹ * b) := by rw [hb']
    _ = (a * y⁻¹) * b := by rw [mul_assoc]
    _ = (y * a) * b := by rw [← h2]
    _ = y * (a * b) := by rw [mul_assoc]

end CFSG.GH74.QTGen4.Ku

end
