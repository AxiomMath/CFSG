module

public import CFSG.GH74.QTGen4.Recog.G23.HLettersE
public import CFSG.Quasithin.Recognition.G23TypeDefs

public section

namespace CFSG.GH74.QTGen4.Recog.G23

section Inversion

variable {G : Type} [Group G]

theorem mul_self_eq_one_of_inv_conj {w a : G} (hw : w * w = 1) (h : w * a * w⁻¹ = a⁻¹) :
    w * a * (w * a) = 1 := by
  have h1 : w * a = a⁻¹ * w := by
    rw [← h]
    simp
  calc w * a * (w * a) = (a⁻¹ * w) * (w * a) := by rw [← h1]
    _ = a⁻¹ * (w * w) * a := by simp only [mul_assoc]
    _ = 1 := by simp [hw]

end Inversion

open CFSG.Quasithin.G23Type

end CFSG.GH74.QTGen4.Recog.G23
