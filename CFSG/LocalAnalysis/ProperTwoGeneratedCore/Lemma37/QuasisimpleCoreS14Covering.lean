module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreS14Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z : J}

namespace FourGen

theorem mul_ne_of_not_commute (hz : FourGen Q z) (h : Setting J Q B) {s : J}
    (hsQ : s ∈ (Q : Subgroup J)) (hss : s * s = centralElt J) (hs_ne : s * z ≠ z * s) {a : J}
    (haQ : a ∈ (Q : Subgroup J)) (haa : a * a = centralElt J) (haz : a * z = z * a)
    (hΩa : ∀ y ∈ (Q : Subgroup J), y * a = a * y → y * y = 1 → y ∈ fourGroup z) :
    s * a ≠ a * s := by
  intro hsa
  have hy : s * a ∈ fourGroup z := hΩa (s * a) ((Q : Subgroup J).mul_mem hsQ haQ)
    (by
      calc s * a * a = a * s * a := by rw [hsa]
        _ = a * (s * a) := by rw [mul_assoc])
    (by
      calc s * a * (s * a) = s * (a * s) * a := by group
        _ = s * (s * a) * a := by rw [hsa]
        _ = (s * s) * (a * a) := by group
        _ = 1 := by rw [hss, haa, h.centralElt_mul_self])
  apply hs_ne
  have h1 : Commute (s * a * a⁻¹) z :=
    (show Commute (s * a) z from hz.mul_comm_of_mem_fourGroup h hy).mul_left
      (show Commute a z from haz).inv_left
  rw [mul_inv_cancel_right] at h1
  exact h1.eq

end FourGen

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
