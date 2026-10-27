module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Dec
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Gen
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Act

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

section Fin

variable [Finite G] {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {u : G}

theorem ps4_std_aux (h : Data S P₁ P₂ z t a) {u : G} (hu : UHyp S P₁ P₂ z u)
    (hwrap : ∃ (t' a₀ b₀ : G) (M : ℕ), Canon S P₁ P₂ z t' a a₀ b₀ M ∧ u = xx t' a₀ M ∧
      Zc (P₁ ⊔ P₂) z t' = Zc (P₁ ⊔ P₂) z t ∧ Xc (P₁ ⊔ P₂) z t' = Xc (P₁ ⊔ P₂) z t) :
    Ps4Std S z u a (Zc (P₁ ⊔ P₂) z t) (Xc (P₁ ⊔ P₂) z t) := by
  obtain ⟨t', a₀, b₀, M, hC, hux, hZ, hX⟩ := hwrap
  have hzS : z ∈ S := h.z_mem
  have hzR : z ∈ P₁ ⊔ P₂ := mem_sup_left h.z_mem₁
  have huS : u ∈ S := h.R_le_S hu.mem
  have hzu : z * u = u * z := h.z_cent' huS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (h.mem_Xc_of_mem_R hu.mem).2 ⟨hu.sq, hu.ne_one, hu.ne_z⟩
  · refine (h.mem_Xc_of_mem_R (mul_mem hu.mem hzR)).2 ⟨?_, ?_, ?_⟩
    · calc u * z * (u * z) = u * (z * u) * z := by simp only [mul_assoc]
        _ = u * (u * z) * z := by rw [hzu]
        _ = (u * u) * (z * z) := by simp only [mul_assoc]
        _ = 1 := by rw [hu.sq, h.z_sq, mul_one]
    · intro e
      apply hu.ne_z
      have := eq_inv_of_mul_eq_one_left e
      rw [this, h.z_inv]
    · intro e
      apply hu.ne_one
      exact mul_right_cancel (e.trans (one_mul z).symm)
  · rw [hux]; exact hC.relIndex_Tc
  · rw [hux]; exact hC.center_Tc
  · intro w0 hw0T hw0sq hw0Z hw0z huw0Z hcard U hU hnorm hUcard hUdih hinf hcls
    rw [hux] at hw0T huw0Z hinf hcls hU
    rw [← hZ] at hw0Z huw0Z
    rw [← hX, ← hZ] at hcls
    have hV : w0 ∈ Vset S (P₁ ⊔ P₂) z t' (xx t' a₀ M) := ⟨hw0T, hw0Z, hw0z, huw0Z⟩
    rw [hux, ← hZ, ← hX]
    exact hC.ps4_decomp hV hU hUcard hinf hcls

theorem ps4_actual (h : Data S P₁ P₂ z t a) :
    Ps4Actual S z t a (Zc (P₁ ⊔ P₂) z t) (Xc (P₁ ⊔ P₂) z t) (US P₁ t) where
  z_Z := Or.inl rfl
  t_Z := Or.inr ⟨1, one_mem _, by simp⟩
  tz_X := Or.inr ⟨1, one_mem _, by simp⟩
  partition := h.partition
  card_Ct := h.actual_card
  US_le := h.US_le
  US_normal := h.US_normal
  US_card := h.US_card
  US_dih := h.US_dih
  US_inter := h.US_inter
  US_cls := h.US_cls

theorem ps4_std (h : Data S P₁ P₂ z t a) (hu : UHyp S P₁ P₂ z u) :
    Ps4Std S z u a (Zc (P₁ ⊔ P₂) z t) (Xc (P₁ ⊔ P₂) z t) :=
  ps4_std_aux h hu (exists_canon_of_uhyp h hu)

end Fin

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
