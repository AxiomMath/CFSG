module

public import CFSG.GF2Type.Smith1979.IdxFourIdentFLCheck
public import CFSG.GF2Type.Smith1979.IdxFourIdentFLStruct

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

namespace FLCheck

@[expose] def cyc6 : Equiv.Perm (Fin 6) where
  toFun i := i + 1
  invFun i := i - 1
  left_inv i := add_sub_cancel_right i 1
  right_inv i := sub_add_cancel i 1

theorem permE_hasRows (π : Equiv.Perm (Fin 6)) : HasRows (permE π) (monRowsF 0 π 0) := by
  have h := mon_hasRows 0 π 0
  rwa [diagE_zero, one_mul, ZMod.val_zero, pow_zero, mul_one] at h

theorem s12_hasRows : HasRows (permE (Equiv.swap 0 1)) s12Rows.toList := by
  have h := permE_hasRows (Equiv.swap 0 1)
  rwa [show monRowsF 0 (Equiv.swap 0 1) 0 = s12Rows.toList by decide +kernel] at h

theorem s6_hasRows : HasRows (permE cyc6) s6Rows.toList := by
  have h := permE_hasRows cyc6
  rwa [show monRowsF 0 cyc6 0 = s6Rows.toList by decide +kernel] at h

theorem sig_hasRows : HasRows frobE sigRows.toList := by
  have h := mon_hasRows 0 1 1
  rwa [diagE_zero, permE_one, one_mul, one_mul, MonAux.frobPow_one,
    show monRowsF 0 (1 : Equiv.Perm (Fin 6)) 1 = sigRows.toList by decide +kernel] at h

end FLCheck

open FLCheck

theorem fl_core {X : Subgroup G12} (hX : Nat.card X = 39191040) (hN : Nsub ≤ X) {y : G12}
    (hy : y ∈ X) (hyg : y ∈ gammaU) (hyu : y * theta0e = theta0e * y) (hnot : y ∉ monLin)
    (hd : y⁻¹ * diagE chStd * y ∈ D5) : M0 ≤ X := by
  obtain ⟨a, b, s, c, π, hc, rfl⟩ := adjacent_structure hyg hyu hd
  have hn : diagE c * permE π ∈ Nsub :=
    mem_Nsub_iff.2 ⟨c, π, 0, hc, by rw [ZMod.val_zero, pow_zero, mul_one]⟩
  have hZ : Umat a b * Delta0 s ∈ X := by
    have h := mul_mem hy (inv_mem (hN hn))
    rwa [mul_inv_cancel_right] at h
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    apply hnot
    rw [Umat_zero_zero, one_mul]
    exact mul_mem (Delta0_mem_monLin s) (mem_monLin_iff.2 ⟨c, π, rfl⟩)
  have hy3 : y3e ∈ X := by
    rcases candidates_ok a b s hab with ⟨m₁, hm₁, m₂, hm₂, he⟩ | ⟨m₁, hm₁, m₂, hm₂, h11⟩
    · have h : y3e = m₁⁻¹ * (Umat a b * Delta0 s) * m₂⁻¹ := by
        rw [he]
        group
      rw [h]
      exact mul_mem (mul_mem (inv_mem (hN hm₁)) hZ) (inv_mem (hN hm₂))
    · have hw := mul_mem (mul_mem (mul_mem hZ (hN hm₁)) hZ) (hN hm₂)
      have h := h11.trans (Subgroup.orderOf_dvd_natCard X hw)
      rw [hX] at h
      omega
  refine (Subgroup.closure_le X).2 ?_
  rintro l ⟨r, hr, hl⟩
  simp only [m0Gens, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [HasRows.eq ⟨rfl, hl⟩ s12_hasRows]
    exact hN (permE_mem_Nsub _)
  · rw [HasRows.eq ⟨rfl, hl⟩ s6_hasRows]
    exact hN (permE_mem_Nsub _)
  · rw [HasRows.eq ⟨rfl, hl⟩ sig_hasRows]
    exact hN frobE_mem_Nsub
  · rw [HasRows.eq ⟨rfl, hl⟩ y3e_hasRows]
    exact hy3

end CFSG.GF2Type.Smith1979.IdxFour
