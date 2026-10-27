module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshQData

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

section Letters

variable {H : Type*} [Group H] (g : Fin 8 → H)

theorem lift_lE : FreeGroup.lift g (FreeGroup.mk lE) = g 0 := lift_mk_single g 0
theorem lift_lA : FreeGroup.lift g (FreeGroup.mk lA) = g 1 := lift_mk_single g 1
theorem lift_lB : FreeGroup.lift g (FreeGroup.mk lB) = g 2 := lift_mk_single g 2
theorem lift_lU : FreeGroup.lift g (FreeGroup.mk lU) = g 3 := lift_mk_single g 3
theorem lift_lS : FreeGroup.lift g (FreeGroup.mk lS) = g 4 := lift_mk_single g 4
theorem lift_lR : FreeGroup.lift g (FreeGroup.mk lR) = g 5 := lift_mk_single g 5
theorem lift_lD : FreeGroup.lift g (FreeGroup.mk lD) = g 6 := lift_mk_single g 6
theorem lift_lD' : FreeGroup.lift g (FreeGroup.mk lD') = g 7 := lift_mk_single g 7

theorem lift_wC :
    FreeGroup.lift g (FreeGroup.mk wC) = g 1 * g 1 * g 2 * g 2 := by
  unfold wC
  rw [lift_mk_append, lift_mk_append, lift_mk_append, lift_lA, lift_lB]

end Letters

theorem rel4D_trivial {H : Type*} [Group H] (g : Fin 8 → H) (α β : ℕ)
    (hDD : g 6 * g 6 = 1) (hD'D' : g 7 * g 7 = 1)
    (hE : g 6 * g 0 * g 6 = g 0 * (g 1 * g 1 * g 2 * g 2))
    (hA : g 6 * g 1 * g 6 = g 1 * (g 1 * g 1 * g 2 * g 2) ^ α)
    (hB : g 6 * g 2 * g 6 = g 2 * (g 1 * g 1 * g 2 * g 2) ^ α)
    (hU : g 6 * g 3 * g 6 = g 3)
    (hE' : g 7 * g 0 * g 7 = g 0 * g 1 * g 1)
    (hA' : g 7 * g 1 * g 7 = g 1)
    (hB' : g 7 * g 2 * g 7 = g 2 * (g 1 * g 1) ^ α)
    (hU' : g 7 * g 3 * g 7 = g 3)
    (hDS : (g 4)⁻¹ * g 6 * g 4 = g 7)
    (hS3 : g 4 * g 4 * g 4 = 1)
    (hR : g 5 * g 6 = g 6 * g 5)
    (hRS : (g 5)⁻¹ * g 4 * g 5 = (g 4)⁻¹)
    (hz : g 7 * g 6 * (g 4 * g 6 * (g 4)⁻¹) =
      g 3 ^ α * (g 1 * g 1 * g 2 * g 2) ^ β * g 0 ^ β)
    (hZ1 : (g 3 ^ α * (g 1 * g 1 * g 2 * g 2) ^ β * g 0 ^ β) *
      (g 3 ^ α * (g 1 * g 1 * g 2 * g 2) ^ β * g 0 ^ β) = 1)
    (hZ2 : (g 3 ^ α * (g 1 * g 1 * g 2 * g 2) ^ β * g 0 ^ β) * (g 2 * g 2) ^ β =
      (g 4 * g 6 * (g 4)⁻¹) * (g 3 ^ α * (g 1 * g 1 * g 2 * g 2) ^ β * g 0 ^ β) *
        (g 4 * g 6 * (g 4)⁻¹)⁻¹)
    (hZ3 : (g 3 ^ α * (g 1 * g 1 * g 2 * g 2) ^ β * g 0 ^ β) * (g 2 * g 2) ^ β *
      (g 3 ^ α * (g 1 * g 1 * g 2 * g 2) ^ β * g 0 ^ β) = (g 2 * g 2) ^ β) :
    ∀ r ∈ rel4D α β, FreeGroup.lift g (FreeGroup.mk r) = 1 := by
  have iD : (g 6)⁻¹ = g 6 := inv_eq_of_mul_eq_one_right hDD
  have iD' : (g 7)⁻¹ = g 7 := inv_eq_of_mul_eq_one_right hD'D'
  have cD : ∀ x : H, g 6 * (g 6 * x) = x := fun x => by rw [← mul_assoc, hDD, one_mul]
  have cD' : ∀ x : H, g 7 * (g 7 * x) = x := fun x => by rw [← mul_assoc, hD'D', one_mul]
  have hsq : g 4 * g 4 = (g 4)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]; exact hS3
  have hss : (g 4)⁻¹ * (g 4)⁻¹ = g 4 := by
    rw [← hsq]
    calc g 4 * g 4 * (g 4 * g 4) = (g 4 * g 4 * g 4) * g 4 := by group
      _ = g 4 := by rw [hS3, one_mul]
  have hD'' : g 4 * g 6 * (g 4)⁻¹ =
      g 6 * g 7 * (g 3 ^ α * (g 1 * g 1 * g 2 * g 2) ^ β * g 0 ^ β) := by
    rw [← hz]
    have h : g 6 * g 7 * (g 7 * g 6 * (g 4 * g 6 * (g 4)⁻¹)) = g 4 * g 6 * (g 4)⁻¹ := by
      simp only [mul_assoc, cD, cD']
    exact h.symm
  have h12 : (g 4)⁻¹ * g 7 * g 4 =
      g 6 * g 7 * (g 3 ^ α * (g 1 * g 1 * g 2 * g 2) ^ β * g 0 ^ β) := by
    rw [← hD'']
    calc (g 4)⁻¹ * g 7 * g 4 = (g 4)⁻¹ * ((g 4)⁻¹ * g 6 * g 4) * g 4 := by rw [hDS]
      _ = ((g 4)⁻¹ * (g 4)⁻¹) * g 6 * (g 4 * g 4) := by group
      _ = g 4 * g 6 * (g 4)⁻¹ := by rw [hss, hsq]
  have h13 : (g 5)⁻¹ * g 6 * g 5 = g 6 := by
    rw [mul_assoc, ← hR, inv_mul_cancel_left]
  have hRS' : (g 5)⁻¹ * (g 4)⁻¹ * g 5 = g 4 := by
    calc (g 5)⁻¹ * (g 4)⁻¹ * g 5 = ((g 5)⁻¹ * g 4 * g 5)⁻¹ := by group
      _ = g 4 := by rw [hRS, inv_inv]
  have h14 : (g 5)⁻¹ * g 7 * g 5 =
      g 6 * g 7 * (g 3 ^ α * (g 1 * g 1 * g 2 * g 2) ^ β * g 0 ^ β) := by
    rw [← hD'']
    calc (g 5)⁻¹ * g 7 * g 5 = (g 5)⁻¹ * ((g 4)⁻¹ * g 6 * g 4) * g 5 := by rw [hDS]
      _ = ((g 5)⁻¹ * (g 4)⁻¹ * g 5) * ((g 5)⁻¹ * g 6 * g 5) * ((g 5)⁻¹ * g 4 * g 5) := by group
      _ = g 4 * g 6 * (g 4)⁻¹ := by rw [hRS', h13, hRS]
  have hw2 : (g 4 * g 6 * (g 4)⁻¹) * (g 4 * g 6 * (g 4)⁻¹) = 1 := by
    calc (g 4 * g 6 * (g 4)⁻¹) * (g 4 * g 6 * (g 4)⁻¹) = g 4 * (g 6 * g 6) * (g 4)⁻¹ := by group
      _ = 1 := by rw [hDD]; group
  have hwinv : (g 4 * g 6 * (g 4)⁻¹)⁻¹ = g 4 * g 6 * (g 4)⁻¹ := inv_eq_of_mul_eq_one_right hw2
  have h16 : g 6 * g 7 * g 6 * g 7 = (g 2 * g 2) ^ β := by
    rw [hwinv, hD''] at hZ2
    generalize g 3 ^ α * (g 1 * g 1 * g 2 * g 2) ^ β * g 0 ^ β = z at hZ1 hZ2 hZ3
    generalize (g 2 * g 2) ^ β = Y at hZ2 hZ3 ⊢
    have h1 : z * Y = (g 6 * g 7) * (g 6 * g 7) * z := by
      rw [hZ2]
      calc g 6 * g 7 * z * z * (g 6 * g 7 * z) = g 6 * g 7 * (z * z) * (g 6 * g 7) * z := by group
        _ = (g 6 * g 7) * (g 6 * g 7) * z := by rw [hZ1, mul_one]
    calc g 6 * g 7 * g 6 * g 7 = (g 6 * g 7) * (g 6 * g 7) * (z * z) := by rw [hZ1, mul_one]; group
      _ = ((g 6 * g 7) * (g 6 * g 7) * z) * z := by rw [mul_assoc _ z z]
      _ = z * Y * z := by rw [h1]
      _ = Y := hZ3
  intro r hr
  simp only [rel4D, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · rw [lift_mk_append, lift_lD]; exact hDD
  · rw [lift_mk_append, lift_lD']; exact hD'D'
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_mk_powW, lift_wC, lift_lD, lift_lE]
    rw [iD]; exact hE
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_mk_powW, lift_wC, lift_lD, lift_lA]
    rw [iD]; exact hA
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_mk_powW, lift_wC, lift_lD, lift_lB]
    rw [iD]; exact hB
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_lD, lift_lU]
    rw [iD]; exact hU
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_lD', lift_lE, lift_lA]
    rw [iD']; exact hE'
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_lD', lift_lA]
    rw [iD']; exact hA'
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_mk_powW, lift_lD', lift_lA, lift_lB]
    rw [iD']; exact hB'
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_lD', lift_lU]
    rw [iD']; exact hU'
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_lS, lift_lD, lift_lD']
    exact hDS
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_mk_powW, lift_wC, lift_lS, lift_lD, lift_lD',
      lift_lU, lift_lE]
    simpa only [mul_assoc] using h12
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_lR, lift_lD]
    exact h13
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_mk_powW, lift_wC, lift_lR, lift_lD, lift_lD',
      lift_lU, lift_lE]
    simpa only [mul_assoc] using h14
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_invW, lift_mk_powW, lift_lB, lift_lD, lift_lD']
    rw [iD, iD']; exact h16
  · apply lift_mkRel_eq_one
    simp only [lift_mk_append, lift_mk_powW, lift_lB, lift_lD, lift_lD']
    exact h16

end CFSG.EvenSporadicStandard.M12Std.Yosh
