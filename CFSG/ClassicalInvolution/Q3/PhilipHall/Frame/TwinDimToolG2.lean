module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolY1b

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement



section G2

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem B_ne (hc : P23Cfg n Y R S t K' W u e g) :
    (u * e ≠ 1 ∧ u * e ≠ u) ∧ (t ≠ 1 ∧ t ≠ u) ∧ (u * t ≠ 1 ∧ u * t ≠ u) ∧
      (u * e * t ≠ 1 ∧ u * e * t ≠ u) ∧ (u * e * (u * t) ≠ 1 ∧ u * e * (u * t) ≠ u) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hee : e ∉ tightCore R ⊔ K' := e_not_mem_sup hc
  have huS : u ∈ tightCore R ⊔ K' := hd.hu
  have hzS : t ∈ tightCore R ⊔ K' := Subgroup.mem_sup_left hz.mem
  have hue : u * e = e * u := T7K.comm_e_of_mem_W hd hd.huW
  have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hd.hu2
  have hez : u * e * (u * t) = e * t := by
    calc u * e * (u * t) = (e * u) * (u * t) := by rw [hue]
      _ = e * (u * u) * t := by group
      _ = e * t := by rw [hd.hu2]; group
  have a1 : u * e ≠ 1 := by
    intro h
    apply hee
    rw [eq_inv_of_mul_eq_one_right h]
    exact (tightCore R ⊔ K').inv_mem huS
  have a2 : u * e ≠ u := by
    intro h
    exact hd.he1 (mul_left_cancel (h.trans (mul_one u).symm))
  have a3 : u * t ≠ 1 := by
    intro h
    apply hd.huz
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hu1]
  have a4 : u * t ≠ u := by
    intro h
    exact hz.ne_one (mul_left_cancel (h.trans (mul_one u).symm))
  have a5 : u * e * t ≠ 1 := by
    intro h
    apply hee
    have h1 : e * t = u⁻¹ := by
      calc e * t = u⁻¹ * (u * e * t) := by group
        _ = u⁻¹ := by rw [h, mul_one]
    have : e = u⁻¹ * t⁻¹ := by
      calc e = (e * t) * t⁻¹ := by group
        _ = u⁻¹ * t⁻¹ := by rw [h1]
    rw [this]
    exact (tightCore R ⊔ K').mul_mem ((tightCore R ⊔ K').inv_mem huS)
      ((tightCore R ⊔ K').inv_mem hzS)
  have a6 : u * e * t ≠ u := by
    intro h
    apply hee
    have h1 : e * t = 1 := by
      have : u * (e * t) = u * 1 := by rw [← mul_assoc, h, mul_one]
      exact mul_left_cancel this
    rw [eq_inv_of_mul_eq_one_left h1]
    exact (tightCore R ⊔ K').inv_mem hzS
  have a7 : u * e * (u * t) ≠ 1 := by
    intro h
    apply hee
    rw [hez] at h
    rw [eq_inv_of_mul_eq_one_left h]
    exact (tightCore R ⊔ K').inv_mem hzS
  have a8 : u * e * (u * t) ≠ u := by
    intro h
    apply hee
    rw [hez] at h
    have : e = u * t⁻¹ := by
      calc e = (e * t) * t⁻¹ := by group
        _ = u * t⁻¹ := by rw [h]
    rw [this]
    exact (tightCore R ⊔ K').mul_mem huS ((tightCore R ⊔ K').inv_mem hzS)
  exact ⟨⟨a1, a2⟩, ⟨hz.ne_one, fun h => hd.huz h.symm⟩, ⟨a3, a4⟩, ⟨a5, a6⟩, ⟨a7, a8⟩⟩

theorem inf_cent_le_gamma2 (hc : P23Cfg n Y R S t K' W u e g) {s : Y}
    (hsB : s ∈ Subgroup.closure ({u * e, u, t} : Set Y)) (hs1 : s ≠ 1) (hsu : s ≠ u) :
    Subgroup.centralizer ({u} : Set Y) ⊓ Subgroup.centralizer ({s} : Set Y) ≤
      gamma2 (Subgroup.closure ({u * e, u, t} : Set Y)) (Subgroup.centralizer ({u} : Set Y)) := by
  have hd := hc.data
  have hB := B_isElemAbelian hc
  have hcomm := T7A.commutes_closure (comm_gen hc)
  have huB : u ∈ Subgroup.closure ({u * e, u, t} : Set Y) := T7K.u_mem_B t u e
  have hs2 : s * s = 1 := by
    have := hB.2 s hsB
    rwa [pow_two] at this
  have hus : u * s = s * u := hcomm u huB s hsB
  have hA := T7A.isElemAbelian2_closure_pair hd.hu2 hs2 hd.hu1 hs1 (Ne.symm hsu) hus
  have hAB : Subgroup.closure ({u, s} : Set Y) ≤ Subgroup.closure ({u * e, u, t} : Set Y) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact huB
    · exact hsB
  rintro y ⟨hyY, hys⟩
  have hyu : u * y = y * u := (Subgroup.mem_centralizer_singleton_iff.mp hyY).symm
  have hys' : s * y = y * s := (Subgroup.mem_centralizer_singleton_iff.mp hys).symm
  exact T7K.le_gamma2 hAB hA ⟨hyY, T7B.mem_centralizer_closure_pair hyu hys'⟩

theorem oddCore_C_le_gamma2 (hc : P23Cfg n Y R S t K' W u e g) :
    oddCoreOf (Subgroup.centralizer ({u} : Set Y)) ≤
      gamma2 (Subgroup.closure ({u * e, u, t} : Set Y)) (Subgroup.centralizer ({u} : Set Y)) := by
  have hB := B_isElemAbelian hc
  have hB8 := B_natCard hc
  have hBC : Subgroup.closure ({u * e, u, t} : Set Y) ≤ Subgroup.centralizer ({u} : Set Y) := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_gen hc x hx u (by simp))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two (Subgroup.closure ({u * e, u, t} : Set Y))
    (oddCoreOf (Subgroup.centralizer ({u} : Set Y))) hB (by rw [hB8]; norm_num)
    (fun b hb => CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ (hBC hb))
    (Nat.coprime_two_left.mpr
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({u} : Set Y))))
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun E hE => ?_
  have hE2 : IsElemAbelian2 E 2 :=
    ⟨hE.2, fun x hx => by rw [← pow_two]; exact hB.2 x (hE.1 hx)⟩
  exact (inf_le_inf_right _ (CFSG.ClassicalInvolution.Balance.oddCoreIn_le _)).trans
    (T7K.le_gamma2 hE.1 hE2)

end G2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
