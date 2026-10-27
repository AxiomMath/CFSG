module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsMFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsMAct
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8UE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Fam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsM

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam


section Main

variable {n : ℕ}

theorem p23E8AZ8M_proved : P23E8AZ8M n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6 y hyY hyt hy3 hmove m hmC hmM
  classical
  have hAB := p23E8PhiAE_of_comm p23E8UEComm_proved hcit hP Y R S t K' W u e g hc hno hA5 hA6
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hWt : W ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  have heC : e ∈ C := hWt heW
  have huC : u ∈ C := hWt hd.huW
  obtain ⟨v, hvO, m', hm'C, hm'u, rfl⟩ :=
    exists_lift hd.hu2 huC hmC (hmM u hd.hu)
  obtain ⟨I⟩ := hA5
  obtain ⟨x, vH, v', ψ, p, ι, hvx, hvH, hzv, hId, hψx, hι, hψv⟩ := frame_ident hc I
  have hm'U : m' ∈ Subgroup.centralizer ({u} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr hm'u
  have hyU : y ∈ Subgroup.centralizer ({u} : Set Y) := rLayer_le_centralizer _ _ hyY
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hyt
  have hcommv : ∀ k : Y, k * t = t * k → k * u = u * k → k * v' = v' * k := by
    intro k hkt hku
    rcases hzv with h | h
    · rw [← h]
      exact hkt
    · rw [h] at hkt
      apply mul_left_cancel (a := u)
      calc u * (k * v') = (u * k) * v' := by group
        _ = (k * u) * v' := by rw [hku]
        _ = k * (u * v') := by group
        _ = (u * v') * k := hkt
        _ = u * (v' * k) := by group
  set gm : ↥(Subgroup.centralizer ({u} : Set Y)) := ⟨m', hm'U⟩ with hgm
  set gy : ↥(Subgroup.centralizer ({u} : Set Y)) := ⟨y, hyU⟩ with hgy
  have hm't : m' * t = t * m' := Subgroup.mem_centralizer_singleton_iff.mp hm'C
  have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyU
  obtain ⟨r, hr⟩ := hy3.exists_card_eq
  rw [Nat.card_zpowers] at hr
  have hyr : y ^ 3 ^ r = 1 := by
    rw [← hr]
    exact pow_orderOf_eq_one y
  have hgyr : gy ^ 3 ^ r = 1 := Subtype.ext (by simpa using hyr)
  have hodd : Odd (3 ^ r) := Odd.pow (by decide)
  have hτ : ∀ L ∈ TwinDisc.secFam (Om R) u,
      L.map (TwinExitPf6.secAut (Om R) u hΩ hc2 gm).toMonoidHom ∈ TwinDisc.secFam (Om R) u :=
    fun L hL => TwinExitPf10.secAut_map_secFam hΩ hc2 gm hL
  have hσ : ∀ L ∈ TwinDisc.secFam (Om R) u,
      L.map (TwinExitPf6.secAut (Om R) u hΩ hc2 gy).toMonoidHom ∈ TwinDisc.secFam (Om R) u :=
    fun L hL => TwinExitPf10.secAut_map_secFam hΩ hc2 gy hL
  have hτv : TwinExitPf6.secAut (Om R) u hΩ hc2 gm (QuotientGroup.mk vH) = QuotientGroup.mk vH :=
    secAut_eq_of_comm hΩ hc2 gm vH (by rw [hvH]; exact hcommv m' hm't hm'u)
  have hσv : TwinExitPf6.secAut (Om R) u hΩ hc2 gy (QuotientGroup.mk vH) = QuotientGroup.mk vH :=
    secAut_eq_of_comm hΩ hc2 gy vH (by rw [hvH]; exact hcommv y hyt hyu)
  have hσk : ∀ z, ((TwinExitPf6.secAut (Om R) u hΩ hc2 gy : _ ≃* _) : _ → _)^[3 ^ r] z = z := by
    intro z
    rw [secAut_iterate hΩ hc2, hgyr, secAut_one hΩ hc2]
  have hσx : TwinExitPf6.secAut (Om R) u hΩ hc2 gy (QuotientGroup.mk x) ≠ QuotientGroup.mk x := by
    intro heq
    have h1 : TwinExitPf6.secAut (Om R) u hΩ hc2 gy (QuotientGroup.mk x) =
        TwinExitPf6.secAut (Om R) u hΩ hc2 1 (QuotientGroup.mk x) := by
      rw [heq, secAut_one hΩ hc2]
    have h2 := act_conj hΩ hc2 x hvx hd.he2 heC hAB gy 1 hyC (by simp [C]) h1
    simp only [Subgroup.coe_one, inv_one, one_mul, mul_one] at h2
    obtain ⟨o, ho, hyo⟩ := exists_mem_conj_of_odd (oddCoreOf_odd_natCard C)
      (by
        calc y * e * y⁻¹ * (y * e * y⁻¹) = y * (e * e) * y⁻¹ := by group
          _ = 1 := by rw [hd.he2]; group) hd.he2 h2
    exact hmove o ho hyo
  obtain ⟨j, hj3, hj⟩ := three_orbit hId hι hψx hψv
    (TwinExitPf6.secAut (Om R) u hΩ hc2 gm) (TwinExitPf6.secAut (Om R) u hΩ hc2 gy) hτ hσ hτv hσv hodd hσk
    hσx
  rw [secAut_iterate hΩ hc2] at hj
  have hgyj : ((gy ^ j : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) ∈ C := by
    rw [Subgroup.coe_pow]
    exact C.pow_mem hyC j
  have h3 := act_conj hΩ hc2 x hvx hd.he2 heC hAB gm (gy ^ j) hm'C hgyj hj
  rw [Subgroup.coe_pow] at h3
  obtain ⟨v₀, hv₀, hv₀e⟩ := exists_mem_conj_of_odd (oddCoreOf_odd_natCard C)
    (by
      calc m' * e * m'⁻¹ * (m' * e * m'⁻¹) = m' * (e * e) * m'⁻¹ := by group
        _ = 1 := by rw [hd.he2]; group)
    (by
      calc y ^ j * e * (y ^ j)⁻¹ * (y ^ j * e * (y ^ j)⁻¹) = y ^ j * (e * e) * (y ^ j)⁻¹ := by group
        _ = 1 := by rw [hd.he2]; group)
    (by simpa using h3)
  refine ⟨j, hj3, v * v₀, (oddCoreOf C).mul_mem hvO hv₀, ?_⟩
  calc v * m' * e * (v * m')⁻¹ = v * (m' * e * m'⁻¹) * v⁻¹ := by group
    _ = v * (v₀ * (y ^ j * e * (y ^ j)⁻¹) * v₀⁻¹) * v⁻¹ := by rw [← hv₀e]
    _ = v * v₀ * (y ^ j * e * (y ^ j)⁻¹) * (v * v₀)⁻¹ := by group

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsM
