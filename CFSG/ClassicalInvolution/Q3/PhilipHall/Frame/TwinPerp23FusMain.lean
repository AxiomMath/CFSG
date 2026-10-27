module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusN
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R56YExit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusLie
public import CFSG.ClassicalInvolution.Q3.TL4AE286Link
public import CFSG.ClassicalInvolution.Q3.TL4OddFrGen
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4D
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4F
public import CFSG.ClassicalInvolution.Q3.TL4OddMu6
public import CFSG.ClassicalInvolution.Q3.TL4VtxFree

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement


section Main

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem mem_cent_u_of_cent_e (hc : P23Cfg n Y R S t K' W u e g) {x : Y}
    (hxe : x ∈ Subgroup.centralizer ({e} : Set Y)) (hxw : x * (u * e) = (u * e) * x) :
    x ∈ Subgroup.centralizer ({u} : Set Y) := by
  have he2 := hc.data.he2
  have hxe' : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp hxe
  have hu_eq : u = (u * e) * e := by rw [mul_assoc, he2, mul_one]
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * u = x * ((u * e) * e) := by rw [← hu_eq]
    _ = (x * (u * e)) * e := by group
    _ = ((u * e) * x) * e := by rw [hxw]
    _ = (u * e) * (x * e) := by group
    _ = (u * e) * (e * x) := by rw [hxe']
    _ = ((u * e) * e) * x := by group
    _ = u * x := by rw [← hu_eq]

theorem mem_cent_e_of_cent_u (hc : P23Cfg n Y R S t K' W u e g) {x : Y}
    (hxu : x ∈ Subgroup.centralizer ({u} : Set Y)) (hxw : x * (u * e) = (u * e) * x) :
    x ∈ Subgroup.centralizer ({e} : Set Y) := by
  have hu2 := hc.data.hu2
  have hxu' : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hxu
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (CFSG.ClassicalInvolution.Asc77.T7Y.comm_e_of_comm_u_ue hu2 hxu' hxw)

theorem p23YExitAE_proved (n : ℕ) : R56.P23YExitAE n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hnoU h5 hno hEorth
  obtain ⟨Q, Q', hTu, hTe⟩ := layerTwins_both hc
  obtain ⟨x, hxe, hxodd, hxQ, hxQ', ⟨q, hq, hxq⟩, -⟩ := lie_fusion_at hcit hP hc.std.perp hTe hno
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hwQ' : u * e ∈ Q' := involution_mem_sylow hΩ hTe.hJ'.1 hTe.hw' hTe.hQ'
  have hxu := mem_cent_u_of_cent_e hc hxe (hxQ' _ hwQ')
  obtain ⟨I⟩ := h5
  exact hxq (nside_ae hc.std.perp hTu (Or.inl rfl) I hxu hxodd hxQ hxQ' q hq)

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus
