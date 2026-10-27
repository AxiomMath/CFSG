module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8LayMain

import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsMAct

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZLay

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Frattini

variable {Y : Type} [Group Y] [Finite Y]

theorem le_cent_sup_oddCore_of_mem_zStarOf {H : Subgroup Y} {z : Y} (hz2 : z * z = 1)
    (hz : z ∈ zStarOf H) :
    H ≤ (H ⊓ Subgroup.centralizer ({z} : Set Y)) ⊔ oddCoreOf H := by
  intro y hy
  obtain ⟨hzH, hcomm⟩ := (Asc77.C25W.mem_zStarOf_iff H).mp hz
  have ha2 : y * z * y⁻¹ * (y * z * y⁻¹) = 1 := by
    calc y * z * y⁻¹ * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hab : (y * z * y⁻¹)⁻¹ * z ∈ oddCoreOf H := by
    have h1 := (oddCoreOf H).inv_mem (hcomm y⁻¹ (H.inv_mem hy))
    have he : (y * z * y⁻¹)⁻¹ * z = (z⁻¹ * y⁻¹⁻¹ * z * y⁻¹)⁻¹ := by group
    rw [he]
    exact h1
  obtain ⟨v, hv, hva⟩ := ClsM.exists_mem_conj_of_odd (oddCoreOf_odd_natCard H) ha2 hz2 hab
  have hvH : v ∈ H := oddCoreOf_le_self H hv
  have hc : v⁻¹ * y ∈ H ⊓ Subgroup.centralizer ({z} : Set Y) := by
    refine ⟨H.mul_mem (H.inv_mem hvH) hy, ?_⟩
    show v⁻¹ * y ∈ Subgroup.centralizer ({z} : Set Y)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : v⁻¹ * y * z = v⁻¹ * (y * z * y⁻¹) * y := by group
    rw [h2, hva]
    group
  have hy' : y = v * (v⁻¹ * y) := by group
  rw [hy']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hv) (Subgroup.mem_sup_left hc)

end Frattini


section Main

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem rLayer_le_gen_of_zStar (hc : P23Cfg n Y R S t K' W u e g)
    (hz : u * e ∈ zStarOf (rLayer (Om R) u)) :
    rLayer (Om R) u ≤ (rLayer (Om R) u ⊓ Subgroup.centralizer ({u * e} : Set Y)) ⊔
      (rLayer (Om R) u ⊓ Subgroup.centralizer ({t} : Set Y)) ⊔
      (rLayer (Om R) u ⊓ oddCoreOf (Subgroup.centralizer ({u} : Set Y))) := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz0 : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hτK : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hc.data.hgt]
    exact hz0.conj g
  have hue2 : u * e * (u * e) = 1 := hτK.sq
  have hYC : rLayer (Om R) u ≤ Subgroup.centralizer ({u} : Set Y) := by
    unfold rLayer
    exact iSup₂_le fun _ _ => iSup_le fun hR => hR
  have hO : oddCoreOf (rLayer (Om R) u) ≤ oddCoreOf (Subgroup.centralizer ({u} : Set Y)) :=
    T8.oddCoreOf_le_oddCoreOf_of_normalized hYC
      (fun c hc' => T8.rLayer_conjSub_eq hΩ.conjInvariant hc')
  refine (le_cent_sup_oddCore_of_mem_zStarOf hue2 hz).trans (sup_le ?_ ?_)
  · exact le_sup_left.trans le_sup_left
  · exact (le_inf (oddCoreOf_le_self _) hO).trans le_sup_right

theorem p23E8ZLay_of_t4 (hT4 : TwinThmE.T4Supply) : P23E8ZLay n := by
  intro hcit hP Y _ _ R S t K' W u e g hc _ hz _ J hJ
  exact Lay.mem_dstarComp_of_mem_tqMembers3 (hT4 n hcit hP) hc
    (Lay.rLayer_le_sigmaStarNorm hc (rLayer_le_gen_of_zStar hc hz)) J hJ

theorem p23E8ZGen_of_sig (hT4 : TwinThmE.T4Supply) (hTwo : P23Two n) (hS : P23E8ZSig n) : P23E8ZGen n :=
  p23E8ZGen_of_parts hTwo (p23E8ZLay_of_t4 hT4) hS

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZLay
