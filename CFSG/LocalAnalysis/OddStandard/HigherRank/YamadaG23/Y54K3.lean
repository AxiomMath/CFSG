module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54K2b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54V4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Kap
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54M3b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y54_comm_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ n ∈ normIn L c.s.fr.F, ∀ y ∈ f4Y c.s, y⁻¹ * (n * y * n⁻¹) ∈ M3 c.s := by
  intro n hn y hy
  obtain ⟨hF, _, hnorm, _, _⟩ := y54_M3_cand c hH
  obtain ⟨m, hmM, x, hxX0, rfl⟩ := y54_Y_decomp hH (y54_M3_cand c hH) y hy
  have hxY : x ∈ f4Y c.s := y54_X0_le_Y hH hxX0
  have hnmM : n * m * n⁻¹ ∈ M3 c.s := hnorm n hn m hmM
  have hcommM : ⁅n, x⁆ ∈ M3 c.s := hF (y54_NL_X0 hH n hn x hxX0)
  have hxn : n * (m * x) * n⁻¹ = (n * m * n⁻¹) * (⁅n, x⁆ * x) := by group
  have hmid : m⁻¹ * (n * m * n⁻¹) * ⁅n, x⁆ ∈ M3 c.s :=
    mul_mem (mul_mem (inv_mem hmM) hnmM) hcommM
  have hmem : x⁻¹ * (m⁻¹ * (n * m * n⁻¹) * ⁅n, x⁆) * x ∈ M3 c.s := by
    simpa using
      y54_M_normal hH (y54_M3_cand c hH) x⁻¹ ((f4Y c.s).inv_mem hxY) _ hmid
  have heq : (m * x)⁻¹ * (n * (m * x) * n⁻¹)
      = x⁻¹ * (m⁻¹ * (n * m * n⁻¹) * ⁅n, x⁆) * x := by
    rw [hxn]; group
  rw [heq]; exact hmem

theorem y54_K_le_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    centIn (M2 c.s) c.s.fr.F ≤ M3 c.s := by
  intro k hkK
  obtain ⟨hF, _, _, _, _⟩ := y54_M3_cand c hH
  obtain ⟨κ, hκN, hκ3, hκV, hκfpf, hκK⟩ := y54_kappa c hH
  have hκN' : κ ∈ f4N c.s := y54_NL_le_N hH hκN
  have hkY : k ∈ f4Y c.s := y54_K_le_Y c hH hkK
  have hk1K : κ * k * κ⁻¹ ∈ centIn (M2 c.s) c.s.fr.F := hκK k hkK
  have hk1Y : κ * k * κ⁻¹ ∈ f4Y c.s := y54_K_le_Y c hH hk1K
  have hm1M3 : k⁻¹ * (κ * k * κ⁻¹) ∈ M3 c.s := y54_comm_M3 c hH κ hκN k hkY
  have hm2M3 : (κ * k * κ⁻¹)⁻¹ * (κ * (κ * k * κ⁻¹) * κ⁻¹) ∈ M3 c.s :=
    y54_comm_M3 c hH κ hκN (κ * k * κ⁻¹) hk1Y
  set u : G := (k * (κ * k * κ⁻¹))⁻¹ * (κ * (κ * k * κ⁻¹) * κ⁻¹) with hu_def
  have huK : u ∈ centIn (M2 c.s) c.s.fr.F := by
    rw [hu_def]; exact mul_mem (inv_mem (mul_mem hkK hk1K)) (hκK _ hk1K)
  have huY : u ∈ f4Y c.s := y54_K_le_Y c hH huK
  have hphikk1 : f3phi c.s (k * (κ * k * κ⁻¹))
      = f3phi c.s k * f3phi c.s (κ * k * κ⁻¹) :=
    y54_phi_mul hH k hkY (κ * k * κ⁻¹) hk1Y
  have hphik2 : f3phi c.s (κ * (κ * k * κ⁻¹) * κ⁻¹)
      = f3phi c.s k * f3phi c.s (κ * k * κ⁻¹) * f3phi c.s u := by
    have h := y54_phi_mul hH (k * (κ * k * κ⁻¹)) (mul_mem hkY hk1Y) u huY
    have heq : k * (κ * k * κ⁻¹) * u = κ * (κ * k * κ⁻¹) * κ⁻¹ := by
      rw [hu_def]; group
    rw [heq, hphikk1] at h
    exact h
  have hv1 : f3phi c.s (κ * k * κ⁻¹) = κ * f3phi c.s k * κ⁻¹ :=
    y54_phi_conj hH κ hκN' k
  have hv2 : f3phi c.s (κ * (κ * k * κ⁻¹) * κ⁻¹)
      = κ * f3phi c.s (κ * k * κ⁻¹) * κ⁻¹ :=
    y54_phi_conj hH κ hκN' (κ * k * κ⁻¹)
  have hcycle := y54_V_cycle (V := cen c.s.fr.B) (y54_V_sq hH) (y54_V_card hH) hκV hκ3 hκfpf
  have hvPhiV : f3phi c.s k ∈ cen c.s.fr.B := y54_K_phi_mem c hH k hkK
  have hvv1 : f3phi c.s k * f3phi c.s (κ * k * κ⁻¹)
      = f3phi c.s (κ * (κ * k * κ⁻¹) * κ⁻¹) := by
    rw [hv1, hv2, hv1]
    exact hcycle _ hvPhiV
  have hphi_u : f3phi c.s u = 1 := by
    have h1 : f3phi c.s (κ * (κ * k * κ⁻¹) * κ⁻¹)
        = f3phi c.s (κ * (κ * k * κ⁻¹) * κ⁻¹) * f3phi c.s u := by
      calc f3phi c.s (κ * (κ * k * κ⁻¹) * κ⁻¹)
          = f3phi c.s k * f3phi c.s (κ * k * κ⁻¹) * f3phi c.s u := hphik2
        _ = f3phi c.s (κ * (κ * k * κ⁻¹) * κ⁻¹) * f3phi c.s u := by rw [hvv1]
    have h2 : (1 : G) = f3phi c.s u := mul_left_cancel (by rw [mul_one]; exact h1)
    exact h2.symm
  have huX0 : u ∈ f4X0 c.s := (y54_phi_eq_one hH u huY).mp hphi_u
  have huF : u ∈ c.s.fr.F := by
    have h : u ∈ centIn (M2 c.s) c.s.fr.F ⊓ f4X0 c.s := ⟨huK, huX0⟩
    simpa [y54_K_inf_X0 c hH] using h
  have hk2M3 : κ * (κ * k * κ⁻¹) * κ⁻¹ ∈ M3 c.s := by
    have heq : κ * (κ * k * κ⁻¹) * κ⁻¹ = k ^ 2 * (k⁻¹ * (κ * k * κ⁻¹)) * u := by
      rw [hu_def]; group
    rw [heq]
    exact mul_mem (mul_mem (hF (y54_Y_sq c hH k hkY)) hm1M3) (hF huF)
  have heqk : k = (κ * (κ * k * κ⁻¹) * κ⁻¹)
      * ((κ * k * κ⁻¹)⁻¹ * (κ * (κ * k * κ⁻¹) * κ⁻¹))⁻¹
      * (k⁻¹ * (κ * k * κ⁻¹))⁻¹ := by group
  rw [heqk]
  exact mul_mem (mul_mem hk2M3 (inv_mem hm2M3)) (inv_mem hm1M3)

end CFSG.OddStandard.HigherRank.YamadaG23
