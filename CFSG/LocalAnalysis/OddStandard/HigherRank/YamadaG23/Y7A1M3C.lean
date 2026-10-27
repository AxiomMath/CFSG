module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1OddN
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Core
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1KF
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1RegD

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_M3_le_C6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    M3 c.s ≤ C6 c.e := by
  obtain ⟨ψ, lab, P, hP⟩ := y7a_reg_data c hH hF
  obtain ⟨N₃, hN⟩ := y7a_exists_N3 hH
  obtain ⟨k, hkK, hk3, hfpf⟩ := y7a_exists_k_F hH
  obtain ⟨hkA, hkFmem⟩ := Subgroup.mem_inf.mp hkK
  have hkF : ∀ f ∈ c.s.fr.F, k * f * k⁻¹ ∈ c.s.fr.F := by
    have hn : k ∈ Subgroup.normalizer (c.s.fr.F : Set G) := (Subgroup.mem_inf.mp hkFmem).2
    intro f hf
    exact (Subgroup.mem_normalizer_iff.mp hn f).mp hf
  have hkNH : k ∈ f4N c.s := y54_NL_le_N hH hkFmem
  have hkY : k ∈ y7aY c := s5_NLA_le_Y c.toCtx5 hH hkA
  have hkX : k ∈ y7aX c := y7a_Y_le_X c hH hkY
  have hkN3 : k ∈ N₃ := hN.char k hkA 1 (by
    show k ^ 3 ∈ c.s.fr.A
    rw [hk3]
    exact Subgroup.one_mem _)
  have hYmem : ∀ w ∈ M3 c.s, w ∈ f4Y c.s := fun w hw => (y54_M3_cand c.toCtx5 hH).2.1 hw
  have hphi_d : f3phi c.s c.d = c.s.fr.z := y54_phi_d (c := c.toCtx5) hH
  have hzord : orderOf c.s.fr.z = 2 := s3_z_order c.s (lfactsA_of_setting hH.hS hH.hZ c.s)
  have hW : ∀ w ∈ M3 c.s, k * w * k⁻¹ ∈ M3 c.s := y54_N_norm_M3 c.toCtx5 hH k hkNH
  have hD : ∀ w ∈ C6 c.e, k * w * k⁻¹ ∈ C6 c.e := y7a_C6_normal c hH hF k hkX
  have hφF : ∀ w ∈ M3 c.s, f3phi c.s w ∈ c.s.fr.F :=
    fun w hw => y54_phi_mem hH w (hYmem w hw)
  have hφmul : ∀ w ∈ M3 c.s, ∀ w' ∈ M3 c.s,
      f3phi c.s (w * w') = f3phi c.s w * f3phi c.s w' :=
    fun w hw w' hw' => y54_phi_mul hH w (hYmem w hw) w' (hYmem w' hw')
  have hφk : ∀ w, f3phi c.s (k * w * k⁻¹) = k * f3phi c.s w * k⁻¹ :=
    y54_phi_conj hH k hkNH
  have hFsq : ∀ f ∈ c.s.fr.F, f ^ 2 = 1 := y54_F_sq hH
  have hFcomm : ∀ f ∈ c.s.fr.F, ∀ f' ∈ c.s.fr.F, f * f' = f' * f := y54_F_comm hH
  have hZ : ∀ x ∈ c.s.fr.Z, x = 1 ∨ x = f3phi c.s c.d := by
    intro x hx
    unfold SFrame.Z at hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hn, ← zpow_mod_orderOf,
      show (orderOf c.s.fr.z : ℤ) = 2 by rw [hzord]; rfl]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp [hphi_d]
  have hdD : c.d ∈ C6 c.e :=
    y7a_C1_le_C6 c hH hF (show c.d ∈ C1 c.e from Subgroup.mem_sup_right c.d_mem)
  have hdW : c.d ∈ M3 c.s := y7a_d_mem_M3 c
  have hker : ∀ w ∈ M3 c.s, f3phi c.s w = 1 → w ∈ C6 c.e := by
    intro w hw hphi
    have hw0 : w ∈ f4X0 c.s := (y54_phi_eq_one hH w (hYmem w hw)).mp hphi
    have hwF : w ∈ c.s.fr.F := by
      rw [← y54_H_inf_M3 c.toCtx5 hH]
      exact ⟨hw0.1, hw⟩
    exact y7a_C1_le_C6 c hH hF
      (show w ∈ C1 c.e from Subgroup.mem_sup_left (s3_F_le_A c.s hwF))
  have hcomm : ∀ w ∈ M3 c.s, k * w * k⁻¹ * w⁻¹ ∈ C6 c.e := by
    intro w hw
    have hmem : ⁅k, w⁆ ∈ M3 c.s := by
      rw [commutatorElement_def]
      exact (M3 c.s).mul_mem (hW w hw) ((M3 c.s).inv_mem hw)
    have h2 : ⁅k, w⁆ ^ (2 ^ 1) = 1 := by
      simpa using (y7a_M3_elemAbelian c hH).2 ⁅k, w⁆ hmem
    exact y7a_comm_in_C6 c hH hF hP hN hkN3 (y7a_M3_le_X c hF hw) (j := 1) h2
  exact y7a_core (W := M3 c.s) (D := C6 c.e) (F := c.s.fr.F) (Z := c.s.fr.Z)
    (φ := f3phi c.s) (k := k) (d := c.d) hk3 hW hD hφF hφmul hφk hFsq hFcomm hkF hfpf
    hZ hdD hdW hker hcomm

end CFSG.OddStandard.HigherRank.YamadaG23
