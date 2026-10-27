module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B1a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B1c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54One
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Iso

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y7b_E_inf_zpowers_t (c : Ctx7 G L) (hb : B5Std c) :
    c.s.fr.E ⊓ zpowers c.s.t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxE, hxt⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxt
  rw [← hn] at hxE ⊢
  rcases Int.emod_two_eq_zero_or_one n with h2 | h2
  · have h2' : n % ((2 : ℕ) : ℤ) = 0 := h2
    rw [show c.s.t ^ n = 1 by rw [← zpow_mod_orderOf c.s.t n, c.s.t_order, h2']; simp]
  · exfalso
    have h2' : n % ((2 : ℕ) : ℤ) = 1 := h2
    have htn : c.s.t ^ n = c.s.t := by
      rw [← zpow_mod_orderOf c.s.t n, c.s.t_order, h2']; simp
    exact s3_t_not_mem_L c.s hb.hH.h31 (htn ▸ y56_E_le_L c.s hxE)

theorem y7b_card_C4 (c : Ctx7 G L) (hb : B5Std c) : Nat.card ↥(C4 c.s) = 2 ^ 7 := by
  obtain ⟨hN, φ, -⟩ := y56_secProp c.toCtx5 hb.hH
  have hQle : c.s.fr.E ⊔ zpowers c.s.t ≤ C4 c.s := (y56_C4_cand c.toCtx5 hb.hH).1
  have hrel : (c.s.fr.E ⊔ zpowers c.s.t).relIndex (C4 c.s) = 8 := by
    have hcard : Nat.card (↥(C4 c.s) ⧸
        (c.s.fr.E ⊔ zpowers c.s.t).subgroupOf (C4 c.s)) = 8 := by
      rw [Nat.card_congr φ.toEquiv, y7b_card_E hb.hH]
    simpa only [Subgroup.relIndex, Subgroup.index] using hcard
  have hQbot : c.s.fr.E ⊓ zpowers c.s.t = ⊥ := y7b_E_inf_zpowers_t c hb
  have hnorm : c.s.fr.E ≤ Subgroup.normalizer (zpowers c.s.t) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    have hc : Commute x c.s.t := y56_t_comm_E c.s x hx
    rw [(hc.zpow_right n).eq]
    group
  have hcardQ : Nat.card ↥(c.s.fr.E ⊔ zpowers c.s.t) = 16 := by
    have h := card_sup_mul_card_inf_of_le_normalizer (H := c.s.fr.E)
      (K := zpowers c.s.t) hnorm
    rw [hQbot, y7b_card_E hb.hH, Nat.card_zpowers, c.s.t_order, Subgroup.card_bot] at h
    simpa using h
  have hmul := Subgroup.relIndex_mul_card (H := c.s.fr.E ⊔ zpowers c.s.t) (K := C4 c.s)
  rw [hrel, inf_eq_left.mpr hQle, hcardQ] at hmul
  norm_num at hmul
  rw [show (2 : ℕ) ^ 7 = 128 by norm_num]
  exact hmul.symm

theorem y7b_card_M4 (c : Ctx7 G L) (hb : B5Std c) : Nat.card ↥(M4 c.e) = 2 ^ 6 := by
  obtain ⟨I, hIE, hzI, hIstable, hrelI⟩ := y7b_C4_cent_d_image c hb
  have hM4leC4 : M4 c.e ≤ C4 c.s := by
    unfold M4 centIn
    exact inf_le_left
  have hzord : orderOf c.s.fr.z = 2 :=
    (lfactsA_of_setting hb.hH.hS hb.hH.hZ c.s).z_order
  have hZleI : c.s.fr.Z ≤ I := by
    rw [show c.s.fr.Z = zpowers c.s.fr.z from rfl]
    exact Subgroup.zpowers_le.mpr hzI
  have hIcase : Nat.card ↥I = 2 ∨ Nat.card ↥I = 8 := by
    by_cases hsub : I ≤ c.s.fr.Z
    · left
      have hIZ : I = c.s.fr.Z := le_antisymm hsub hZleI
      rw [hIZ, show c.s.fr.Z = zpowers c.s.fr.z from rfl, Nat.card_zpowers, hzord]
    · right
      obtain ⟨u, huI, huZ⟩ := Set.not_subset.mp hsub
      have huE : u ∈ c.s.fr.E := hIE huI
      have hu1 : u ≠ 1 := by rintro rfl; exact huZ (Subgroup.one_mem _)
      have huz : u ≠ c.s.fr.z := by
        rintro rfl
        exact huZ (show c.s.fr.z ∈ c.s.fr.Z from Subgroup.mem_zpowers _)
      have hEZI : ∀ v ∈ c.s.fr.E, v ∉ c.s.fr.Z → v ∈ I := by
        intro v hvE hvZ
        have hv1 : v ≠ 1 := by rintro rfl; exact hvZ (Subgroup.one_mem _)
        have hvz : v ≠ c.s.fr.z := by
          rintro rfl
          exact hvZ (show c.s.fr.z ∈ c.s.fr.Z from Subgroup.mem_zpowers _)
        obtain ⟨n, hn, hnv⟩ := y56_NE_trans hb.hH u huE hu1 huz v hvE hv1 hvz
        have hmem : n * u * n⁻¹ ∈ I := hIstable n hn u huI
        rwa [hnv] at hmem
      have hEI : c.s.fr.E ≤ I := by
        intro v hvE
        by_cases hvZ : v ∈ c.s.fr.Z
        · exact hZleI hvZ
        · exact hEZI v hvE hvZ
      rw [le_antisymm hIE hEI, y7b_card_E hb.hH]
  rcases hIcase with hI2 | hI8
  · have hrel2 : (M4 c.e).relIndex (C4 c.s) = 2 := by rw [hrelI, hI2]
    have hmul := Subgroup.relIndex_mul_card (H := M4 c.e) (K := C4 c.s)
    rw [hrel2, inf_eq_left.mpr hM4leC4, y7b_card_C4 c hb] at hmul
    norm_num at hmul
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num]
    omega
  · exfalso
    have hrel8 : (M4 c.e).relIndex (C4 c.s) = 8 := by rw [hrelI, hI8]
    have hmul := Subgroup.relIndex_mul_card (H := M4 c.e) (K := C4 c.s)
    rw [hrel8, inf_eq_left.mpr hM4leC4, y7b_card_C4 c hb] at hmul
    have hcardM4 : Nat.card ↥(M4 c.e) = 2 ^ 4 := by
      rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
      omega
    have hV2leM4 : V2 c.e ≤ M4 c.e := by
      unfold V2
      exact inf_le_right
    have hV2eqM4 : V2 c.e = M4 c.e := by
      apply Subgroup.eq_of_le_of_card_ge hV2leM4
      rw [hcardM4, hb.h72.1.2.2.2.1]
    have hM4leM3 : M4 c.e ≤ M3 c.s := by
      rw [← hV2eqM4]
      exact inf_le_left
    have hEleH : c.s.fr.E ≤ c.s.H :=
      (y56_E_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS)
    have hEleM3 : c.s.fr.E ≤ M3 c.s := (y7b_E_le_M4 c hb).trans hM4leM3
    have hEleF : c.s.fr.E ≤ c.s.fr.F := by
      rw [← y54_H_inf_M3 c.toCtx5 hb.hH]
      exact le_inf hEleH hEleM3
    have h4 : Nat.card ↥(c.s.fr.E ⊓ c.s.fr.F) = 4 := by
      rw [y7b_E_inf_F hb.hH, y7b_card_V hb.hH]
    rw [inf_eq_left.mpr hEleF, y7b_card_E hb.hH] at h4
    norm_num at h4

theorem y7b_phi_M4 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ f ∈ c.s.fr.E, ∃ m ∈ M4 c.e, ⁅m, c.s.t⁆ = f := by
  have hM4leC4 : M4 c.e ≤ C4 c.s := by
    unfold M4 centIn
    exact inf_le_left
  have hM4Y : M4 c.e ≤ e4Y c.s := hM4leC4.trans (y56_C4_cand c.toCtx5 hb.hH).2.1
  have hEleH : c.s.fr.E ≤ c.s.H :=
    (y56_E_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS)
  let ψ : ↥(M4 c.e) →* ↥(c.s.fr.E) :=
    MonoidHom.mk' (fun m => ⟨f3phi c.s (m : G), y56_phi_mem hb.hH (m : G) (hM4Y m.2)⟩)
      (fun a b => Subtype.ext (y56_phi_mul hb.hH (a : G) (hM4Y a.2) (b : G) (hM4Y b.2)))
  have hker : ψ.ker = (c.s.fr.E).subgroupOf (M4 c.e) := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hφ : f3phi c.s (m : G) = 1 := by
        change (ψ m : G) = 1
        exact congrArg (fun x : ↥(c.s.fr.E) => (x : G)) h
      have hmQ : (m : G) ∈ e4Q c.s :=
        y56_M_inf_ker (c := c.toCtx5) hb.hH (y56_C4_cand c.toCtx5 hb.hH) (m : G)
          (hM4leC4 m.2) hφ
      have htH : c.s.t ∈ c.s.H := by
        show c.s.t ∈ Subgroup.centralizer ({c.s.t} : Set G)
        exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have hQH : e4Q c.s ≤ c.s.H := sup_le hEleH (Subgroup.zpowers_le.mpr htH)
      have : (m : G) ∈ c.s.H ⊓ M4 c.e := ⟨hQH hmQ, m.2⟩
      rwa [y7b_H_inf_M4 c hb] at this
    · intro hm
      have hmE : (m : G) ∈ c.s.fr.E := hm
      apply Subtype.ext
      show f3phi c.s (m : G) = 1
      have hcomm : Commute (m : G) c.s.t := y56_t_comm_E c.s (m : G) hmE
      unfold f3phi
      rw [hcomm.eq]
      group
  have hcard_ker : Nat.card ↥ψ.ker = 8 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (y7b_E_le_M4 c hb)).toEquiv,
      y7b_card_E hb.hH]
  have hcard_range : Nat.card ↥ψ.range = 8 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hcard_ker, y7b_card_M4 c hb] at h
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num] at h
    omega
  have hrange_top : ψ.range = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [hcard_range, Subgroup.card_top, y7b_card_E hb.hH]
  intro f hf
  have hf' : (⟨f, hf⟩ : ↥(c.s.fr.E)) ∈ ψ.range := by
    rw [hrange_top]
    exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hf'
  refine ⟨(m : G), m.2, ?_⟩
  have : f3phi c.s (m : G) = f := congrArg (fun x : ↥(c.s.fr.E) => (x : G)) hm
  exact this

end CFSG.OddStandard.HigherRank.YamadaG23
