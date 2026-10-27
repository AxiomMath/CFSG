module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3c

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7bd_comm_mem {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

private lemma y7bd_conj_mem_closure {a b w g : G}
    (ha : g * a * g⁻¹ = a) (hb : g * b * g⁻¹ = b)
    (hw : w ∈ Subgroup.closure ({a, b} : Set G)) :
    g * w * g⁻¹ ∈ Subgroup.closure ({a, b} : Set G) := by
  refine Subgroup.closure_induction (p := fun w _ => g * w * g⁻¹ ∈
    Subgroup.closure ({a, b} : Set G)) ?_ ?_ ?_ ?_ hw
  · intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · rw [ha]; exact Subgroup.subset_closure (by simp)
    · rw [hb]; exact Subgroup.subset_closure (by simp)
  · simp
  · intro u v _ _ hu hv
    rw [show g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) from by group]
    exact Subgroup.mul_mem _ hu hv
  · intro u _ hu
    rw [show g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ from by group]
    exact Subgroup.inv_mem _ hu

private lemma y7bd_conj_zpow_eq {g z : G} (hz : g * z * g⁻¹ = z) (k : ℤ) :
    g * z ^ k * g⁻¹ = z ^ k := by
  rw [← conj_zpow (a := g) (b := z) (i := k), hz]

private lemma y7bd_zpow_two_eq_one_or_self {x : G} (hx : x ^ 2 = 1) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · left
    rw [orderOf_eq_one_iff.mp h1, one_zpow]
  · have hmod := zpow_mod_orderOf x k
    rw [h2] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [← hmod, show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0]
      simp
    · right
      rw [← hmod, show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1]
      simp

theorem y7b_g_comm_e0 (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    ⁅c.g, c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂⁆ = c.s.fr.b₁ * c.s.fr.b₂ * c.s.fr.z := by
  obtain ⟨-, -, hact, hg2, -⟩ := c.g_spec hRT
  obtain ⟨ha1, ha2, hb1, -, -, -⟩ := y5_g_swap hb.hH hg2 hact
  have hsrel := s3_srel hb.hH.hS hb.hH.hZ c.s
  have hz2 : c.s.fr.z * c.s.fr.z = 1 := by rw [← pow_two]; exact hsrel.z_sq
  have ha1a2inv : c.s.fr.a₁ * c.s.fr.a₂⁻¹ = c.s.fr.a₂⁻¹ * c.s.fr.a₁ :=
    (commutatorElement_eq_one_iff_commute.mp hsrel.a1a2).inv_right.eq
  have hcomm_b : c.s.fr.b₁ * c.s.fr.b₂ = c.s.fr.b₂ * c.s.fr.b₁ :=
    commutatorElement_eq_one_iff_mul_comm.mp hsrel.b1b2
  have hconj1 : c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₁⁻¹ = c.s.fr.z * c.s.fr.b₁ := by
    have h := hsrel.comm1
    rw [commutatorElement_def] at h
    rw [← h]; group
  have hconj2 : c.s.fr.a₂ * c.s.fr.b₂ * c.s.fr.a₂⁻¹ = c.s.fr.z * c.s.fr.b₂ := by
    have h := hsrel.comm2
    rw [commutatorElement_def] at h
    rw [← h]; group
  have hz_inv : c.s.fr.z⁻¹ = c.s.fr.z := inv_eq_of_mul_eq_one_right hz2
  have hb1_inv_z : c.s.fr.b₁⁻¹ = c.s.fr.b₁ * c.s.fr.z := by
    rw [inv_eq_iff_mul_eq_one]
    rw [← mul_assoc, ← pow_two]
    change c.s.fr.z * c.s.fr.z = 1
    rw [← pow_two]
    exact hsrel.z_sq
  have hzbinv : (c.s.fr.z * c.s.fr.b₁)⁻¹ = c.s.fr.b₁ := by
    rw [mul_inv_rev, hb1_inv_z, hz_inv]
    rw [mul_assoc, hz2, mul_one]
  have hb1inv : c.s.fr.a₁ * c.s.fr.b₁⁻¹ * c.s.fr.a₁⁻¹ = c.s.fr.b₁ := by
    rw [show c.s.fr.a₁ * c.s.fr.b₁⁻¹ * c.s.fr.a₁⁻¹
        = (c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₁⁻¹)⁻¹ from by group, hconj1]
    exact hzbinv
  have hzb1 : c.s.fr.z * c.s.fr.b₁ = c.s.fr.b₁ * c.s.fr.z := by
    change c.s.fr.b₁ ^ 2 * c.s.fr.b₁ = c.s.fr.b₁ * c.s.fr.b₁ ^ 2
    group
  have hzb2 : c.s.fr.z * c.s.fr.b₂ = c.s.fr.b₂ * c.s.fr.z := by
    rw [← hsrel.b2_sq]; group
  have hz_comm : c.s.fr.z * (c.s.fr.b₁ * c.s.fr.b₂)
      = (c.s.fr.b₁ * c.s.fr.b₂) * c.s.fr.z := by
    rw [← mul_assoc, hzb1, mul_assoc, hzb2, ← mul_assoc]
  have hge : c.g * (c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂) * c.g⁻¹
      = c.s.fr.a₂ * c.s.fr.b₂ * c.s.fr.a₁ := by
    rw [show c.g * (c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂) * c.g⁻¹
        = (c.g * c.s.fr.a₁ * c.g⁻¹) * (c.g * c.s.fr.b₁ * c.g⁻¹)
          * (c.g * c.s.fr.a₂ * c.g⁻¹) from by group, ha1, hb1, ha2]
  rw [commutatorElement_def, hge]
  have hmain : c.s.fr.a₂ * c.s.fr.b₂ * c.s.fr.a₁
      * (c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂)⁻¹
      = c.s.fr.b₁ * c.s.fr.b₂ * c.s.fr.z := by
    rw [show (c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂)⁻¹
        = c.s.fr.a₂⁻¹ * (c.s.fr.b₁⁻¹ * c.s.fr.a₁⁻¹) from by group]
    rw [show c.s.fr.a₂ * c.s.fr.b₂ * c.s.fr.a₁
        * (c.s.fr.a₂⁻¹ * (c.s.fr.b₁⁻¹ * c.s.fr.a₁⁻¹))
        = c.s.fr.a₂ * c.s.fr.b₂ * (c.s.fr.a₁ * c.s.fr.a₂⁻¹)
          * (c.s.fr.b₁⁻¹ * c.s.fr.a₁⁻¹) from by group]
    rw [ha1a2inv]
    rw [show c.s.fr.a₂ * c.s.fr.b₂ * (c.s.fr.a₂⁻¹ * c.s.fr.a₁)
        * (c.s.fr.b₁⁻¹ * c.s.fr.a₁⁻¹)
        = (c.s.fr.a₂ * c.s.fr.b₂ * c.s.fr.a₂⁻¹)
          * (c.s.fr.a₁ * c.s.fr.b₁⁻¹ * c.s.fr.a₁⁻¹) from by group]
    rw [hconj2, hb1inv]
    rw [show (c.s.fr.z * c.s.fr.b₂) * c.s.fr.b₁
        = c.s.fr.z * (c.s.fr.b₁ * c.s.fr.b₂) from by rw [mul_assoc, ← hcomm_b]]
    rw [hz_comm]
  rw [hmain]

theorem y7b_T_inf_cs_le_A (c : Ctx7 G L) (hb : B5Std c) :
    c.s.T ⊓ centralizerSection (M5 c.e) (V1 c.e) ≤ c.s.fr.A := by
  intro x hx
  obtain ⟨hxT, hxcs⟩ := Subgroup.mem_inf.mp hx
  simp only [centralizerSection, Set.mem_setOf_eq] at hxcs
  obtain ⟨_, _, hxcomm⟩ := hxcs
  by_cases hxR : x ∈ c.s.R
  · exact y7b_R_cs_le_A c hb x hxR hxcomm
  · exfalso
    have hRT : c.s.R ≠ c.s.T := fun h => hxR (by rw [h]; exact hxT)
    obtain ⟨hgT, hgnR, hact, hg2, hgd⟩ := c.g_spec hRT
    obtain ⟨-, -, -, -, hz, -⟩ := y5_g_swap hb.hH hg2 hact
    have hg_inv : c.g⁻¹ = c.g := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hg2)
    have hgnormV1 : ∀ v ∈ V1 c.e, c.g * v * c.g⁻¹ ∈ V1 c.e := by
      intro v hv
      rw [c.hV] at hv ⊢
      exact y7bd_conj_mem_closure hz hgd hv
    rcases y5_T_cosets hb.hH x hxT c.g hgT with h1 | h2 | h3
    · exact hxR h1
    · exact hgnR h2
    · obtain ⟨r, hrR, hxr⟩ : ∃ r ∈ c.s.R, x = c.g * r :=
        ⟨(x⁻¹ * c.g)⁻¹, c.s.R.inv_mem h3, by group⟩
      obtain ⟨y, hyS, hy⟩ := s3_R_cases c.s hb.hH.hS hb.hH.h31 r hrR
      have hcomm_tr : ∀ w ∈ c.s.fr.S, ⁅w, r⁆ = ⁅w, y⁆ := by
        intro w hw
        rcases hy with h | h
        · rw [h]
        · rw [h, commutatorElement_mul_right_eq_mul_conj]
          have hwt : ⁅w, c.s.t⁆ = 1 :=
            commutatorElement_eq_one_iff_mul_comm.mpr (s3_comm_t_of_mem_L c.s (s3_S_le_L c.s hw))
          rw [hwt]
          group
      have hyA : y ∈ c.s.fr.A := by
        apply y7b_CF hb.hH y hyS
        intro f hf
        have hfS : f ∈ c.s.fr.S := (s3_F_le_A c.s).trans (s3_A_le_S c.s) hf
        have hfM5 : f ∈ M5 c.e := by
          unfold M5 M3
          exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hf)
        have hfxV1 : ⁅f, x⁆ ∈ V1 c.e := hxcomm f hfM5
        have hfg : ⁅f, c.g⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          calc f * c.g = (c.g * f * c.g⁻¹) * c.g := by
                rw [y5_g_cent_F hb.hH hg2 hact f hf]
            _ = c.g * f := by group
        have hdecomp : ⁅f, x⁆ = c.g * ⁅f, r⁆ * c.g⁻¹ := by
          rw [hxr, commutatorElement_mul_right_eq_mul_conj, hfg]
          group
        have heq : c.g * ⁅f, x⁆ * c.g = ⁅f, y⁆ := by
          rw [hdecomp, ← hcomm_tr f hfS]
          rw [show c.g * (c.g * ⁅f, r⁆ * c.g⁻¹) * c.g
              = (c.g * c.g) * ⁅f, r⁆ * (c.g⁻¹ * c.g) from by group, ← pow_two, hg2]
          group
        have hfyV1 : ⁅f, y⁆ ∈ V1 c.e := by
          rw [← heq]
          simpa only [hg_inv] using hgnormV1 ⁅f, x⁆ hfxV1
        have hfyS : ⁅f, y⁆ ∈ c.s.fr.S := y7bd_comm_mem hfS hyS
        have hfyZ : ⁅f, y⁆ ∈ c.s.fr.Z := by
          have hmem : ⁅f, y⁆ ∈ c.s.H ⊓ V1 c.e :=
            Subgroup.mem_inf.mpr ⟨c.s.sylow_T.1 (s3_S_le_T c.s hfyS), hfyV1⟩
          rwa [y7b_H_inf_V1 c hb] at hmem
        rw [← commutatorElement_inv]
        exact c.s.fr.Z.inv_mem hfyZ
      have he0E : y56e0 c.s ∈ c.s.fr.E := y56_e0_mem_E c.s
      have he0A : y56e0 c.s ∈ c.s.fr.A := s3_E_le_A c.s he0E
      have he0S : y56e0 c.s ∈ c.s.fr.S := s3_A_le_S c.s he0A
      have he0M5 : y56e0 c.s ∈ M5 c.e := by
        unfold M5
        exact Subgroup.mem_sup_right (y7b_E_le_M4 c hb he0E)
      have he0xV1 : ⁅y56e0 c.s, x⁆ ∈ V1 c.e := hxcomm _ he0M5
      have he0xZ : ⁅y56e0 c.s, x⁆ ∈ c.s.fr.Z := by
        have hmem : ⁅y56e0 c.s, x⁆ ∈ c.s.H ⊓ V1 c.e :=
          Subgroup.mem_inf.mpr
            ⟨y7bd_comm_mem (c.s.sylow_T.1 (s3_S_le_T c.s he0S)) (c.s.sylow_T.1 hxT),
              he0xV1⟩
        rwa [y7b_H_inf_V1 c hb] at hmem
      have hdecomp0 : ⁅y56e0 c.s, x⁆ = ⁅y56e0 c.s, c.g⁆ * (c.g * ⁅y56e0 c.s, r⁆ * c.g⁻¹) := by
        rw [hxr, commutatorElement_mul_right_eq_mul_conj]
        group
      have he0r_eq : ⁅y56e0 c.s, r⁆ = ⁅y56e0 c.s, y⁆ := hcomm_tr _ he0S
      have he0yZ : ⁅y56e0 c.s, y⁆ ∈ c.s.fr.Z :=
        (lfactsA_of_setting hb.hH.hS hb.hH.hZ c.s).comm_A _ he0A _ hyA
      have hconjZ : c.g * ⁅y56e0 c.s, y⁆ * c.g⁻¹ ∈ c.s.fr.Z := by
        rw [SFrame.Z] at he0yZ ⊢
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp he0yZ
        rw [← hk, y7bd_conj_zpow_eq hz k]
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
      have he0gZ : ⁅y56e0 c.s, c.g⁆ ∈ c.s.fr.Z := by
        have h : ⁅y56e0 c.s, c.g⁆
            = ⁅y56e0 c.s, x⁆ * (c.g * ⁅y56e0 c.s, y⁆ * c.g⁻¹)⁻¹ := by
          rw [hdecomp0, he0r_eq]
          group
        rw [h]
        exact c.s.fr.Z.mul_mem he0xZ (c.s.fr.Z.inv_mem hconjZ)
      have hge0 : ⁅y56e0 c.s, c.g⁆ = (c.s.fr.b₁ * c.s.fr.b₂ * c.s.fr.z)⁻¹ := by
        rw [← commutatorElement_inv, y7b_g_comm_e0 c hb hRT]
      have hb12Z : c.s.fr.b₁ * c.s.fr.b₂ ∈ c.s.fr.Z := by
        rw [hge0] at he0gZ
        have hb12z : c.s.fr.b₁ * c.s.fr.b₂ * c.s.fr.z ∈ c.s.fr.Z := by
          simpa only [inv_inv] using c.s.fr.Z.inv_mem he0gZ
        have hzZ : c.s.fr.z ∈ c.s.fr.Z := Subgroup.mem_zpowers c.s.fr.z
        have heq : c.s.fr.b₁ * c.s.fr.b₂
            = (c.s.fr.b₁ * c.s.fr.b₂ * c.s.fr.z) * c.s.fr.z⁻¹ := by group
        rw [heq]
        exact c.s.fr.Z.mul_mem hb12z (c.s.fr.Z.inv_mem hzZ)
      obtain ⟨-, -, hw1, -, hwz, -⟩ := y56_v0 hb.hH
      have hzz : c.s.fr.z ^ 2 = 1 := (s3_srel hb.hH.hS hb.hH.hZ c.s).z_sq
      rw [SFrame.Z, Subgroup.mem_zpowers_iff] at hb12Z
      obtain ⟨k, hk⟩ := hb12Z
      rcases y7bd_zpow_two_eq_one_or_self hzz k with hk1 | hkz
      · exact hw1 (by rw [← hk, hk1])
      · exact hwz (by rw [← hk, hkz])

end CFSG.OddStandard.HigherRank.YamadaG23
