module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BFb
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B2a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B2b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B2c

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem eq_of_le_of_le_of_card_eq_two {Z K V : Subgroup G}
    (hZK : Z ≤ K) (hKV : K ≤ V) (hV : Nat.card ↥V = 4) (hZ : Nat.card ↥Z = 2)
    (hne : K ≠ V) : K = Z := by
  have hZV : Z ≤ V := hZK.trans hKV
  have hrelZV : Z.relIndex V = 2 := by
    have h := Subgroup.relIndex_mul_card (H := Z) (K := V)
    rw [inf_of_le_left hZV, hV, hZ] at h
    omega
  have hprod := Subgroup.relIndex_mul_relIndex (H := Z) (K := K) (L := V) hZK hKV
  rw [hrelZV] at hprod
  have hKrelV : K.relIndex V = 2 := by
    have hdvd : K.relIndex V ∣ 2 :=
      ⟨Z.relIndex K, by rw [mul_comm]; exact hprod.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (Subgroup.relIndex_eq_one.mp h1) fun hVK => hne (le_antisymm hKV hVK)
    · exact h2
  have hZKrel : Z.relIndex K = 1 := by
    rw [hKrelV] at hprod
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hZKrel) hZK

theorem y7b_H_inf_V1 (c : Ctx7 G L) (hb : B5Std c) : c.s.H ⊓ V1 c.e = c.s.fr.Z := by
  have hcardV1 : Nat.card ↥(V1 c.e) = 4 := y7b_card_V1 c hb
  have hzsq : c.s.fr.z ^ 2 = 1 := (s3_srel hb.hH.hS hb.hH.hZ c.s).z_sq
  have hzne : c.s.fr.z ≠ 1 := y54_z_ne_one hb.hH
  have hcardZ : Nat.card ↥c.s.fr.Z = 2 := by
    rw [SFrame.Z, Nat.card_zpowers]
    exact orderOf_eq_prime hzsq hzne
  have hzV1 : c.s.fr.z ∈ V1 c.e := by
    rw [c.hV]; exact Subgroup.subset_closure (by simp)
  have hdV1 : c.d ∈ V1 c.e := by
    rw [c.hV]; exact Subgroup.subset_closure (by simp)
  have hzH : c.s.fr.z ∈ c.s.H := s3_L_le_H c.s hb.hH.hS (s3_z_mem_L c.s)
  have hZle : c.s.fr.Z ≤ c.s.H ⊓ V1 c.e := by
    rw [SFrame.Z]
    exact le_inf (Subgroup.zpowers_le.mpr hzH) (Subgroup.zpowers_le.mpr hzV1)
  have hd_not_H : c.d ∉ c.s.H := by
    intro hd
    have hcomm : c.d * c.s.t = c.s.t * c.d :=
      (Subgroup.mem_centralizer_iff.mp hd c.s.t (by simp)).symm
    have h1 : c.s.t = c.s.fr.z * c.s.t := by
      have h := y5_dtd hb.hH
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one] at h
      exact h
    have h2 : (1 : G) * c.s.t = c.s.fr.z * c.s.t := by rw [one_mul]; exact h1
    exact hzne (mul_right_cancel h2).symm
  have hKneV1 : c.s.H ⊓ V1 c.e ≠ V1 c.e := by
    intro heq
    have hdK : c.d ∈ c.s.H ⊓ V1 c.e := by rw [heq]; exact hdV1
    exact hd_not_H (Subgroup.mem_inf.mp hdK).1
  exact eq_of_le_of_le_of_card_eq_two hZle inf_le_right hcardV1 hcardZ hKneV1

theorem y7b_EF_le_M5 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.fr.A ⊓ c.s.fr.B ≤ M5 c.e := by
  rw [← y7b_EF_eq hb.hH]
  exact sup_le ((y7b_E_le_M4 c hb).trans le_sup_right) (le_sup_right.trans le_sup_left)

theorem y7b_H_inf_M5 (c : Ctx7 G L) (hb : B6Std c) :
    c.s.H ⊓ M5 c.e = c.s.fr.A ⊓ c.s.fr.B := by
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ ?_
    · calc c.s.H ⊓ M5 c.e ≤ c.s.H ⊓ M6 c.e :=
          inf_le_inf le_rfl (y7b_M5_le_M6 c hb.toB5Std)
        _ = c.s.fr.A := hb.h71.2.1.2.1
    · calc c.s.H ⊓ M5 c.e ≤ c.s.H ⊓ M7 c.s :=
          inf_le_inf le_rfl (y7b_M5_le_M7 c hb)
        _ = c.s.fr.B := hb.h75.1.2.1
  · refine le_inf ((inf_le_left.trans (s3_A_le_S c.s)).trans
      ((s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS))) (y7b_EF_le_M5 c hb.toB5Std)

theorem y7b_R_inf_M5 (c : Ctx7 G L) (hb : B6Std c) :
    c.s.R ⊓ M5 c.e = c.s.fr.A ⊓ c.s.fr.B := by
  refine le_antisymm ?_ ?_
  · calc c.s.R ⊓ M5 c.e ≤ c.s.H ⊓ M5 c.e :=
        inf_le_inf (c.s.R_le_T.trans c.s.sylow_T.1) le_rfl
      _ = c.s.fr.A ⊓ c.s.fr.B := y7b_H_inf_M5 c hb
  · exact le_inf ((inf_le_left.trans (s3_A_le_S c.s)).trans c.s.S_le_R)
      (y7b_EF_le_M5 c hb.toB5Std)

private theorem inf_M5_eq (c : Ctx7 G L) (hb : B6Std c) {X : Subgroup G}
    (hXH : X ≤ c.s.H) (hEFX : c.s.fr.A ⊓ c.s.fr.B ≤ X) :
    X ⊓ M5 c.e = c.s.fr.A ⊓ c.s.fr.B := by
  refine le_antisymm ?_ ?_
  · calc X ⊓ M5 c.e ≤ c.s.H ⊓ M5 c.e := inf_le_inf hXH le_rfl
      _ = c.s.fr.A ⊓ c.s.fr.B := y7b_H_inf_M5 c hb
  · exact le_inf hEFX (y7b_EF_le_M5 c hb.toB5Std)

theorem y7b_card_R5 (c : Ctx7 G L) (hb : B6Std c) : Nat.card ↥(R5 c.e) = 2 ^ 11 := by
  have h := card_sup_mul_card_inf_of_le_normalizer (H := c.s.R) (K := M5 c.e)
    (y7b_R_le_NM5 c hb.toB5Std)
  rw [y7b_R_inf_M5 c hb, y7b_card_AB hb.hH, y7b_card_R hb.hH,
    y7b_card_M5 c hb.toB5Std] at h
  show Nat.card ↥(c.s.R ⊔ M5 c.e) = 2 ^ 11
  norm_num at h ⊢
  omega

theorem y7b_R5_isPGroup (c : Ctx7 G L) (hb : B6Std c) : IsPGroup 2 ↥(R5 c.e) :=
  IsPGroup.of_card (y7b_card_R5 c hb)

theorem y7b_card_AM5 (c : Ctx7 G L) (hb : B6Std c) : Nat.card ↥(AM5 c.e) = 2 ^ 9 := by
  have hXH : c.s.fr.A ≤ c.s.H :=
    (s3_A_le_S c.s).trans ((s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS))
  have hinf := inf_M5_eq c hb hXH inf_le_left
  have hrel : c.s.fr.A ≤ normalizer (M5 c.e : Set G) :=
    (s3_A_le_S c.s).trans (c.s.S_le_R.trans (y7b_R_le_NM5 c hb.toB5Std))
  have h := card_sup_mul_card_inf_of_le_normalizer (H := c.s.fr.A) (K := M5 c.e) hrel
  rw [hinf, y7b_card_AB hb.hH, y56_card_A hb.hH, y7b_card_M5 c hb.toB5Std] at h
  show Nat.card ↥(c.s.fr.A ⊔ M5 c.e) = 2 ^ 9
  norm_num at h ⊢
  omega

theorem y7b_card_BM5 (c : Ctx7 G L) (hb : B6Std c) : Nat.card ↥(BM5 c.e) = 2 ^ 9 := by
  have hXH : c.s.fr.B ≤ c.s.H :=
    (s3_B_le_S c.s).trans ((s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS))
  have hinf := inf_M5_eq c hb hXH inf_le_right
  have hrel : c.s.fr.B ≤ normalizer (M5 c.e : Set G) :=
    (s3_B_le_S c.s).trans (c.s.S_le_R.trans (y7b_R_le_NM5 c hb.toB5Std))
  have h := card_sup_mul_card_inf_of_le_normalizer (H := c.s.fr.B) (K := M5 c.e) hrel
  rw [hinf, y7b_card_AB hb.hH, y54_card_B hb.hH, y7b_card_M5 c hb.toB5Std] at h
  show Nat.card ↥(c.s.fr.B ⊔ M5 c.e) = 2 ^ 9
  norm_num at h ⊢
  omega

theorem y7b_card_SM5 (c : Ctx7 G L) (hb : B6Std c) : Nat.card ↥(SM5 c.e) = 2 ^ 10 := by
  have hXH : c.s.fr.S ≤ c.s.H := (s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS)
  have hinf := inf_M5_eq c hb hXH (inf_le_left.trans (s3_A_le_S c.s))
  have hrel : c.s.fr.S ≤ normalizer (M5 c.e : Set G) :=
    c.s.S_le_R.trans (y7b_R_le_NM5 c hb.toB5Std)
  have h := card_sup_mul_card_inf_of_le_normalizer (H := c.s.fr.S) (K := M5 c.e) hrel
  rw [hinf, y7b_card_AB hb.hH, y54_card_S hb.hH, y7b_card_M5 c hb.toB5Std] at h
  show Nat.card ↥(c.s.fr.S ⊔ M5 c.e) = 2 ^ 10
  norm_num at h ⊢
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
