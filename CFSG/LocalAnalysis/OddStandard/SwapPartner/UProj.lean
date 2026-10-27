module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UBasic
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGDefs

import CFSG.LocalAnalysis.OddStandard.SwapPartner.UTstar
import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGCent

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G}

private theorem u_g_x1_g (F : UFrame z ι ιd) : gElt ιd * ι τ₀ * gElt ιd = z := by
  have h : gElt ιd * (gElt ιd * z * gElt ιd) * gElt ιd = z := by
    calc gElt ιd * (gElt ιd * z * gElt ιd) * gElt ιd
        = (gElt ιd * gElt ιd) * z * (gElt ιd * gElt ιd) := by group
      _ = z := by rw [F.g_sq]; group
  rwa [F.g_z_g] at h

private theorem u_x2_orderOf (F : UFrame z ι ιd) : orderOf (z * ι τ₀) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ (F.d8).x_ne
  rw [pow_two]
  exact (F.d8).x_sq

private theorem u_zpowers_x2 (F : UFrame z ι ιd) {d : G}
    (hd : d ∈ Subgroup.zpowers (z * ι τ₀)) : d = 1 ∨ d = z * ι τ₀ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd
  have h2 : ((orderOf (z * ι τ₀) : ℕ) : ℤ) = 2 := by rw [u_x2_orderOf F]; norm_num
  have hmod : (z * ι τ₀) ^ k = (z * ι τ₀) ^ (k % (2 : ℤ)) := by
    rw [← zpow_mod_orderOf (z * ι τ₀) k, h2]
  have hk2 : k % (2 : ℤ) = 0 ∨ k % (2 : ℤ) = 1 := by
    have h0 : 0 ≤ k % (2 : ℤ) := Int.emod_nonneg k (by norm_num)
    have hlt : k % (2 : ℤ) < 2 := Int.emod_lt_of_pos k (by norm_num)
    omega
  rw [← hk]
  rcases hk2 with h | h
  · left; rw [hmod, h]; simp
  · right; rw [hmod, h]; simp

private theorem u_x2_comm_CEgrp (F : UFrame z ι ιd) {c : G} (hc : c ∈ CEgrp z ι) :
    (z * ι τ₀) * c = c * (z * ι τ₀) := by
  obtain ⟨hcz, hcx⟩ := Subgroup.mem_inf.mp hc
  have hz : z * c = c * z := (mem_centralizer_singleton_iff.mp hcz).symm
  have hx : ι τ₀ * c = c * ι τ₀ := (mem_centralizer_singleton_iff.mp hcx).symm
  calc (z * ι τ₀) * c = z * (ι τ₀ * c) := by group
    _ = z * (c * ι τ₀) := by rw [hx]
    _ = (z * c) * ι τ₀ := by group
    _ = (c * z) * ι τ₀ := by rw [hz]
    _ = c * (z * ι τ₀) := by group

private theorem u_conj_form (F : UFrame z ι ιd) (i j : Fin 2) (ρ : Perm (Fin 8)) :
    gElt ιd * (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι (liftS8 ρ)) * gElt ιd =
      (ι τ₀) ^ (i : ℕ) * z ^ (j : ℕ) * ι (liftS8 ρ) := by
  have hgz : MulAut.conj (gElt ιd) z = ι τ₀ := by
    rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right F.g_sq]
    exact F.g_z_g
  have hgx : MulAut.conj (gElt ιd) (ι τ₀) = z := by
    rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right F.g_sq]
    exact u_g_x1_g F
  have hgs : MulAut.conj (gElt ιd) (ι (liftS8 ρ)) = ι (liftS8 ρ) := by
    rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right F.g_sq, F.g_comm ρ, mul_assoc,
      F.g_sq, mul_one]
  calc gElt ιd * (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι (liftS8 ρ)) * gElt ιd
      = MulAut.conj (gElt ιd) (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι (liftS8 ρ)) := by
        rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right F.g_sq]
    _ = MulAut.conj (gElt ιd) (z ^ (i : ℕ)) * MulAut.conj (gElt ιd) ((ι τ₀) ^ (j : ℕ)) *
          MulAut.conj (gElt ιd) (ι (liftS8 ρ)) := by rw [map_mul, map_mul]
    _ = (MulAut.conj (gElt ιd) z) ^ (i : ℕ) * (MulAut.conj (gElt ιd) (ι τ₀)) ^ (j : ℕ) *
          MulAut.conj (gElt ιd) (ι (liftS8 ρ)) := by rw [map_pow, map_pow]
    _ = (ι τ₀) ^ (i : ℕ) * z ^ (j : ℕ) * ι (liftS8 ρ) := by rw [hgz, hgx, hgs]

private theorem u_fin2_eq_of_comm (F : UFrame z ι ιd) {i j : Fin 2}
    (h : (ι τ₀) ^ (i : ℕ) * z ^ (j : ℕ) = z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ)) : i = j := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at h ⊢
  all_goals first
    | rfl
    | (exfalso; first | exact F.cent.ne_z τ₀ h | exact F.cent.ne_z τ₀ h.symm)

private theorem u_x2_mem_Egrp (F : UFrame z ι ιd) : z * ι τ₀ ∈ Egrp z ι := by
  rw [mem_Egrp_iff F.cent]
  exact ⟨1, 1, by simp⟩

private theorem u_inf_x2_Siggrp (F : UFrame z ι ιd) :
    Subgroup.zpowers (z * ι τ₀) ⊓ Siggrp ι = ⊥ := by
  refine eq_bot_iff.mpr ?_
  intro t ht
  obtain ⟨ht1, ht2⟩ := Subgroup.mem_inf.mp ht
  have htE : t ∈ Egrp z ι := (Subgroup.zpowers_le.mpr (u_x2_mem_Egrp F)) ht1
  have hbot : t ∈ (⊥ : Subgroup G) := by
    rw [← Egrp_inf_Siggrp F.cent]
    exact Subgroup.mem_inf.mpr ⟨htE, ht2⟩
  exact Subgroup.mem_bot.mp hbot

private theorem u_card_Siggrp (F : UFrame z ι ιd) : Nat.card (Siggrp ι) = 40320 := by
  have h : Nat.card (Siggrp ι) = Nat.card (Perm (Fin 8)) := by
    show Nat.card ((ι.comp liftS8).range) = Nat.card (Perm (Fin 8))
    exact (Nat.card_congr (MonoidHom.ofInjective (injective_comp_liftS8 F)).toEquiv).symm
  rw [h, Nat.card_perm, Nat.card_fin]
  norm_num

private theorem u_le_T (F : UFrame z ι ιd) {B : Subgroup G} (hB : B ≤ CEgrp z ι)
    (hg : ∀ b ∈ B, gElt ιd * b = b * gElt ιd) :
    B ≤ Subgroup.zpowers (z * ι τ₀) ⊔ Siggrp ι := by
  intro b hb
  have hgbg : gElt ιd * b * gElt ιd = b := by
    calc gElt ιd * b * gElt ιd = b * gElt ιd * gElt ιd := by rw [hg b hb]
      _ = b * (gElt ιd * gElt ιd) := by group
      _ = b := by rw [F.g_sq, mul_one]
  obtain ⟨i, j, ρ, hb_eq⟩ := (mem_CEgrp_iff F.cent).mp (hB hb)
  rw [hb_eq] at hgbg
  have heq : (ι τ₀) ^ (i : ℕ) * z ^ (j : ℕ) * ι (liftS8 ρ) =
      z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι (liftS8 ρ) :=
    (u_conj_form F i j ρ).symm.trans hgbg
  have hij : i = j := u_fin2_eq_of_comm F (mul_right_cancel heq)
  rw [hb_eq, hij]
  fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one]
  · exact Subgroup.mem_sup_right ((mem_Siggrp_iff).mpr ⟨ρ, rfl⟩)
  · exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩))
      (Subgroup.mem_sup_right ((mem_Siggrp_iff).mpr ⟨ρ, rfl⟩))

theorem exists_eq_mul_sigma_of_card_eq (F : UFrame z ι ιd) {B : Subgroup G} (hB : B ≤ CEgrp z ι)
    (hg : ∀ b ∈ B, gElt ιd * b = b * gElt ιd) (hx : z * ι τ₀ ∉ B) (hcard : Nat.card ↥B = 40320)
    (ρ : Perm (Fin 8)) :
    ∃ b ∈ B, b = ι (liftS8 ρ) ∨ b = (z * ι τ₀) * ι (liftS8 ρ) := by
  classical
  have hBT : B ≤ Subgroup.zpowers (z * ι τ₀) ⊔ Siggrp ι := u_le_T F hB hg
  have hcommT : ∀ d ∈ Subgroup.zpowers (z * ι τ₀), ∀ q ∈ Siggrp ι, d * q = q * d := by
    intro d hd q hq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd
    have hcq : Commute (z * ι τ₀) q := u_x2_comm_CEgrp F (Siggrp_le_CEgrp F.cent hq)
    rw [← hk]
    exact (hcq.zpow_left k).eq
  have hcardT : Nat.card ↥(Subgroup.zpowers (z * ι τ₀) ⊔ Siggrp ι) = 80640 := by
    rw [card_sup_of_commute hcommT (u_inf_x2_Siggrp F), Nat.card_zpowers, u_x2_orderOf F,
      u_card_Siggrp F]
  have hcommB : ∀ d ∈ Subgroup.zpowers (z * ι τ₀), ∀ b ∈ B, d * b = b * d := by
    intro d hd b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd
    have hcb : Commute (z * ι τ₀) b := u_x2_comm_CEgrp F (hB hb)
    rw [← hk]
    exact (hcb.zpow_left k).eq
  have hDQB : Subgroup.zpowers (z * ι τ₀) ⊓ B = ⊥ := by
    refine eq_bot_iff.mpr ?_
    intro t ht
    obtain ⟨ht1, ht2⟩ := Subgroup.mem_inf.mp ht
    rcases u_zpowers_x2 F ht1 with h | h
    · exact Subgroup.mem_bot.mpr h
    · exact absurd (h ▸ ht2) hx
  have hcardB' : Nat.card ↥(Subgroup.zpowers (z * ι τ₀) ⊔ B) = 80640 := by
    rw [card_sup_of_commute hcommB hDQB, Nat.card_zpowers, u_x2_orderOf F, hcard]
  have hB'T : Subgroup.zpowers (z * ι τ₀) ⊔ B = Subgroup.zpowers (z * ι τ₀) ⊔ Siggrp ι := by
    haveI : Finite ↥(Subgroup.zpowers (z * ι τ₀) ⊔ Siggrp ι) :=
      Nat.finite_of_card_ne_zero (by rw [hcardT]; norm_num)
    refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hBT) ?_
    rw [hcardT, hcardB']
  have hs_mem : ι (liftS8 ρ) ∈ Subgroup.zpowers (z * ι τ₀) ⊔ B := by
    rw [hB'T]
    exact Subgroup.mem_sup_right ((mem_Siggrp_iff).mpr ⟨ρ, rfl⟩)
  obtain ⟨d, hd, b, hb, hdbs⟩ := (mem_sup_iff_of_commute hcommB).mp hs_mem
  rcases u_zpowers_x2 F hd with hd1 | hdx2
  · refine ⟨b, hb, Or.inl ?_⟩
    rw [hd1, one_mul] at hdbs
    exact hdbs.symm
  · refine ⟨b, hb, Or.inr ?_⟩
    have hx2inv : (z * ι τ₀)⁻¹ = z * ι τ₀ := inv_eq_of_mul_eq_one_right (F.d8).x_sq
    rw [hdx2] at hdbs
    have h1 : (z * ι τ₀) * b = ι (liftS8 ρ) := hdbs.symm
    calc b = (z * ι τ₀)⁻¹ * ((z * ι τ₀) * b) := by group
      _ = (z * ι τ₀)⁻¹ * ι (liftS8 ρ) := by rw [h1]
      _ = (z * ι τ₀) * ι (liftS8 ρ) := by rw [hx2inv]

end CFSG.OddStandard.AltStdSec.SwapPartner
