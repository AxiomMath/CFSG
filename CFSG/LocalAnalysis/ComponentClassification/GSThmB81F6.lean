module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81F5
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81F4

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

theorem sigma_comm_P0 (hσp : d.sigma * d.p * d.sigma⁻¹ = h.a * d.p) (i : ℤ) :
    d.sigma * d.p ^ (2 * i) = d.p ^ (2 * i) * d.sigma ∧
      d.sigma * (d.p ^ (2 * i) * d.b) = d.p ^ (2 * i) * d.b * d.sigma := by
  obtain ⟨β, hP⟩ := d.pres
  have hσp' : d.sigma * d.p * d.sigma⁻¹ = d.p ^ (orderOf d.p / 2) * d.p := by rw [hσp, d.p_a]
  have h1 : d.sigma * d.p ^ (2 * i) * d.sigma⁻¹ = d.p ^ (2 * i) := by
    rw [Eight.MC.Pres.sigma_zpow hσp', (hP.a_zpow_eq_one_iff _).mpr ⟨i, by ring⟩, one_mul]
  have h2 : d.sigma * d.p ^ (2 * i) = d.p ^ (2 * i) * d.sigma := by
    calc d.sigma * d.p ^ (2 * i) = d.sigma * d.p ^ (2 * i) * d.sigma⁻¹ * d.sigma := by group
      _ = d.p ^ (2 * i) * d.sigma := by rw [h1]
  refine ⟨h2, ?_⟩
  rw [← mul_assoc, h2, mul_assoc, d.sigma_comm_b, ← mul_assoc]

theorem sigma_comm_R0_of_comm (hσp : d.sigma * d.p * d.sigma⁻¹ = d.p) {r : H}
    (hr : r ∈ d.R0) : d.sigma * r = r * d.sigma := by
  obtain ⟨β, hP⟩ := d.pres
  have hσp' : d.sigma * d.p = d.p * d.sigma := by
    calc d.sigma * d.p = d.sigma * d.p * d.sigma⁻¹ * d.sigma := by group
      _ = d.p * d.sigma := by rw [hσp]
  have hP' : ∀ w ∈ h.P, d.sigma * w = w * d.sigma := by
    intro w hw
    obtain ⟨i, rfl | rfl⟩ := hP.mem_cases hw
    · exact (Commute.zpow_right (show Commute d.sigma d.p from hσp') i).eq
    · rw [← mul_assoc, (Commute.zpow_right (show Commute d.sigma d.p from hσp') i).eq,
        mul_assoc, d.sigma_comm_b, ← mul_assoc]
  obtain ⟨π, hπ, hr' | hr'⟩ := d.mem_R0_cases hr
  · subst r
    exact hP' π hπ
  · subst r
    rw [← mul_assoc, hP' π hπ, mul_assoc]

theorem eight_dvd_of_sigma_ne (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts)
    (hσp : d.sigma * d.p * d.sigma⁻¹ = h.a * d.p) : 8 ∣ orderOf d.p := by
  obtain ⟨β, hP⟩ := d.pres
  obtain ⟨i, hi4, hi2, hσy⟩ := d.exists_sigma_comm hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F
  have hσp' : d.sigma * d.p * d.sigma⁻¹ = d.p ^ (orderOf d.p / 2) * d.p := by rw [hσp, d.p_a]
  have h1 : (d.p ^ (orderOf d.p / 2)) ^ i = 1 := by
    have := Eight.MC.Pres.sigma_zpow hσp' i
    rw [hσy, mul_inv_cancel_right] at this
    calc (d.p ^ (orderOf d.p / 2)) ^ i = (d.p ^ (orderOf d.p / 2)) ^ i * d.p ^ i * (d.p ^ i)⁻¹ := by
          group
      _ = 1 := by rw [← this, mul_inv_cancel]
  obtain ⟨t, ht⟩ := (hP.a_zpow_eq_one_iff i).mp h1
  refine hP.eight_dvd_of_ne_four fun h4 => hi2 ?_
  rw [ht, ← orderOf_dvd_iff_zpow_eq_one, h4]
  exact ⟨t, by push_cast; ring⟩

theorem sigma_comm_E (hRk : CFL2Rank) (hJ : CFL2J) (hC : CFL2C) (hB1 : ConjFixStatement)
    (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (F : d.Facts) {E : Subgroup H} (hES : E ≤ h.S) (hE2 : ∀ e ∈ E, e * e = 1)
    (hE32 : Nat.card E = 32) : ∀ e ∈ E, d.sigma * e = e * d.sigma := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨β, hP⟩ := d.pres
  have hdec := d.eq_sup_of_card_eq hRk hJ hC hCF1 hCF2 F hES hE2 hE32
  have hσR : d.sigma ∈ d.R0 := mem_sup_right (mem_zpowers _)
  have hcomm : ∀ x ∈ E ⊓ h.D, ∀ y ∈ E ⊓ d.R0, x * y = y * x :=
    fun x hx y hy => d.D_comm_R0 F x (mem_inf.mp hx).2 y (mem_inf.mp hy).2
  have hECom : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    Eight.comm_of_mul_self hE2 hx hy
  have hR : ∀ r ∈ E ⊓ d.R0, d.sigma * r = r * d.sigma := by
    rcases d.sigma_p hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F with hσp | hσp
    · intro r hr
      exact d.sigma_comm_R0_of_comm hσp (mem_inf.mp hr).2
    · have h8 := d.eight_dvd_of_sigma_ne hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F hσp
      have hσp' : d.sigma * d.p * d.sigma⁻¹ = d.p ^ (orderOf d.p / 2) * d.p := by
        rw [hσp, d.p_a]
      have hP0 : ∀ w : H, (∃ i : ℤ, w = d.p ^ (2 * i) ∨ w = d.p ^ (2 * i) * d.b) →
          d.sigma * w = w * d.sigma := by
        rintro w ⟨i, rfl | rfl⟩
        · exact (d.sigma_comm_P0 hσp i).1
        · exact (d.sigma_comm_P0 hσp i).2
      have hdisj : (E ⊓ h.D) ⊓ (E ⊓ d.R0) = ⊥ :=
        eq_bot_iff.mpr ((inf_le_inf inf_le_right inf_le_right).trans
          (d.D_inf_R0 hCF1 hCF2 F).le)
      have hc32 := Seven.card_sup_of_commute hcomm hdisj
      rw [← hdec, hE32] at hc32
      have hcD := d.card_elem_D hRk hCF1 hCF2 F (inf_le_right : E ⊓ h.D ≤ h.D)
        (fun w hw => hE2 w (mem_inf.mp hw).1)
      have hcR := d.card_elem_R0 (inf_le_right : E ⊓ d.R0 ≤ d.R0)
        (fun w hw => hE2 w (mem_inf.mp hw).1)
      have hR8 : Nat.card ↥(E ⊓ d.R0) = 8 := by
        have hpos : 0 < Nat.card ↥(E ⊓ h.D) := Nat.card_pos
        nlinarith
      have hRN : E ⊓ d.R0 ≤ normalizer (h.J : Set H) :=
        (inf_le_left.trans hES).trans h.toHyp52.S_le_normalizer
      have h1 := Seven.card_eq_card_rhoImg_mul hRN
      have h2 := d.card_rhoImg_R0_le (inf_le_right : E ⊓ d.R0 ≤ d.R0)
      rw [hR8] at h1
      have hEP4 : 4 ≤ Nat.card ↥((E ⊓ d.R0) ⊓ coreActionKernel h.J) := by
        by_contra hlt
        push Not at hlt
        have : Nat.card (Seven.rhoImg h.J (E ⊓ d.R0)) *
            Nat.card ↥((E ⊓ d.R0) ⊓ coreActionKernel h.J) ≤ 2 * 3 :=
          Nat.mul_le_mul h2 (by omega)
        omega
      have hEPmem : ∀ w ∈ (E ⊓ d.R0) ⊓ coreActionKernel h.J, w ∈ E ∧ w ∈ h.P := by
        intro w hw
        obtain ⟨⟨hwE, -⟩, hwC⟩ := hw
        exact ⟨hwE, mem_inf.mpr ⟨hES hwE, hwC⟩⟩
      have hu : ∃ u ∈ E, u ∈ h.P ∧ u ∉ zpowers d.p := by
        by_contra hne
        push Not at hne
        have hle : (E ⊓ d.R0) ⊓ coreActionKernel h.J ≤ zpowers (d.p ^ (orderOf d.p / 2)) := by
          intro w hw
          obtain ⟨hwE, hwP⟩ := hEPmem w hw
          rcases hP.eq_one_or_a (hne w hwE hwP) (hE2 w hwE) with h3 | h3
          · rw [h3]; exact one_mem _
          · rw [h3]; exact mem_zpowers _
        have h3 := card_le_of_le hle
        rw [Nat.card_zpowers] at h3
        have h4 : orderOf (d.p ^ (orderOf d.p / 2)) ≤ 2 :=
          orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hP.a_mul_a)
        omega
      obtain ⟨u, huE, huP, hup⟩ := hu
      have he₁ : ∃ e₁ ∈ E ⊓ d.R0, e₁ ∉ h.P := by
        by_contra hne
        push Not at hne
        have hle : E ⊓ d.R0 ≤ h.P := fun w hw => hne w hw
        have h3 := hP.card_le_four hle (fun w hw => hE2 w (mem_inf.mp hw).1)
        omega
      obtain ⟨e₁, he₁R, he₁P⟩ := he₁
      obtain ⟨π₁, hπ₁, he₁' | he₁'⟩ := d.mem_R0_cases (mem_inf.mp he₁R).2
      · exact absurd (he₁' ▸ hπ₁) he₁P
      have hσinv : d.sigma⁻¹ = d.sigma := inv_eq_of_mul_eq_one_right d.sigma_mul_self
      have hconjP : ∀ π ∈ h.P, d.sigma⁻¹ * π * d.sigma ∈ h.P := fun π hπ => by
        have := (mem_normalizer_iff.mp (inv_mem d.sigma_mem_normalizer_P) π).mp hπ
        rwa [inv_inv] at this
      have hform : ∀ π : H, π * d.sigma = d.sigma * (d.sigma⁻¹ * π * d.sigma) := fun π => by
        group
      have he8 : ∀ π ∈ h.P, ∀ v ∈ E, v ∈ h.P → v ∉ zpowers d.p → π * d.sigma ∈ E →
          (∃ i : ℤ, d.sigma⁻¹ * π * d.sigma = d.p ^ (2 * i) ∨
            d.sigma⁻¹ * π * d.sigma = d.p ^ (2 * i) * d.b) ∧
          ∃ j : ℤ, v = d.p ^ (2 * j) * d.b := by
        intro π hπ v hvE hvP hvp hπE
        refine hP.e8_lemma h8 d.sigma_mul_self d.sigma_comm_b hσp' (hconjP π hπ) hvP hvp
          (hE2 v hvE) ?_ ?_
        · rw [← hform]; exact hE2 _ hπE
        · rw [← hform]; exact hECom _ hπE v hvE
      have he₁E : π₁ * d.sigma ∈ E := he₁' ▸ (mem_inf.mp he₁R).1
      intro r hr
      obtain ⟨π, hπ, hr' | hr'⟩ := d.mem_R0_cases (mem_inf.mp hr).2
      · subst r
        by_cases hπp : π ∈ zpowers d.p
        · rcases hP.eq_one_or_a hπp (hE2 π (mem_inf.mp hr).1) with h3 | h3
          · rw [h3, one_mul, mul_one]
          · rw [h3, d.p_a]
            show d.tau * d.b * h.a = h.a * (d.tau * d.b)
            rw [mul_assoc, ← d.a_comm_b, ← mul_assoc, d.tau_comm_a, mul_assoc]
        · obtain ⟨-, j, hj⟩ := he8 π₁ hπ₁ π (mem_inf.mp hr).1 hπ hπp he₁E
          rw [hj]
          exact (d.sigma_comm_P0 hσp j).2
      · subst r
        obtain ⟨⟨i, hi⟩, -⟩ := he8 π hπ u huE huP hup (mem_inf.mp hr).1
        have h3 := hP0 _ ⟨i, hi⟩
        calc d.sigma * (π * d.sigma) = d.sigma * (d.sigma * (d.sigma⁻¹ * π * d.sigma)) := by
              rw [← hform]
          _ = d.sigma * ((d.sigma⁻¹ * π * d.sigma) * d.sigma) := by rw [h3]
          _ = (d.sigma * (d.sigma⁻¹ * π * d.sigma)) * d.sigma :=
              (mul_assoc d.sigma (d.sigma⁻¹ * π * d.sigma) d.sigma).symm
          _ = π * d.sigma * d.sigma := by rw [← hform]
  intro e he
  rw [hdec] at he
  obtain ⟨x, hx, y, hy, rfl⟩ := Eight.exists_mul_of_mem_sup₂ hcomm he
  have hxσ : d.sigma * x = x * d.sigma :=
    (d.D_comm_R0 F x (mem_inf.mp hx).2 d.sigma hσR).symm
  rw [← mul_assoc, hxσ, mul_assoc, hR y hy, ← mul_assoc]

theorem F32_le_centralizer_sigma (hRk : CFL2Rank) (hJ : CFL2J) (hC : CFL2C)
    (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion)
    (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    h.F32 ≤ centralizer ({d.sigma} : Set H) :=
  Eight.JeN_le_of fun _ hES hE2 hE32 w hw => mem_centralizer_singleton_iff.mpr
    (d.sigma_comm_E hRk hJ hC hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F hES hE2 hE32 w hw).symm

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
