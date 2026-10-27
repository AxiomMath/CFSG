module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81F3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Fus3

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

theorem D_sup_tau_inf_P (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    (h.D ⊔ zpowers d.tau) ⊓ coreActionKernel h.J = ⊥ := by
  have hc : ∀ x ∈ h.D, ∀ y ∈ zpowers d.tau, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x d.tau from (d.D_comm_tau F hx).symm) k).eq
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hw1, hw2⟩ := mem_inf.mp hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Eight.exists_mul_of_mem_sup₂ hc hw1
  have hwS : x * y ∈ h.S := mul_mem (h.toHyp52.D_le_S hx)
    ((zpowers_le.mpr d.tau_mem_S) hy)
  have hwP : x * y ∈ h.P := mem_inf.mpr ⟨hwS, hw2⟩
  rcases eq_one_or_of_mem_zpowers_of_mul_self d.tau_sq hy with h1 | h1
  · rw [h1, mul_one] at hwP ⊢
    rw [← h.toHyp52.D_inf_P_eq_bot H₁.center_J]
    exact mem_inf.mpr ⟨hx, hwP⟩
  · exfalso
    apply d.tau_not_mem_DP hCF1 hCF2 F
    rw [h1] at hwP
    have : d.tau = x⁻¹ * (x * d.tau) := by group
    rw [this]
    exact mul_mem_sup (inv_mem hx) hwP

theorem card_elem_D (hRk : CFL2Rank) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (F : d.Facts) {X : Subgroup H} (hXD : X ≤ h.D) (hX2 : ∀ x ∈ X, x * x = 1) :
    Nat.card X ≤ 4 := by
  have hc : ∀ x ∈ X, ∀ y ∈ zpowers d.tau, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x d.tau from (d.D_comm_tau F (hXD hx)).symm) k).eq
  have hτ2 : ∀ y ∈ zpowers d.tau, y * y = 1 := by
    intro y hy
    rcases eq_one_or_of_mem_zpowers_of_mul_self d.tau_sq hy with h1 | h1
    · rw [h1, one_mul]
    · rw [h1]; exact d.tau_sq
  have hdisj : X ⊓ zpowers d.tau = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwX, hwτ⟩ := mem_inf.mp hw
    rcases eq_one_or_of_mem_zpowers_of_mul_self d.tau_sq hwτ with h1 | h1
    · exact h1
    · exfalso
      exact d.tau_not_mem_DP hCF1 hCF2 F (mem_sup_left (h1 ▸ hXD hwX))
  have hcard := Seven.card_sup_of_commute hc hdisj
  have hτord : Nat.card (zpowers d.tau) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact d.tau_sq)
      (fun h1 => d.tau_not_mem_DP hCF1 hCF2 F (h1 ▸ one_mem _))
  have hle : X ⊔ zpowers d.tau ≤ h.D ⊔ zpowers d.tau := sup_le_sup_right hXD _
  have hN : X ⊔ zpowers d.tau ≤ normalizer (h.J : Set H) :=
    (sup_le (hXD.trans h.toHyp52.D_le_S) (zpowers_le.mpr d.tau_mem_S)).trans
      h.toHyp52.S_le_normalizer
  have h1 := Seven.card_eq_card_rhoImg_mul hN
  have h2 : (X ⊔ zpowers d.tau) ⊓ coreActionKernel h.J = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ hle).trans (d.D_sup_tau_inf_P hCF1 hCF2 F).le)
  rw [h2, Subgroup.card_bot, mul_one] at h1
  obtain ⟨p', f', hp', hp2', hf', hJL⟩ := H₁.exists_lieModel_Jbar
  have h3 := hRk _ p' f' hp' hp2' hf' hJL _ (rhoImg_mul_self (Seven.sup_sq_eq_one hX2 hτ2 hc))
  rw [← h1, hcard, hτord] at h3
  omega

noncomputable abbrev rhoS {s : H} (hs : s ∈ h.S) : MulAut (h.J ⧸ pPrimeCore 2 h.J) :=
  Eight.oddBarAction h.J ⟨s, h.toHyp52.S_le_normalizer hs⟩

theorem rhoS_mem {W : Subgroup H} {s : H} (hs : s ∈ h.S) (hsW : s ∈ W) :
    rhoS hs ∈ Seven.rhoImg h.J W :=
  ⟨⟨s, h.toHyp52.S_le_normalizer hs⟩, mem_subgroupOf.mpr hsW, rfl⟩

theorem rhoS_mul_self {s : H} (hs : s ∈ h.S) (hs2 : s * s = 1) : rhoS hs * rhoS hs = 1 := by
  rw [← map_mul, show (⟨s, h.toHyp52.S_le_normalizer hs⟩ : ↥(normalizer (h.J : Set H))) *
    ⟨s, h.toHyp52.S_le_normalizer hs⟩ = 1 from Subtype.ext hs2, map_one]

theorem rhoS_inf_centralizer_le (hC : CFL2C) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    Seven.rhoImg h.J h.S ⊓ centralizer ((Seven.rhoImg h.J h.D : Subgroup _) :
        Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))) ≤
      zpowers (rhoS (h.toHyp52.D_le_S d.z_D)) ⊔ zpowers (rhoS d.tau_mem_S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzS : d.z ∈ h.S := h.toHyp52.D_le_S d.z_D
  set ρz := rhoS hzS with hρz
  set ρτ := rhoS d.tau_mem_S with hρτ
  obtain ⟨T, hT, hTD⟩ := h.toHyp52.sec8_exists_sylow_Dbar
  have hinn : innOf (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) = Seven.rhoImg h.J h.D := by
    rw [hT, Seven.rhoImg_eq_innOf (inf_le_right : h.D ≤ h.J)]
  set C := Seven.rhoImg h.J h.S ⊓ centralizer ((Seven.rhoImg h.J h.D : Subgroup _) :
    Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))) with hCdef
  have hS2 : IsPGroup 2 (Seven.rhoImg h.J h.S) :=
    (h.toHyp52.isPGroup_S.of_equiv (subgroupOfEquivOfLe h.toHyp52.S_le_normalizer).symm).map _
  have hC4 : Nat.card C ≤ 4 := by
    obtain ⟨p', f', hp', hp2', hf', hJL⟩ := H₁.exists_lieModel_Jbar
    refine hC _ p' f' hp' hp2' hf' hJL T (hTD ▸ F.eight_le) _ (hS2.to_le inf_le_left) ?_
    rw [hinn]
    exact inf_le_right
  have hcomm : ∀ s (hs : s ∈ h.S), (∀ e ∈ h.D, s * e = e * s) → rhoS hs ∈ C := by
    intro s hs hse
    refine mem_inf.mpr ⟨rhoS_mem hs hs, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨e, heN⟩, he, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hse e (mem_subgroupOf.mp he)).symm
  have hzC : ρz ∈ C := hcomm _ hzS (fun e he => (mem_centralizer_iff.mp d.z_S e
    (h.toHyp52.D_le_S he)).symm)
  have hτC : ρτ ∈ C := hcomm _ d.tau_mem_S (fun e he => d.D_comm_tau F he)
  have hz1 : ρz ≠ 1 := by
    intro h1
    have hzP := (rho_eq_one_iff (h := h) hzS).mp h1
    have := (h.toHyp52.D_inf_P_eq_bot H₁.center_J) ▸ mem_inf.mpr ⟨d.z_D, hzP⟩
    exact d.z_ne_one (mem_bot.mp this)
  have hτ1 : ρτ ≠ 1 := fun h1 => d.tau_not_mem_DP hCF1 hCF2 F
    (mem_sup_right ((rho_eq_one_iff (h := h) d.tau_mem_S).mp h1))
  have hzτ : ρz ≠ ρτ := by
    intro h1
    have h2 : rhoS (mul_mem (inv_mem hzS) d.tau_mem_S) = 1 := by
      show Eight.oddBarAction h.J
        ((⟨d.z, h.toHyp52.S_le_normalizer hzS⟩ : ↥(normalizer (h.J : Set H)))⁻¹ *
          ⟨d.tau, h.toHyp52.S_le_normalizer d.tau_mem_S⟩) = 1
      rw [map_mul, map_inv]
      exact inv_mul_eq_one.mpr h1
    have h3 := (rho_eq_one_iff (h := h) (mul_mem (inv_mem hzS) d.tau_mem_S)).mp h2
    apply d.tau_not_mem_DP hCF1 hCF2 F
    have : d.tau = d.z * (d.z⁻¹ * d.tau) := by group
    rw [this]
    exact mul_mem_sup d.z_D h3
  have hz2 : ρz * ρz = 1 := rhoS_mul_self hzS d.z_mul_self
  have hτ2 : ρτ * ρτ = 1 := rhoS_mul_self d.tau_mem_S d.tau_sq
  have hcz : Nat.card (zpowers ρz) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hcτ : Nat.card (zpowers ρτ) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (by rw [pow_two]; exact hτ2) hτ1
  have hzτc : ρz * ρτ = ρτ * ρz := by
    exact mem_centralizer_iff.mp (mem_inf.mp hτC).2 ρz (rhoS_mem hzS d.z_D)
  have hcW : ∀ x ∈ zpowers ρz, ∀ y ∈ zpowers ρτ, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow hzτc i j).eq
  have hdW : zpowers ρz ⊓ zpowers ρτ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hw1, hw2⟩ := mem_inf.mp hw
    rcases eq_one_or_of_mem_zpowers_of_mul_self hz2 hw1 with h1 | h1
    · exact h1
    · rcases eq_one_or_of_mem_zpowers_of_mul_self hτ2 hw2 with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hzτ
  have hcardW := Seven.card_sup_of_commute hcW hdW
  rw [hcz, hcτ] at hcardW
  have hWC : zpowers ρz ⊔ zpowers ρτ ≤ C := sup_le (zpowers_le.mpr hzC) (zpowers_le.mpr hτC)
  have hCW : C = zpowers ρz ⊔ zpowers ρτ := (eq_of_le_of_card_ge hWC (by omega)).symm
  rw [hCW]

theorem le_D_sup_R0 (hRk : CFL2Rank) (hJ : CFL2J) (hC : CFL2C) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) {E : Subgroup H} (hES : E ≤ h.S)
    (hE2 : ∀ e ∈ E, e * e = 1) (hE32 : Nat.card E = 32) : E ≤ h.D ⊔ d.R0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEN : E ≤ normalizer (h.J : Set H) := hES.trans h.toHyp52.S_le_normalizer
  have h1 := Seven.card_eq_card_rhoImg_mul hEN
  obtain ⟨p', f', hp', hp2', hf', hJL⟩ := H₁.exists_lieModel_Jbar
  have h2 : Nat.card (Seven.rhoImg h.J E) ≤ 8 :=
    hRk _ p' f' hp' hp2' hf' hJL _ (rhoImg_mul_self hE2)
  obtain ⟨β, hP⟩ := d.pres
  have h3 : Nat.card ↥(E ⊓ coreActionKernel h.J) ≤ 4 :=
    hP.card_le_four (fun w hw => mem_inf.mpr ⟨hES (mem_inf.mp hw).1, (mem_inf.mp hw).2⟩)
      (fun w hw => hE2 w (mem_inf.mp hw).1)
  have h8 : Nat.card (Seven.rhoImg h.J E) = 8 := by
    rw [hE32] at h1
    have : 32 ≤ Nat.card (Seven.rhoImg h.J E) * 4 := h1 ▸ Nat.mul_le_mul_left _ h3
    omega
  obtain ⟨T, hT, hTD⟩ := h.toHyp52.sec8_exists_sylow_Dbar
  have hinn : innOf (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) = Seven.rhoImg h.J h.D := by
    rw [hT, Seven.rhoImg_eq_innOf (inf_le_right : h.D ≤ h.J)]
  have hS2 : IsPGroup 2 (Seven.rhoImg h.J h.S) :=
    (h.toHyp52.isPGroup_S.of_equiv (subgroupOfEquivOfLe h.toHyp52.S_le_normalizer).symm).map _
  have hDS : Seven.rhoImg h.J h.D ≤ Seven.rhoImg h.J h.S :=
    map_mono fun x hx => mem_subgroupOf.mpr (h.toHyp52.D_le_S (mem_subgroupOf.mp hx))
  have hES' : Seven.rhoImg h.J E ≤ Seven.rhoImg h.J h.S :=
    map_mono fun x hx => mem_subgroupOf.mpr (hES (mem_subgroupOf.mp hx))
  have h4 := hJ _ p' f' hp' hp2' hf' hJL T (hTD ▸ F.eight_le) _ hS2 (hinn ▸ hDS) _ hES'
    (rhoImg_mul_self hE2) h8
  rw [hinn] at h4
  have h5 : Seven.rhoImg h.J E ≤ Seven.rhoImg h.J (h.D ⊔ zpowers d.tau) :=
    h4.trans (sup_le (map_mono fun x hx => mem_subgroupOf.mpr (mem_sup_left
      (mem_subgroupOf.mp hx))) ((d.rhoS_inf_centralizer_le hC hCF1 hCF2 F).trans
        (sup_le (zpowers_le.mpr (rhoS_mem (h.toHyp52.D_le_S d.z_D) (mem_sup_left d.z_D)))
          (zpowers_le.mpr (rhoS_mem d.tau_mem_S (mem_sup_right (mem_zpowers _)))))))
  intro e he
  obtain ⟨w, hw, hwe⟩ := mem_map.mp (h5 (rhoS_mem (hES he) he))
  have hwS : (w : H) ∈ h.S :=
    (sup_le h.toHyp52.D_le_S (zpowers_le.mpr d.tau_mem_S)) (mem_subgroupOf.mp hw)
  have h6 : (w : H)⁻¹ * e ∈ h.P := by
    refine (rho_eq_one_iff (h := h) (mul_mem (inv_mem hwS) (hES he))).mp ?_
    show Eight.oddBarAction h.J (w⁻¹ * ⟨e, h.toHyp52.S_le_normalizer (hES he)⟩) = 1
    rw [map_mul, map_inv, hwe, inv_mul_cancel]
  have hτR : d.tau ∈ d.R0 := by
    have : d.tau = d.sigma * d.b := by
      show d.tau = d.tau * d.b * d.b
      rw [mul_assoc, d.b_mul_self, mul_one]
    rw [this]
    exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left d.b_mem_P)
  have hle : h.D ⊔ zpowers d.tau ≤ h.D ⊔ d.R0 := sup_le le_sup_left
    (zpowers_le.mpr (mem_sup_right hτR))
  rw [show e = (w : H) * ((w : H)⁻¹ * e) by group]
  exact mul_mem (hle (mem_subgroupOf.mp hw)) (mem_sup_right (mem_sup_left h6))

theorem eq_sup_of_card_eq (hRk : CFL2Rank) (hJ : CFL2J) (hC : CFL2C) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) {E : Subgroup H} (hES : E ≤ h.S)
    (hE2 : ∀ e ∈ E, e * e = 1) (hE32 : Nat.card E = 32) : E = (E ⊓ h.D) ⊔ (E ⊓ d.R0) :=
  eq_sup_inf_of_elemAb (d.D_comm_R0 F) (d.D_inf_R0 hCF1 hCF2 F)
    (d.le_D_sup_R0 hRk hJ hC hCF1 hCF2 F hES hE2 hE32) hE2
    (fun X hX hX2 => d.card_elem_D hRk hCF1 hCF2 F hX hX2)
    (fun X hX hX2 => d.card_elem_R0 hX hX2) (by rw [hE32])

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
