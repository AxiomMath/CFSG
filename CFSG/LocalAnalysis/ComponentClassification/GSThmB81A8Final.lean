module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8Dih
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Frontier
public import Certificates.Certificate2007
public import Certificates.Certificate2013
public import Certificates.Certificate2014
public import Certificates.Certificate2019

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace A8

theorem mem_sup_cases {G : Type*} [Group G] {x y w : G} (hx : x * x = 1) (hy : y * y = 1)
    (hc : x * y = y * x) (hw : w ∈ zpowers x ⊔ zpowers y) :
    w = 1 ∨ w = x ∨ w = y ∨ w = x * y := by
  have hcomm : ∀ u ∈ zpowers x, ∀ v ∈ zpowers y, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
    exact (Commute.zpow_zpow hc i j).eq
  obtain ⟨u, hu, v, hv, rfl⟩ := Eight.exists_mul_of_mem_sup₂ hcomm hw
  rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hx hu with rfl | rfl <;>
    rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hy hv with rfl | rfl
  · left; rw [one_mul]
  · right; right; left; rw [one_mul]
  · right; left; rw [mul_one]
  · right; right; right; rfl

end A8

theorem gs81Step8Input_of_in81 (I : In81) : GS81Step8Input := by
  intro H _ _ h H₁ d v hst hA8
  have F := hst.facts
  have h3 := Hyp59.L81Hyp.Data.not_conj_asigma_sigma F hst.not_b_bz
  obtain ⟨M, -, hA, hΦ⟩ := A8.exists_model H₁ I.cf1 I.cf2 hA8
  have hD8 := A8.card_D (M := M) I.cf1 I.cf2 F hA hΦ
  have hp4 : orderOf d.p = 4 := by
    have := d.card_P
    rw [hst.card_P, hD8] at this
    omega
  have hpa : d.p * d.p = h.a := by
    have := d.p_a
    rw [hp4, show 4 / 2 = 2 from rfl, pow_two] at this
    exact this
  have hp1 : d.p * d.p * d.p * d.p = 1 := by
    calc d.p * d.p * d.p * d.p = d.p ^ 4 := by simp only [pow_succ, pow_zero, one_mul]
      _ = 1 := by rw [← hp4, pow_orderOf_eq_one]
  obtain ⟨e₁, e₂, θ, he₁D, he₂D, he₁₁, he₂₂, he₁₂, he₁1, he₂1, hne, hθC, hθP, hθo, hθ₁, hθ₂⟩ :=
    A8.exists_theta I hA8 F h3
  have hfus := fun {q : H} (hqP : q ∈ h.P) (hq2 : q * q = h.a)
      (hbq : d.b * q * d.b⁻¹ = q⁻¹) =>
    A8.fused_of_dihedral I hA8 F h3 he₁D he₂D he₁₁ he₂₂ he₁₂ he₁1 he₂1 hne hθC hθP hθo hθ₁ hθ₂
      hqP hq2 hbq
  have haS : h.a ∈ h.S := h.toHyp52.a_mem_S
  have haP : h.a ∈ h.P := h.toHyp52.a_mem_P
  have hpP : d.p ∈ h.P := d.p_mem
  have hpbP : d.p * d.b ∈ h.P := mul_mem hpP d.b_mem_P
  have haa := Six.a_mul_a_self h.toHyp52
  have hbinv : d.b⁻¹ = d.b := inv_eq_of_mul_eq_one_right d.b_mul_self
  have hdih : d.b * d.p * d.b = d.p⁻¹ := by
    have := hst.dihedral
    rwa [hbinv] at this
  have hpb2 : d.p * d.b * (d.p * d.b) = 1 := by
    rw [show d.p * d.b * (d.p * d.b) = d.p * (d.b * d.p * d.b) by group, hdih, mul_inv_cancel]
  have hpb1 : d.p * d.b ≠ 1 := fun h1 => d.b_not_mem_zpowers (by
    rw [show d.b = d.p⁻¹ from eq_inv_of_mul_eq_one_right h1]
    exact inv_mem (mem_zpowers _))
  have hapb : h.a ≠ d.p * d.b := fun h1 => d.b_not_mem_zpowers (by
    have hb : d.b = d.p := by
      calc d.b = d.p⁻¹ * (d.p * d.b) := by group
        _ = d.p⁻¹ * (d.p * d.p) := by rw [← h1, hpa]
        _ = d.p := by group
    rw [hb]
    exact mem_zpowers _)
  have hcapb : h.a * (d.p * d.b) = d.p * d.b * h.a :=
    (h.toHyp52.comm_a (mem_inf.mp hpbP).1).symm
  obtain ⟨hX₁4, hX₁2⟩ := card_sup_zpowers_of_inv haa hpb2
    (Hyp59.L81Hyp.Data.a_ne_one' (h := h)) hpb1 hapb hcapb
  obtain ⟨hX₂4, hX₂2⟩ := card_sup_zpowers_of_inv he₁₁ he₂₂ he₁1 he₂1 hne he₁₂
  set X₁ : Subgroup H := zpowers h.a ⊔ zpowers (d.p * d.b) with hX₁
  set X₂ : Subgroup H := zpowers e₁ ⊔ zpowers e₂ with hX₂
  have hX₁P : X₁ ≤ h.P := sup_le (zpowers_le.mpr haP) (zpowers_le.mpr hpbP)
  have hX₂D : X₂ ≤ h.D := sup_le (zpowers_le.mpr he₁D) (zpowers_le.mpr he₂D)
  have hDP := h.toHyp52.D_inf_P_eq_bot H₁.center_J
  have hc12 : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x :=
    fun x hx y hy => (H₁.D_comm_P (hX₂D hy) (hX₁P hx)).symm
  have hd12 : X₁ ⊓ X₂ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hw' : w ∈ h.D ⊓ h.P := mem_inf.mpr ⟨hX₂D (mem_inf.mp hw).2, hX₁P (mem_inf.mp hw).1⟩
    rwa [hDP] at hw'
  set X : Subgroup H := X₁ ⊔ X₂ with hX
  have hX16 : Nat.card X = 16 := by rw [hX, Seven.card_sup_of_commute hc12 hd12, hX₁4, hX₂4]
  have hX2 : ∀ w ∈ X, w * w = 1 := Seven.sup_sq_eq_one hX₁2 hX₂2 hc12
  have hXC : X ≤ centralizer ({h.a * d.sigma} : Set H) :=
    sup_le (fun w hw => A8.mem_C_of_mem_P I F h3 (hX₁P hw))
      (fun w hw => A8.mem_C_of_mem_D F (hX₂D hw))
  have hXDP : X ≤ h.D ⊔ h.P := sup_le (hX₁P.trans le_sup_right) (hX₂D.trans le_sup_left)
  have hXS : X ≤ h.S := sup_le (hX₁P.trans inf_le_left) (hX₂D.trans inf_le_left)
  have hσS := d.sigma_mem_S
  have hss : h.a * d.sigma * (h.a * d.sigma) = 1 := by
    calc h.a * d.sigma * (h.a * d.sigma) = h.a * (d.sigma * h.a) * d.sigma := by group
      _ = h.a * (h.a * d.sigma) * d.sigma := by rw [h.toHyp52.comm_a hσS]
      _ = (h.a * h.a) * (d.sigma * d.sigma) := by group
      _ = 1 := by rw [haa, d.sigma_mul_self, one_mul]
  have hsX : h.a * d.sigma ∉ X := fun h1 => d.sigma_not_mem_DP I.cf1 I.cf2 F (by
    have := mul_mem (inv_mem (mem_sup_right haP : h.a ∈ h.D ⊔ h.P)) (hXDP h1)
    rwa [inv_mul_cancel_left] at this)
  have hs1 : h.a * d.sigma ≠ 1 := fun h1 => hsX (h1 ▸ one_mem _)
  have hcs : ∀ x ∈ X, ∀ y ∈ zpowers (h.a * d.sigma), x * y = y * x := by
    intro x hx y hy
    rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hss hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact mem_centralizer_singleton_iff.mp (hXC hx)
  have hds : X ⊓ zpowers (h.a * d.sigma) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hss (mem_inf.mp hw).2 with
      h1 | h1
    · exact h1
    · exact absurd (h1 ▸ (mem_inf.mp hw).1) hsX
  have hcs2 : Nat.card (zpowers (h.a * d.sigma)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hss) hs1
  have hAS : X ⊔ zpowers (h.a * d.sigma) ≤ h.S :=
    sup_le hXS (zpowers_le.mpr (mul_mem haS hσS))
  refine ⟨X ⊔ zpowers (h.a * d.sigma), le_inf (hAS.trans le_sup_left)
    (sup_le hXC (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))),
    Seven.sup_sq_eq_one hX2 (fun w hw => ?_) hcs, ?_, ?_⟩
  · rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hss hw with rfl | rfl
    · rw [one_mul]
    · exact hss
  · rw [Seven.card_sup_of_commute hcs hds, hX16, hcs2]
  intro t ht htn
  obtain ⟨htA, htJ⟩ := mem_inf.mp ht
  have htP : t ∈ h.P := mem_inf.mpr ⟨hAS htA, htJ⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := Eight.exists_mul_of_mem_sup₂ hcs htA
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Eight.exists_mul_of_mem_sup₂ hc12 hx
  have hxy : x₂ = 1 ∧ y = 1 := by
    rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hss hy with rfl | rfl
    · refine ⟨?_, rfl⟩
      have h1 : x₂ ∈ h.P := by
        have := mul_mem (inv_mem (hX₁P hx₁)) htP
        rwa [mul_one, inv_mul_cancel_left] at this
      have h2 : x₂ ∈ h.D ⊓ h.P := mem_inf.mpr ⟨hX₂D hx₂, h1⟩
      rwa [hDP] at h2
    · exfalso
      have hx₂a : x₂ * h.a = h.a * x₂ := h.toHyp52.comm_a (hXS (mem_sup_right hx₂))
      have h1 : x₂ * d.sigma ∈ h.P := by
        have heq : x₂ * d.sigma = h.a⁻¹ * x₁⁻¹ * (x₁ * x₂ * (h.a * d.sigma)) := by
          calc x₂ * d.sigma = h.a⁻¹ * x₁⁻¹ * (x₁ * (h.a * x₂) * d.sigma) := by group
            _ = h.a⁻¹ * x₁⁻¹ * (x₁ * x₂ * (h.a * d.sigma)) := by rw [← hx₂a]; group
        rw [heq]
        exact mul_mem (mul_mem (inv_mem haP) (inv_mem (hX₁P hx₁))) htP
      have h2 : x₂ * d.sigma ∈ (h.D ⊔ zpowers d.sigma) ⊓ h.P :=
        mem_inf.mpr ⟨mul_mem (mem_sup_left (hX₂D hx₂)) (mem_sup_right (mem_zpowers _)), h1⟩
      rw [Hyp59.L81Hyp.Data.DSig_inf_P I F, mem_bot] at h2
      apply d.sigma_not_mem_DP I.cf1 I.cf2 F
      rw [show d.sigma = x₂⁻¹ from eq_inv_of_mul_eq_one_right h2]
      exact mem_sup_left (inv_mem (hX₂D hx₂))
  obtain ⟨rfl, rfl⟩ := hxy
  rw [mul_one, mul_one] at htn ⊢
  rcases A8.mem_sup_cases haa hpb2 hcapb hx₁ with rfl | rfl | rfl | rfl
  · exact absurd (one_mem _) htn
  · left
    exact ⟨1, by group⟩
  · exact hfus hpP hpa hst.dihedral
  · have heq : h.a * (d.p * d.b) = d.p⁻¹ * d.b := by
      rw [← hpa, ← mul_assoc, show d.p * d.p * d.p = d.p⁻¹ from eq_inv_of_mul_eq_one_left hp1]
    rw [heq]
    refine hfus (inv_mem hpP) ?_ ?_
    · rw [← mul_inv_rev, hpa, inv_eq_of_mul_eq_one_right haa]
    · rw [show d.b * d.p⁻¹ * d.b⁻¹ = (d.b * d.p * d.b⁻¹)⁻¹ by group, hst.dihedral]

end CFSG.ComponentClassification.GSThmB
