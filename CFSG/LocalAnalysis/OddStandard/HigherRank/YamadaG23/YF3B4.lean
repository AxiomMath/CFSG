module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3B3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma f3_phi_inv {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {y : G}
    (hy : y ∈ f3Y s) : f3phi s y⁻¹ = (f3phi s y)⁻¹ := by
  have h := f3_phi_mul hH y hy y⁻¹ (inv_mem hy)
  have h1 : f3phi s (y * y⁻¹) = 1 := by
    rw [mul_inv_cancel]
    simp [f3phi]
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem f3_Y_eq_Y1X0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ f3Y s, ∃ c ∈ f3Y1 s, ∃ a ∈ f3X0 s, y = c * a := by
  intro y hy
  obtain ⟨k, hk, _, _, hkfix, _, _⟩ := f3_exists_k hH
  have hkL : k ∈ L := hk.1
  have hkB : k ∈ normalizer (s.fr.B : Set G) := hk.2
  have hkN : k ∈ f3N s := ⟨s3_L_le_H s hH.hS hkL, hkB⟩
  have hkX : k ∈ s.X := f3_N_le_X s hkN
  have hkt : k * s.t = s.t * k := s3_comm_t_of_mem_L s hkL
  have hv : f3phi s y ∈ cen s.fr.B := f3_phi_mem hH y hy
  have hV : ∀ a ∈ cen s.fr.B, ∀ b ∈ cen s.fr.B, a * b = b * a :=
    fun a ha b hb => (ha.2 b hb.1).symm
  have hkV : ∀ v ∈ cen s.fr.B, k * v * k⁻¹ ∈ cen s.fr.B := by
    intro v hv'
    refine ⟨(Subgroup.mem_normalizer_iff.mp hkB v).mp hv'.1, ?_⟩
    show k * v * k⁻¹ ∈ Subgroup.centralizer (s.fr.B : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : k⁻¹ * b * k ∈ s.fr.B := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hkB) b).mp hb
    have hcomm : v * (k⁻¹ * b * k) = (k⁻¹ * b * k) * v := (hv'.2 _ hb').symm
    have hcalc : (k * v * k⁻¹) * b = b * (k * v * k⁻¹) := by
      calc (k * v * k⁻¹) * b
          = k * (v * (k⁻¹ * b * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * b * k) * v) * k⁻¹ := by rw [hcomm]
        _ = b * (k * v * k⁻¹) := by group
    exact hcalc.symm
  obtain ⟨u, huV, hu_eq⟩ := fpf_surj hV hkV hkfix (f3phi s y) hv
  obtain ⟨y', hy'Y, hy'phi⟩ := f3_phi_surj hH u huV
  have hck : k * y'⁻¹ * k⁻¹ ∈ f3Y s := f3_Y_normal hH k hkX y'⁻¹ (inv_mem hy'Y)
  have hcY : y' * (k * y'⁻¹ * k⁻¹) ∈ f3Y s := mul_mem hy'Y hck
  have hcY1 : y' * (k * y'⁻¹ * k⁻¹) ∈ f3Y1 s := by
    have h := Subgroup.commutator_mem_commutator hy'Y hkN
    rw [commutatorElement_def] at h
    exact Subgroup.mem_sup_left (by simpa only [mul_assoc] using h)
  have hphi_c : f3phi s (y' * (k * y'⁻¹ * k⁻¹)) = u * (k * u * k⁻¹)⁻¹ := by
    rw [f3_phi_mul hH y' hy'Y (k * y'⁻¹ * k⁻¹) hck, f3_phi_conj s hkt y'⁻¹,
      f3_phi_inv hH hy'Y, hy'phi]
    group
  have hphi_eq : f3phi s (y' * (k * y'⁻¹ * k⁻¹)) = f3phi s y := by
    rw [hphi_c, ← hu_eq]
  have ha : (y' * (k * y'⁻¹ * k⁻¹))⁻¹ * y ∈ f3X0 s := by
    refine (f3_phi_eq_one hH _ (mul_mem (inv_mem hcY) hy)).mp ?_
    rw [f3_phi_mul hH _ (inv_mem hcY) y hy, f3_phi_inv hH hcY, hphi_eq]
    group
  exact ⟨y' * (k * y'⁻¹ * k⁻¹), hcY1, (y' * (k * y'⁻¹ * k⁻¹))⁻¹ * y, ha, by group⟩

theorem f3_Y1_normal {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.X, ∀ c ∈ f3Y1 s, x * c * x⁻¹ ∈ f3Y1 s := by
  intro x hx c hc
  obtain ⟨y, hy, n, hn, hxyn⟩ := f3_X_eq_YN hH x hx
  rw [hxyn]
  obtain ⟨hYn, hNn⟩ := ext_normal (f3_extCtx hH)
  have hnc : n * c * n⁻¹ ∈ f3Y1 s := hNn n hn c hc
  have hyn : y * (n * c * n⁻¹) * y⁻¹ ∈ f3Y1 s := hYn y hy _ hnc
  simpa only [mul_inv_rev, mul_assoc] using hyn

theorem f3_C₂_le_X {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) : s.C₂ ≤ s.X :=
  calc s.C₂ = f3Y1 s := f3_C₂_eq_Y1 hH
    _ ≤ f3Y s := f3_Y1_le_Y hH
    _ ≤ s.X := inf_le_left

theorem f3_C₂_le_Y {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.C₂ ≤ f3Y s := by
  rw [f3_C₂_eq_Y1 hH]
  exact f3_Y1_le_Y hH

theorem f3_P_le_C₂ {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    f3P s ≤ s.C₂ := by
  rw [f3_C₂_eq_Y1 hH]
  exact le_sup_right

theorem f3_C₂_isPGroup {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    IsPGroup 2 ↥s.C₂ := by
  rw [f3_C₂_eq_Y1 hH]
  exact f3_Y1_isPGroup hH

theorem f3_C₂_normal {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.X, ∀ c ∈ s.C₂, x * c * x⁻¹ ∈ s.C₂ := by
  intro x hx c hc
  rw [f3_C₂_eq_Y1 hH] at hc ⊢
  exact f3_Y1_normal hH x hx c hc

theorem f3_X_eq_C₂N {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.X, ∃ c ∈ s.C₂, ∃ n ∈ f3N s, x = c * n := by
  intro x hx
  obtain ⟨y, hy, n, hn, hxyn⟩ := f3_X_eq_YN hH x hx
  obtain ⟨c, hc, a, ha, hca⟩ := f3_Y_eq_Y1X0 hH y hy
  exact ⟨c, by rw [f3_C₂_eq_Y1 hH]; exact hc, a * n, mul_mem (f3_X0_le_N hH ha) hn,
    by rw [hxyn, hca, mul_assoc]⟩

theorem f3_X_eq_N_sup_C₂ {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.X = f3N s ⊔ s.C₂ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hc, n, hn, rfl⟩ := f3_X_eq_C₂N hH x hx
    exact (sup_comm s.C₂ (f3N s)) ▸ Subgroup.mul_mem_sup hc hn
  · exact sup_le (f3_N_le_X s) (f3_C₂_le_X hH)

theorem f3_H_inf_C₂ {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.H ⊓ s.C₂ = f3P s := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hcH, hcC⟩ := hc
    have hcY : c ∈ f3Y s := f3_C₂_le_Y hH hcC
    have hcX0 : c ∈ f3X0 s := by
      rw [← f3_Y_inf_H hH]
      exact ⟨hcY, hcH⟩
    have hcY1 : c ∈ f3Y1 s := by
      rwa [← f3_C₂_eq_Y1 hH]
    have hmem : c ∈ f3Y1 s ⊓ f3X0 s := ⟨hcY1, hcX0⟩
    rwa [f3_Y1_inf_X0 hH] at hmem
  · exact le_inf (f3_P_le_H s) (f3_P_le_C₂ hH)

theorem f3_C₂_inf_X0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.C₂ ⊓ f3X0 s = f3P s := by
  rw [f3_C₂_eq_Y1 hH]
  exact f3_Y1_inf_X0 hH

end CFSG.OddStandard.HigherRank.YamadaG23
