module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3C3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem f3_Q_le_K1 (s : Setting3 G L) :
    centIn s.T (cen s.fr.B) ≤ centIn s.T₂ (cen s.fr.B) :=
  fun _ hx => Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (Subgroup.mem_inf.mp hx).1,
    (Subgroup.mem_inf.mp hx).2⟩

theorem f3_Q_le_T1 {s : Setting3 G L} (e : Setting3.Ext s) :
    centIn s.T (cen s.fr.B) ≤ e.T₁ :=
  fun _ hx => e.T_le (Subgroup.mem_inf.mp hx).1

theorem f3_Q_le_T2 (s : Setting3 G L) : centIn s.T (cen s.fr.B) ≤ s.T₂ :=
  fun _ hx => Subgroup.mem_sup_left (Subgroup.mem_inf.mp hx).1

private theorem f3_T2_le_X {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.T₂ ≤ s.X :=
  sup_le (f3_T_le_X hH) (f3_C₂_le_X hH)

private theorem f3_P_le_Q (s : Setting3 G L) :
    f3P s ≤ centIn s.T (cen s.fr.B) :=
  fun _ hp => Subgroup.mem_inf.mpr ⟨f3_P_le_T s hp, f3_P_le_cent_V s hp⟩

private theorem f3_Q_le_X0 (s : Setting3 G L) :
    centIn s.T (cen s.fr.B) ≤ f3X0 s :=
  fun _ hq => Subgroup.mem_inf.mpr ⟨s.sylow_T.1 (Subgroup.mem_inf.mp hq).1,
    (Subgroup.mem_inf.mp hq).2⟩

private theorem f3_T_normal_Q {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.T, ∀ q ∈ centIn s.T (cen s.fr.B), x * q * x⁻¹ ∈ centIn s.T (cen s.fr.B) := by
  intro x hx q hq
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact s.T.mul_mem (s.T.mul_mem hx (Subgroup.mem_inf.mp hq).1) (s.T.inv_mem hx)
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    intro v hv
    have hqcent : q ∈ centralizer (cen s.fr.B : Set G) := (Subgroup.mem_inf.mp hq).2
    have hnm : x⁻¹ * v * x ∈ cen s.fr.B := by
      simpa using f3_X_norm_V hH x⁻¹ (f3_T_le_X hH (s.T.inv_mem hx)) v hv
    have hcommq : (x⁻¹ * v * x) * q = q * (x⁻¹ * v * x) :=
      Subgroup.mem_centralizer_iff.mp hqcent (x⁻¹ * v * x) hnm
    calc v * (x * q * x⁻¹)
        = x * ((x⁻¹ * v * x) * q) * x⁻¹ := by group
      _ = x * (q * (x⁻¹ * v * x)) * x⁻¹ := by rw [hcommq]
      _ = x * q * x⁻¹ * v := by group

theorem f3_Q_normal_T2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.T₂, ∀ q ∈ centIn s.T (cen s.fr.B), x * q * x⁻¹ ∈ centIn s.T (cen s.fr.B) := by
  intro x hxT₂ q hq
  obtain ⟨τ, hτT, c, hcC₂, rfl⟩ := f3_mem_T₂ hH x hxT₂
  have hqY : q ∈ f3Y s :=
    Subgroup.mem_inf.mpr ⟨f3_T_le_X hH (Subgroup.mem_inf.mp hq).1, (Subgroup.mem_inf.mp hq).2⟩
  have hcq : c * q * c⁻¹ ∈ centIn s.T (cen s.fr.B) := by
    have hcomm : ⁅c, q⁆ ∈ f3P s :=
      ext_comm_mem (f3_extCtx hH) (f3_Y_sq hH) c (f3_C₂_le_Y hH hcC₂) q hqY
    have hdecomp : c * q * c⁻¹ = ⁅c, q⁆ * q := by
      rw [commutatorElement_def]
      group
    rw [hdecomp]
    exact (centIn s.T (cen s.fr.B)).mul_mem (f3_P_le_Q s hcomm) hq
  have heq : τ * c * q * (τ * c)⁻¹ = τ * (c * q * c⁻¹) * τ⁻¹ := by group
  rw [heq]
  exact f3_T_normal_Q hH τ hτT (c * q * c⁻¹) hcq

theorem f3_Q_relIndex_T {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (centIn s.T (cen s.fr.B)).relIndex s.T = 2 := by
  obtain ⟨w, hwV, hzV, hw1, hz1, hwz, _, hz2, _, hV⟩ := f3_V_elems hH
  obtain ⟨τ, hτT, _, _, hτw⟩ := f3_exists_tau hH
  refine relIndex_cent_two (V := cen s.fr.B) (U := s.T) hzV hwV hz1 hz2 hwz hV ?_ ?_ hτT ?_
  · intro u hu v hv
    exact f3_X_norm_V hH u (f3_T_le_X hH hu) v hv
  · intro u hu
    exact f3_T1_fix_z hH u (e.T_le hu)
  · intro hcon
    have h2 : τ * w * τ⁻¹ = s.fr.z * w := hτw w hwV hw1 hwz
    have hw_eq : w = s.fr.z * w := hcon.symm.trans h2
    have hz_eq : s.fr.z = 1 := by
      have h : s.fr.z * w = 1 * w := by rw [one_mul]; exact hw_eq.symm
      exact mul_right_cancel h
    exact hz1 hz_eq

theorem f3_Q_relIndex_T2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (centIn s.T (cen s.fr.B)).relIndex s.T₂ = 8 := by
  rw [← Subgroup.relIndex_mul_relIndex (H := centIn s.T (cen s.fr.B)) (K := s.T) (L := s.T₂)
    inf_le_left le_sup_left, f3_Q_relIndex_T hH, f3_T_relIndex_T₂ hH]

theorem f3_K1_relIndex {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (centIn s.T (cen s.fr.B)).relIndex (centIn s.T₂ (cen s.fr.B)) = 4 := by
  obtain ⟨w, hwV, hzV, hw1, hz1, hwz, _, hz2, _, hV⟩ := f3_V_elems hH
  obtain ⟨τ, hτT, _, _, hτw⟩ := f3_exists_tau hH
  have h2 : (centIn s.T₂ (cen s.fr.B)).relIndex s.T₂ = 2 := by
    refine relIndex_cent_two (V := cen s.fr.B) (U := s.T₂) hzV hwV hz1 hz2 hwz hV ?_ ?_
      (Subgroup.mem_sup_left hτT) ?_
    · intro u hu v hv
      exact f3_X_norm_V hH u (f3_T2_le_X hH hu) v hv
    · intro u hu
      exact f3_T2_fix_z hH u hu
    · intro hcon
      have h2' : τ * w * τ⁻¹ = s.fr.z * w := hτw w hwV hw1 hwz
      have hw_eq : w = s.fr.z * w := hcon.symm.trans h2'
      have hz_eq : s.fr.z = 1 := by
        have h : s.fr.z * w = 1 * w := by rw [one_mul]; exact hw_eq.symm
        exact mul_right_cancel h
      exact hz1 hz_eq
  have h := Subgroup.relIndex_mul_relIndex (H := centIn s.T (cen s.fr.B))
    (K := centIn s.T₂ (cen s.fr.B)) (L := s.T₂) (f3_Q_le_K1 s) inf_le_left
  rw [h2, f3_Q_relIndex_T2 hH] at h
  omega

theorem f3_K2_relIndex {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (centIn s.T (cen s.fr.B)).relIndex e.T₁ = 4 := by
  have h := Subgroup.relIndex_mul_relIndex (H := centIn s.T (cen s.fr.B)) (K := s.T)
    (L := e.T₁) inf_le_left e.T_le
  rw [f3_Q_relIndex_T hH, hH.hDef.2.1] at h
  omega

theorem f3_K1_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ centIn s.T₂ (cen s.fr.B), x ^ 2 ∈ centIn s.T (cen s.fr.B) := by
  intro x hx
  have hxT₂ : x ∈ s.T₂ := (Subgroup.mem_inf.mp hx).1
  have hxcent : x ∈ centralizer (cen s.fr.B : Set G) := (Subgroup.mem_inf.mp hx).2
  have hxY : x ∈ f3Y s := Subgroup.mem_inf.mpr ⟨f3_T2_le_X hH hxT₂, hxcent⟩
  have hsq : x ^ 2 ∈ f3P s := f3_Y_sq hH x hxY
  exact Subgroup.mem_inf.mpr ⟨f3_P_le_T s hsq, f3_P_le_cent_V s hsq⟩

theorem f3_K2_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ e.T₁, x ^ 2 ∈ centIn s.T (cen s.fr.B) := by
  obtain ⟨w, hwV, hzV, _, _, hwz, _, hz2, _, hV⟩ := f3_V_elems hH
  intro x hx
  have hnorm : ∀ v ∈ cen s.fr.B, x * v * x⁻¹ ∈ cen s.fr.B :=
    fun v hv => f3_X_norm_V hH x (f3_T1_le_X hH hx) v hv
  have hfixz : x * s.fr.z * x⁻¹ = s.fr.z := f3_T1_fix_z hH x hx
  have hcent : x ^ 2 ∈ centralizer (cen s.fr.B : Set G) :=
    sq_mem_cent (V := cen s.fr.B) hzV hwV hz2 hV hnorm hfixz
  exact Subgroup.mem_inf.mpr ⟨s.R_le_T (f3_T1_sq_mem_R hH x hx), hcent⟩

theorem f3_K_ne {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ¬ e.T₁ ≤ centIn s.T₂ (cen s.fr.B) := by
  obtain ⟨w, hwV, _, hw1, hz1, hwz, _, _, _, _⟩ := f3_V_elems hH
  obtain ⟨τ, hτT, _, _, hτw⟩ := f3_exists_tau hH
  intro hle
  have hτK : τ ∈ centIn s.T₂ (cen s.fr.B) := hle (e.T_le hτT)
  have hcent : τ ∈ centralizer (cen s.fr.B : Set G) := (Subgroup.mem_inf.mp hτK).2
  have hcommw : w * τ = τ * w := Subgroup.mem_centralizer_iff.mp hcent w hwV
  have h1 : τ * w * τ⁻¹ = w := by rw [← hcommw]; group
  have h2 : τ * w * τ⁻¹ = s.fr.z * w := hτw w hwV hw1 hwz
  have hz_eq : s.fr.z = 1 := by
    have h : s.fr.z * w = 1 * w := by rw [one_mul]; exact (h1.symm.trans h2).symm
    exact mul_right_cancel h
  exact hz1 hz_eq

theorem f3_T2_nonab {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ x ∈ s.T₂, ∃ y ∈ s.T₂, x * y * x⁻¹ * y⁻¹ ∉ centIn s.T (cen s.fr.B) := by
  obtain ⟨f, hfval, hfsurj, _⟩ := f3_phiHom hH
  obtain ⟨w, hwV, _, hw1, hz1, hwz, hw2, _, _, _⟩ := f3_V_elems hH
  obtain ⟨τ, hτT, _, _, hτw⟩ := f3_exists_tau hH
  obtain ⟨c, hc⟩ := hfsurj ⟨w, hwV⟩
  have hcC₂ : (c : G) ∈ s.C₂ := c.2
  have hphi_c : f3phi s (c : G) = w := by
    rw [← hfval c, hc]
  have hτC₂ : τ * (c : G) * τ⁻¹ ∈ s.C₂ := f3_T_norm_C₂ hH τ hτT (c : G) hcC₂
  have haY : τ * (c : G) * τ⁻¹ ∈ f3Y s := f3_C₂_le_Y hH hτC₂
  have hcinvY : (c : G)⁻¹ ∈ f3Y s := f3_C₂_le_Y hH (s.C₂.inv_mem hcC₂)
  have hcY : (c : G) ∈ f3Y s := f3_C₂_le_Y hH hcC₂
  have hww : w * w = 1 := by simpa [pow_two] using hw2
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left hww
  have hphi_a : f3phi s (τ * (c : G) * τ⁻¹) = s.fr.z * w := by
    rw [f3_phi_conj s (s3_comm_t_of_mem_T s hτT) (c : G), hphi_c]
    exact hτw w hwV hw1 hwz
  have hphi_cinv : f3phi s (c : G)⁻¹ = w := by
    have hmul := f3_phi_mul hH (c : G) hcY (c : G)⁻¹ hcinvY
    rw [mul_inv_cancel, show f3phi s (1 : G) = 1 by simp [f3phi]] at hmul
    rw [hphi_c] at hmul
    have : f3phi s (c : G)⁻¹ = w⁻¹ := eq_inv_of_mul_eq_one_right hmul.symm
    rw [this, hwinv]
  have hphi_elem : f3phi s (τ * (c : G) * τ⁻¹ * (c : G)⁻¹) = s.fr.z := by
    have hmul := f3_phi_mul hH (τ * (c : G) * τ⁻¹) haY (c : G)⁻¹ hcinvY
    rw [hphi_a, hphi_cinv] at hmul
    have hzww : (s.fr.z * w) * w = s.fr.z := by rw [mul_assoc, hww, mul_one]
    exact hmul.trans hzww
  refine ⟨τ, Subgroup.mem_sup_left hτT, (c : G), Subgroup.mem_sup_right hcC₂, ?_⟩
  intro hmemQ
  have helemY : τ * (c : G) * τ⁻¹ * (c : G)⁻¹ ∈ f3Y s := (f3Y s).mul_mem haY hcinvY
  have hmemX0 : τ * (c : G) * τ⁻¹ * (c : G)⁻¹ ∈ f3X0 s := f3_Q_le_X0 s hmemQ
  have hphi1 : f3phi s (τ * (c : G) * τ⁻¹ * (c : G)⁻¹) = 1 :=
    (f3_phi_eq_one hH _ helemY).mpr hmemX0
  rw [hphi_elem] at hphi1
  exact hz1 hphi1

theorem f3_c10 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    SecProp s.T₂ (centIn s.T (cen s.fr.B)) (fun Y _ _ π =>
      Nonempty (Y ≃* DihedralGroup 4) ∧
        {V : Subgroup Y | IsE 2 ↥V} =
          {((centIn s.T₂ (cen s.fr.B)).subgroupOf s.T₂).map π, (e.T₁.subgroupOf s.T₂).map π}) :=
  secProp_d8 (f3_Q_le_T2 s) (f3_Q_normal_T2 hH) (fun _ hx => (Subgroup.mem_inf.mp hx).1)
    (f3_c8 hH) (f3_Q_le_K1 s) (f3_Q_le_T1 e) (f3_Q_relIndex_T2 hH) (f3_T2_nonab hH)
    (f3_K1_sq hH) (f3_K2_sq hH) (f3_K1_relIndex hH) (f3_K2_relIndex hH) (f3_K_ne hH)

end CFSG.OddStandard.HigherRank.YamadaG23
