module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step4e

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

namespace Q3Data

variable (d : Q3Data H)
include d

variable {T : Subgroup X}

theorem mem_normalizer_R0 (hq : h.IsQ3) (hF : Cat8.Q3Facts) (hT : IsPGroup 2 T)
    (hR0T : d.R0 ≤ T) (hTC : T ≤ centralizer ({d.b * d.z} : Set X)) {t : X}
    (htN : ∀ n ∈ d.NT T, t * n * t⁻¹ ∈ d.NT T) : t ∈ normalizer (d.R0 : Set X) := by
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  have hR0N : d.R0 ≤ d.NT T := le_inf hR0T le_normalizer
  have hE32 : ∀ E : Subgroup X, E ≤ d.R0M → (∀ u ∈ E, u * u = 1) → Nat.card E = 16 →
      ∀ e ∈ E ⊔ h.B, t * e * t⁻¹ ∈ d.R0 := by
    intro E hER hE2 hEc e he
    have hEB : E ⊔ h.B ≤ d.R0 := by
      rw [d.R0_eq]
      exact sup_le_sup_right hER _
    have hbN : d.b ∈ normalizer (E : Set X) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
        d.b_comm_of_mem_M3 (d.RM_le (hER hr).1))
    have hEB2 : ∀ u ∈ E ⊔ h.B, u * u = 1 := by
      intro u hu
      rw [d.B_eq] at hu
      obtain ⟨m, hm, hum⟩ := Eight.mem_sup_zpowers_cases hbN d.b_mul_self hu
      rcases hum with hum | hum <;> rw [hum]
      · exact hE2 m hm
      · have hmb := d.b_comm_of_mem_M3 (d.RM_le (hER hm).1)
        calc m * d.b * (m * d.b) = m * (d.b * m) * d.b := by group
          _ = m * (m * d.b) * d.b := by rw [hmb]
          _ = (m * m) * (d.b * d.b) := by group
          _ = 1 := by rw [hE2 m hm, d.b_mul_self, one_mul]
    have hEBc : Nat.card ↥(E ⊔ h.B) = 32 := by
      rw [d.card_sup_B hCF1 hCF2 (hER.trans (inf_le_left.trans d.RM_le)), hEc]
    set E' := conjugate (E ⊔ h.B) t⁻¹ with hE'
    have hE'N : E' ≤ d.NT T := by
      intro y hy
      rw [hE', mem_conjugate_iff] at hy
      have := htN _ (hR0N (hEB hy))
      rwa [show t * (t⁻¹ * y * t⁻¹⁻¹) * t⁻¹ = y by group] at this
    have hE'2 : ∀ u ∈ E', u * u = 1 := by
      intro u hu
      rw [hE', mem_conjugate_iff] at hu
      have := hEB2 _ hu
      calc u * u = t * ((t⁻¹ * u * t⁻¹⁻¹) * (t⁻¹ * u * t⁻¹⁻¹)) * t⁻¹ := by group
        _ = 1 := by rw [this]; group
    have hE'c : Nat.card E' = 32 := by rw [hE', Eight.card_conjugate_eq, hEBc]
    have hle := d.E32_le_R0 hq hF hT hR0T hTC hE'N hE'2 hE'c
    apply hle
    rw [hE', mem_conjugate_iff]
    rwa [show t⁻¹ * (t * e * t⁻¹) * t⁻¹⁻¹ = e by group]
  have hS := d.R0M_le_closure hCF1 hCF2
  have hSne : ∃ y : X, ∃ A : Subgroup X, A ≤ d.R0M ∧ (∀ u ∈ A, u * u = 1) ∧
      Nat.card A = 16 ∧ y ∈ A := by
    by_contra hne
    have hemp : {y | ∃ A : Subgroup X, A ≤ d.R0M ∧ (∀ u ∈ A, u * u = 1) ∧
        Nat.card A = 16 ∧ y ∈ A} = (∅ : Set X) :=
      Set.eq_empty_iff_forall_notMem.mpr fun y hy => hne ⟨y, hy⟩
    have h1 := hS d.z_mem_R0M
    rw [hemp, Subgroup.closure_empty, mem_bot] at h1
    exact d.z_ne h1
  obtain ⟨-, E₁, hE₁R, hE₁2, hE₁c, -⟩ := hSne
  have hb : t * d.b * t⁻¹ ∈ d.R0 :=
    hE32 E₁ hE₁R hE₁2 hE₁c _ (mem_sup_right (d.B_eq ▸ mem_zpowers d.b))
  have hR0M : ∀ y ∈ d.R0M, t * y * t⁻¹ ∈ d.R0 := by
    have hle : closure {y | ∃ A : Subgroup X, A ≤ d.R0M ∧ (∀ u ∈ A, u * u = 1) ∧
        Nat.card A = 16 ∧ y ∈ A} ≤ d.R0.comap (MulAut.conj t).toMonoidHom := by
      rw [closure_le]
      rintro y ⟨A, hA, hA2, hAc, hy⟩
      show (MulAut.conj t) y ∈ d.R0
      rw [MulAut.conj_apply]
      exact hE32 A hA hA2 hAc y (mem_sup_left hy)
    intro y hy
    have := hle (hS hy)
    rw [mem_comap] at this
    simpa [MulAut.conj_apply] using this
  have hall : ∀ y ∈ d.R0, t * y * t⁻¹ ∈ d.R0 := by
    intro y hy
    have hbN : d.b ∈ normalizer (d.R0M : Set X) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
        d.b_comm_of_mem_M3 (d.RM_le hr.1))
    rw [d.R0_eq, d.B_eq] at hy
    obtain ⟨m, hm, hym⟩ := Eight.mem_sup_zpowers_cases hbN d.b_mul_self hy
    rcases hym with hym | hym <;> rw [hym]
    · exact hR0M m hm
    · rw [show t * (m * d.b) * t⁻¹ = (t * m * t⁻¹) * (t * d.b * t⁻¹) by group]
      exact mul_mem (hR0M m hm) hb
  have := Eight.mem_normalizer_of_conj_mem (C := d.R0) (s := t⁻¹) fun c hc => by
    rw [inv_inv]
    exact hall c hc
  simpa using inv_mem this

theorem bz_not_conj_tz (hq : h.IsQ3) (hF : Cat8.Q3Facts) (w : X) :
    w⁻¹ * (d.b * d.z) * w ≠ d.tau * d.z := by
  intro hw
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  set C := centralizer ({d.b * d.z} : Set X) with hC
  obtain ⟨P, hPz, hP2, hPc⟩ := d.exists_two_subgroup_centralizer_z hq hF
  obtain ⟨c, hc⟩ := d.exists_z_conj_tz hq hF
  have hv : (w * c⁻¹)⁻¹ * (d.b * d.z) * (w * c⁻¹) = d.z := by
    rw [show (w * c⁻¹)⁻¹ * (d.b * d.z) * (w * c⁻¹) = c * (w⁻¹ * (d.b * d.z) * w) * c⁻¹ by
      group, hw, ← hc]
    group
  have hP' : conjugate P (w * c⁻¹)⁻¹ ≤ C := conjugate_le_centralizer (by rw [hv]; exact hPz)
  obtain ⟨T₀, hT₀⟩ := ((d.isPGroup_R0 hCF1 hCF2).comap_subtype (K := C)).exists_le_sylow
  set T := (T₀ : Subgroup C).map C.subtype with hTdef
  have hTC : T ≤ C := map_subtype_le _
  have hT2 : IsPGroup 2 T := T₀.isPGroup'.map _
  have hR0T : d.R0 ≤ T := fun r hr => ⟨⟨r, d.R0_le_centralizer_bz hr⟩, hT₀ hr, rfl⟩
  have hTc : 512 ≤ Nat.card T := by
    have hP'2 : IsPGroup 2 ↥(conjugate P (w * c⁻¹)⁻¹) := hP2.map _
    have h1 := card_le_card_sylow (hP'2.comap_subtype (K := C)) T₀
    rw [← card_map_of_injective C.subtype_injective, map_comap_eq, range_subtype,
      inf_eq_right.mpr hP', Eight.card_conjugate_eq, hPc] at h1
    rw [hTdef, card_map_of_injective C.subtype_injective]
    exact h1
  have hN := d.card_N_le hq hF hT2 hR0T hTC
  have hne : d.NT T ≠ T := fun h1 => by
    rw [h1] at hN
    omega
  obtain ⟨t, htT, htN, htn⟩ := Eight.exists_mem_normalizer_not_mem hT2 inf_le_left hne
  exact htN ⟨htT, d.mem_normalizer_R0 hq hF hT2 hR0T hTC htn⟩

theorem not_fused (hq : h.IsQ3) (hF : Cat8.Q3Facts) (w : X) :
    w⁻¹ * h.a * w ≠ d.b ∧ w⁻¹ * h.a * w ≠ d.b * d.z ∧ w⁻¹ * h.a * w ≠ d.tau * d.z ∧
      w⁻¹ * d.b * w ≠ d.b * d.z ∧ w⁻¹ * d.b * w ≠ d.tau * d.z ∧
      w⁻¹ * (d.b * d.z) * w ≠ d.tau * d.z :=
  ⟨d.a_not_conj_b hF.simple hF.inner w, d.a_not_conj_bz hF.simple hF.inner w,
    d.a_not_conj_tz hq hF.simple hF.inner hF.out w,
    d.b_not_conj_bz hq hF.simple hF.inner hF.innerInv hF.noNilp w,
    d.b_not_conj_tz hq hF.simple hF.inner hF.out w, d.bz_not_conj_tz hq hF w⟩

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
