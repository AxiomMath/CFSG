module

public import CFSG.LargeExtraspecial.S4Span

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem commute_of_fix {k₁ k₂ x b c : G} (hb : k₁ * S.z * k₁⁻¹ = b)
    (hc : k₂ * S.z * k₂⁻¹ = c) (hbQ : b ∈ S.QG) (hbz : b ≠ S.z) (hcQ : c ∈ S.QG)
    (hx : x ∈ S.L0 k₁) (hxQ : x ∉ S.QG) (hxc : x * c * x⁻¹ = c ∨ x * c * x⁻¹ = c * S.z) :
    b * c = c * b := by
  set T := S.conjBy k₁ with hT
  have hTz : T.z = b := hb
  have hcc : c * c = 1 := by rw [← hc]; exact (S.conjBy k₂).z_mul_z
  have hbb : b * b = 1 := by rw [← hTz]; exact T.z_mul_z
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hzb : S.z ∈ T.QG := S.z_mem_Qa_of_mem_QG hb hbQ hbz
  by_contra hcomm
  have hbc : b * c = S.z * (c * b) := (S.mul_comm_or hbQ hcQ).resolve_left hcomm
  have hzc : c * S.z = S.z * c := S.z_comm_QG hcQ
  have hbz' : b * S.z = S.z * b := S.z_comm_QG hbQ
  have hcbc : c * b * c⁻¹ = b * S.z := by
    have e : c * b = S.z * (b * c) := by
      rw [hbc, ← mul_assoc S.z S.z, S.z_mul_z, one_mul]
    rw [e, hbz']
    group
  have hxbz : x ∈ S.Qa (c * k₁) := by
    have h1 : c * x * c⁻¹ ∈ S.Qa (c * k₁) := conj_mem_Qa_mul S hx.1
    have h2 : S.z ∈ S.Qa (c * k₁) := by
      have := conj_mem_Qa_mul (S := S) (h := c) hzb
      rwa [hzc, mul_assoc, mul_inv_cancel, mul_one] at this
    rcases hxc with h | h
    · have e : c * x * c⁻¹ = x := by
        have hxc' : x * c = c * x := by
          calc x * c = x * c * x⁻¹ * x := by group
            _ = c * x := by rw [h]
        rw [← hxc', mul_assoc, mul_inv_cancel, mul_one]
      rwa [e] at h1
    · have e : c * x * c⁻¹ = S.z * x := by
        have hxc' : x * c = c * S.z * x := by
          calc x * c = x * c * x⁻¹ * x := by group
            _ = c * S.z * x := by rw [h]
        calc c * x * c⁻¹ = c * x * c := by rw [hci]
          _ = c * (x * c) := by group
          _ = c * (c * S.z * x) := by rw [hxc']
          _ = (c * c) * S.z * x := by group
          _ = S.z * x := by rw [hcc, one_mul]
      have := mul_mem (inv_mem h2) h1
      rwa [e, ← mul_assoc, inv_mul_cancel, one_mul] at this
  obtain ⟨u, huQ, huz⟩ := T.exists_conj_eq_mul_z hzb S.z_ne_one (by rw [hTz]; exact hbz.symm)
  have hub : u * b * u⁻¹ = b := by
    rw [← hTz, T.z_comm_QG huQ]
    group
  have hz : (u * (c * k₁)) * S.z * (u * (c * k₁))⁻¹ = 1 * S.z * 1⁻¹ := by
    calc (u * (c * k₁)) * S.z * (u * (c * k₁))⁻¹ = u * (c * (k₁ * S.z * k₁⁻¹) * c⁻¹) * u⁻¹ := by
          group
      _ = u * b * u⁻¹ * (u * S.z * u⁻¹) := by rw [hb, hcbc]; group
      _ = b * (S.z * b) := by rw [hub, huz, hTz]
      _ = 1 * S.z * 1⁻¹ := by rw [← mul_assoc, hbz', mul_assoc, hbb, mul_one]; group
  have huxQ : u * x * u⁻¹ ∈ S.QG := by
    have := conj_mem_Qa_mul (S := S) (h := u) hxbz
    rwa [S.Qa_eq_of_conj_eq hz, S.Qa_one] at this
  apply hxQ
  rcases T.mul_comm_or huQ hx.1 with h | h
  · rwa [h, mul_assoc, mul_inv_cancel, mul_one] at huxQ
  · have e : u * x * u⁻¹ = b * x := by
      rw [h, hTz]
      group
    rw [e] at huxQ
    have := mul_mem (inv_mem hbQ) huxQ
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this

variable {g : G}

theorem lemma_4_1 (H : Hyp4 S g) (h : S.M)
    (hx : ∃ x ∈ S.Lbar ((h : G) * g), x ∈ normalizer (S.Lbar g : Set S.O) ∧ x ≠ 1) :
    (g * S.z * g⁻¹) * ((h : G) * g * S.z * ((h : G) * g)⁻¹) =
      ((h : G) * g * S.z * ((h : G) * g)⁻¹) * (g * S.z * g⁻¹) := by
  obtain ⟨x, hxL, hxN, hx1⟩ := hx
  obtain ⟨y, hy, rfl⟩ := (mem_Lbar S).mp hxL
  have hyQ : (y : G) ∉ S.QG := fun h' => hx1 ((S.ρ_eq_one_iff y).mpr h')
  have hfix := fix_of_mem_normalizer H hxN
  rw [S.ρ_cl y H.conj_mem] at hfix
  have hyc := (S.cl_eq_cl_iff H.conj_mem (S.conj_mem_QG y.2 H.conj_mem)).mp hfix.symm
  have := commute_of_fix rfl rfl (conj_mem_QG' S h.2 H.conj_mem) (conj_ne_z' S h.2 H.conj_ne)
    H.conj_mem hy hyQ hyc
  exact this.symm

theorem lemma_4_1_conj (H : Hyp4 S g) (h₁ h₂ : S.M)
    (hx : ∃ x ∈ S.Lbar ((h₁ : G) * g), x ∈ normalizer (S.Lbar ((h₂ : G) * g) : Set S.O) ∧ x ≠ 1) :
    ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹) * ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) =
      ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) * ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹) := by
  obtain ⟨x, hxL, hxN, hx1⟩ := hx
  obtain ⟨y, hy, rfl⟩ := (mem_Lbar S).mp hxL
  have hyQ : (y : G) ∉ S.QG := fun h' => hx1 ((S.ρ_eq_one_iff y).mpr h')
  have hfix : ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹)) =
        S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) := by
    have hmem : ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹)) ∈
          fixSub S (S.Lbar ((h₂ : G) * g)) := by
      intro w hw
      have hw' : (S.ρ y)⁻¹ * w * S.ρ y ∈ S.Lbar ((h₂ : G) * g) := by
        have := (mem_normalizer_iff.mp (inv_mem hxN) w).mp hw
        simpa using this
      have h1 := cl_mem_fixSub H h₂ _ hw'
      simp only [coe_mul_apply] at h1
      have h2 := congrArg ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
      rwa [apply_inv_apply_O] at h2
    refine eq_cl_of_mem_fixSub H h₂ hmem ?_
    rw [Ne, LinearEquiv.map_eq_zero_iff]
    exact cl_conj_ne_zero H h₂
  have haQ₂ := conj_mem_QG' S h₂.2 H.conj_mem
  rw [S.ρ_cl y haQ₂] at hfix
  have hyc := (S.cl_eq_cl_iff haQ₂ (S.conj_mem_QG y.2 haQ₂)).mp hfix.symm
  exact commute_of_fix rfl rfl (conj_mem_QG' S h₁.2 H.conj_mem) (conj_ne_z' S h₁.2 H.conj_ne)
    haQ₂ hy hyQ hyc

theorem commute_of_mem_Dset (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) {h₁ h₂ : S.M}
    (ht₁ : t ∈ S.Lbar ((h₁ : G) * g)) (ht₂ : t ∈ S.Lbar ((h₂ : G) * g)) :
    ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹) * ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) =
      ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) * ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹) :=
  lemma_4_1_conj H h₁ h₂ ⟨t, ht₁, le_normalizer ht₂, ht1⟩

end CFSG.LargeExtraspecial.S4
