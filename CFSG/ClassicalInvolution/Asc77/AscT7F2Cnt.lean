module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Ctx
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Out

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7F2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


namespace Hyp25T

variable (h : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')

include h

theorem inf_R_R' : Nat.card ↥(R ⊓ R') = 2 := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.hz.sq) h.hz.ne_one
  refine le_antisymm ?_ ?_
  · exact h.hΩ.card_le_two_of_le_inf h.hK h.hK' h.hs.hne.symm (h.hRsyl.2.1.to_le inf_le_left)
      (inf_le_left.trans h.hRsyl.1) (inf_le_right.trans h.hR'syl.1)
  · have h1 : Subgroup.zpowers z ≤ R ⊓ R' :=
      Subgroup.zpowers_le.mpr ⟨h.hzR.mem, h.hzR'.mem⟩
    have := Subgroup.card_le_of_le h1
    rwa [Nat.card_zpowers, hz2] at this

theorem card_RR : Nat.card ↥(R ⊔ R') * 2 = Nat.card R * Nat.card R' := by
  have hRN : R' ≤ Subgroup.normalizer (R : Set G) := T7A.le_normalizer_of_commutes h.hcomm
  have := T7A.card_sup_mul_card_inf hRN
  rw [h.inf_R_R', sup_comm] at this
  exact this


variable (h11 : C25_11 p f)

include h11

theorem Csub_inf_Csub_le : Csub S R ⊓ Csub S R' ≤ Subgroup.zpowers z := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hxS, hxR⟩ := mem_Csub.mp hx1
  obtain ⟨-, hxR'⟩ := mem_Csub.mp hx2
  have hle : R ⊔ R' ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hxR r hr))
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hxR' r hr))
  have hcent : x ∈ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have := h11 G Ω K K' W S R R' z t u₁ u₂ h.hyp
  rw [← this]
  exact ⟨hxS, hcent⟩

theorem mem_R'_of_mem_RR_of_mem_C {x : G} (hx : x ∈ R ⊔ R') (hxC : x ∈ Csub S R) : x ∈ R' := by
  obtain ⟨ρ, hρ, ρ', hρ', rfl⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute h.hcomm hx
  obtain ⟨hxS, hxR⟩ := mem_Csub.mp hxC
  have hρS : ρ ∈ (S : Subgroup G) := h.hRS hρ
  have hρC : ρ ∈ Csub S R := by
    refine mem_Csub.mpr ⟨hρS, fun r hr => ?_⟩
    have h1 : r * (ρ * ρ') = (ρ * ρ') * r := hxR r hr
    have h2 : r * ρ' = ρ' * r := h.hcomm r hr ρ' hρ'
    have h3 : r * ρ * ρ' = ρ * r * ρ' := by
      calc r * ρ * ρ' = r * (ρ * ρ') := by group
        _ = (ρ * ρ') * r := h1
        _ = ρ * (ρ' * r) := by group
        _ = ρ * (r * ρ') := by rw [h2]
        _ = ρ * r * ρ' := by group
    exact mul_right_cancel h3
  have hz : ρ ∈ Subgroup.zpowers z := h.Csub_inf_Csub_le h11 ⟨hρC, h.R_le_C' hρ⟩
  have hzR' : Subgroup.zpowers z ≤ R' := Subgroup.zpowers_le.mpr h.hzR'.mem
  exact R'.mul_mem (hzR' hz) hρ'

theorem mem_R_of_mem_RR_of_mem_C' {x : G} (hx : x ∈ R ⊔ R') (hxC : x ∈ Csub S R') : x ∈ R := by
  obtain ⟨ρ, hρ, ρ', hρ', rfl⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute h.hcomm hx
  obtain ⟨hxS, hxR⟩ := mem_Csub.mp hxC
  have hρ'S : ρ' ∈ (S : Subgroup G) := h.hR'S hρ'
  have hρ'C : ρ' ∈ Csub S R' := by
    refine mem_Csub.mpr ⟨hρ'S, fun r hr => ?_⟩
    have h1 : r * (ρ * ρ') = (ρ * ρ') * r := hxR r hr
    have h2 : ρ * r = r * ρ := h.hcomm ρ hρ r hr
    have h3 : ρ * (r * ρ') = ρ * (ρ' * r) := by
      calc ρ * (r * ρ') = (ρ * r) * ρ' := by group
        _ = (r * ρ) * ρ' := by rw [h2]
        _ = r * (ρ * ρ') := by group
        _ = (ρ * ρ') * r := h1
        _ = ρ * (ρ' * r) := by group
    exact mul_left_cancel h3
  have hz : ρ' ∈ Subgroup.zpowers z := h.Csub_inf_Csub_le h11 ⟨h.R'_le_C hρ', hρ'C⟩
  have hzR : Subgroup.zpowers z ≤ R := Subgroup.zpowers_le.mpr h.hzR.mem
  exact R.mul_mem hρ (hzR hz)


theorem P_inf_P' : Psub S R ⊓ Psub S R' ≤ R ⊔ R' := by
  rintro x ⟨hxP, hxP'⟩
  unfold Psub at hxP hxP'
  obtain ⟨ρ, hρ, m, hm, rfl⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
    (fun x hx y hy => (mem_Csub.mp hy).2 x hx) hxP
  obtain ⟨ρ', hρ', m', hm', hxe⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
    (fun x hx y hy => (mem_Csub.mp hy).2 x hx) hxP'
  obtain ⟨hmS, hmR⟩ := mem_Csub.mp hm
  obtain ⟨hm'S, hmR'⟩ := mem_Csub.mp hm'
  have hρS : ρ ∈ (S : Subgroup G) := h.hRS hρ
  have hρ'S : ρ' ∈ (S : Subgroup G) := h.hR'S hρ'
  set u := m * ρ'⁻¹ with hu
  have huS : u ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hmS ((S : Subgroup G).inv_mem hρ'S)
  have huC : u ∈ Csub S R := by
    refine mem_Csub.mpr ⟨huS, fun r hr => ?_⟩
    have h1 := hmR r hr
    have h2 := h.hcomm r hr ρ' hρ'
    calc r * (m * ρ'⁻¹) = (r * m) * ρ'⁻¹ := by group
      _ = (m * r) * ρ'⁻¹ := by rw [h1]
      _ = m * (r * ρ'⁻¹) := by group
      _ = m * (ρ'⁻¹ * r) := by
        congr 1
        calc r * ρ'⁻¹ = ρ'⁻¹ * (ρ' * r) * ρ'⁻¹ := by group
          _ = ρ'⁻¹ * (r * ρ') * ρ'⁻¹ := by rw [h2]
          _ = ρ'⁻¹ * r := by group
      _ = (m * ρ'⁻¹) * r := by group
  have huC' : u ∈ Csub S R' := by
    have hu2 : u = m' * ρ⁻¹ := by
      have h1 : ρ * m = ρ' * m' := hxe
      have hρm : ρ * m = m * ρ := (mem_Csub.mp hm).2 ρ hρ
      have hρ'm' : ρ' * m' = m' * ρ' := (mem_Csub.mp hm').2 ρ' hρ'
      have hρρ' : ρ * ρ' = ρ' * ρ := h.hcomm ρ hρ ρ' hρ'
      have h2 : m * ρ = m' * ρ' := by rw [← hρm, h1, hρ'm']
      calc u = m * ρ'⁻¹ := rfl
        _ = (m * ρ) * (ρ⁻¹ * ρ'⁻¹) := by group
        _ = (m' * ρ') * (ρ⁻¹ * ρ'⁻¹) := by rw [h2]
        _ = m' * (ρ' * ρ⁻¹ * ρ'⁻¹) := by group
        _ = m' * ρ⁻¹ := by
          congr 1
          have : ρ' * ρ⁻¹ = ρ⁻¹ * ρ' := by
            calc ρ' * ρ⁻¹ = ρ⁻¹ * (ρ * ρ') * ρ⁻¹ := by group
              _ = ρ⁻¹ * (ρ' * ρ) * ρ⁻¹ := by rw [hρρ']
              _ = ρ⁻¹ * ρ' := by group
          rw [this]; group
    refine mem_Csub.mpr ⟨huS, fun r hr => ?_⟩
    rw [hu2]
    have h1 := hmR' r hr
    have h2 := h.hcomm ρ hρ r hr
    calc r * (m' * ρ⁻¹) = (r * m') * ρ⁻¹ := by group
      _ = (m' * r) * ρ⁻¹ := by rw [h1]
      _ = m' * (r * ρ⁻¹) := by group
      _ = m' * (ρ⁻¹ * r) := by
        congr 1
        calc r * ρ⁻¹ = ρ⁻¹ * (ρ * r) * ρ⁻¹ := by group
          _ = ρ⁻¹ * (r * ρ) * ρ⁻¹ := by rw [h2]
          _ = ρ⁻¹ * r := by group
      _ = (m' * ρ⁻¹) * r := by group
  have hzu : u ∈ Subgroup.zpowers z := h.Csub_inf_Csub_le h11 ⟨huC, huC'⟩
  have hzR : Subgroup.zpowers z ≤ R := Subgroup.zpowers_le.mpr h.hzR.mem
  have hm_eq : m = u * ρ' := by rw [hu]; group
  have : ρ * m = ρ * u * ρ' := by rw [hm_eq]; group
  rw [this]
  exact Subgroup.mul_mem_sup (R.mul_mem hρ (hzR hzu)) hρ'

omit h11 in
theorem R_le_P : R ≤ Psub S R := le_sup_left

omit h11 in
theorem RR_le_P : R ⊔ R' ≤ Psub S R := sup_le le_sup_left (h.R'_le_C.trans le_sup_right)

omit h11 in
theorem RR_le_P' : R ⊔ R' ≤ Psub S R' := sup_le (h.R_le_C'.trans le_sup_right) le_sup_left

theorem P_inf_P'_eq : Psub S R ⊓ Psub S R' = R ⊔ R' :=
  le_antisymm (h.P_inf_P' h11) (le_inf h.RR_le_P h.RR_le_P')


theorem R'_inf_C'_le : R' ⊓ Csub S R' ≤ Subgroup.zpowers z := fun _ hx =>
  h.Csub_inf_Csub_le h11 ⟨h.R'_le_C hx.1, hx.2⟩

omit h11 in
theorem z_mem_C' : z ∈ Csub S R' :=
  mem_Csub.mpr ⟨h.hRS h.hzR.mem, fun r hr => h.hyp.hzS r (h.hR'S hr)⟩

theorem card_P' : Nat.card ↥(Psub S R') * 2 = Nat.card R' * Nat.card ↥(Csub S R') := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.hz.sq) h.hz.ne_one
  have hC : Csub S R' ≤ Subgroup.normalizer (R' : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_centralizes (mem_Csub.mp hx).2)
  have hprod := T7A.card_sup_mul_card_inf hC
  have heq : R' ⊓ Csub S R' = Subgroup.zpowers z :=
    le_antisymm (h.R'_inf_C'_le h11)
      (le_inf (Subgroup.zpowers_le.mpr h.hzR'.mem) (Subgroup.zpowers_le.mpr h.z_mem_C'))
  rw [heq, Nat.card_zpowers, hz2, sup_comm] at hprod
  exact hprod

omit h11 in
theorem relIndex_P'_le (h16 : C25_16 p f) : (Psub S R').relIndex (Nsub S R) ≤ 2 := by
  have hN2 : IsPGroup 2 ↥(Nsub S R) := S.isPGroup'.to_le (show Nsub S R ≤ _ from inf_le_left)
  have hF : ∀ y ∈ Nsub S R, ¬ IsFAut R' y := fun y hy =>
    h16 G Ω K K' W S R R' z t u₁ u₂ h.hyp y (mem_Nsub.mp hy).1
  have hB := T7F2.relIndex_sup_centralizer_le_two h.hqR' h.hzR' h.R'_le_N hN2
    (fun y hy => h.conj_R'_of_mem_N hy) hF
  have heq : Nsub S R ⊓ Subgroup.centralizer (R' : Set G) = Csub S R' := by
    ext x
    constructor
    · rintro ⟨hxN, hxc⟩
      exact mem_Csub.mpr ⟨(mem_Nsub.mp hxN).1, fun r hr => Subgroup.mem_centralizer_iff.mp hxc r hr⟩
    · intro hx
      exact ⟨h.C'_le_N hx, Subgroup.mem_centralizer_iff.mpr (mem_Csub.mp hx).2⟩
  rw [heq] at hB
  exact hB

theorem relIndex_R'_C_le (h16 : C25_16 p f) : R'.relIndex (Csub S R) ≤ 2 := by
  have hN2 : IsPGroup 2 ↥(Csub S R) := S.isPGroup'.to_le (show Csub S R ≤ _ from inf_le_left)
  have hF : ∀ y ∈ Csub S R, ¬ IsFAut R' y := fun y hy =>
    h16 G Ω K K' W S R R' z t u₁ u₂ h.hyp y (mem_Csub.mp hy).1
  have hB := T7F2.relIndex_sup_centralizer_le_two h.hqR' h.hzR' h.R'_le_C hN2
    (fun y hy => h.conj_R'_of_mem_N (h.C_le_N hy)) hF
  have hle : Csub S R ⊓ Subgroup.centralizer (R' : Set G) ≤ R' := by
    rintro x ⟨hxC, hxc⟩
    have hx' : x ∈ Csub S R' :=
      mem_Csub.mpr ⟨(mem_Csub.mp hxC).1, fun r hr => Subgroup.mem_centralizer_iff.mp hxc r hr⟩
    exact (Subgroup.zpowers_le.mpr h.hzR'.mem) (h.Csub_inf_Csub_le h11 ⟨hxC, hx'⟩)
  rw [sup_eq_left.mpr hle] at hB
  exact hB

omit h11 in
theorem card_C_eq : Nat.card ↥(Csub S R) = Nat.card ↥(Csub S R') := by
  rw [← h.conj_C', AscL62.natCard_conjSub]

theorem card_C_le (h16 : C25_16 p f) : Nat.card ↥(Csub S R') ≤ 2 * Nat.card R' := by
  have h1 := h.relIndex_R'_C_le h11 h16
  have h2 := Subgroup.relIndex_mul_card R' (Csub S R)
  rw [inf_eq_left.mpr h.R'_le_C] at h2
  calc Nat.card ↥(Csub S R') = Nat.card ↥(Csub S R) := h.card_C_eq.symm
    _ = R'.relIndex (Csub S R) * Nat.card R' := h2.symm
    _ ≤ 2 * Nat.card R' := Nat.mul_le_mul_right _ h1

omit h11 in
theorem card_N : (Psub S R').relIndex (Nsub S R) * Nat.card ↥(Psub S R') =
    Nat.card ↥(Nsub S R) := by
  have h2 := Subgroup.relIndex_mul_card (Psub S R') (Nsub S R)
  rwa [inf_eq_left.mpr h.P'_le_N] at h2

omit h11 in
theorem card_R'_eq : Nat.card R' = Nat.card R := h.card_R_eq.symm


theorem d8_of_lt (h16 : C25_16 p f) (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(Nsub S R)) :
    (Psub S R').relIndex (Nsub S R) = 2 ∧ Nat.card ↥(Csub S R') = 2 * Nat.card R' := by
  have hi := h.relIndex_P'_le h16
  have hc := h.card_C_le h11 h16
  have hq := h.card_P' h11
  have hρ := h.card_RR
  have hn := h.card_N
  have hrr : Nat.card R = Nat.card R' := h.card_R_eq
  have hdvd : Nat.card R ∣ Nat.card ↥(Csub S R') := Subgroup.card_dvd_of_le h.R_le_C'
  rw [hrr] at hdvd hρ
  obtain ⟨k, hk⟩ := hdvd
  have hr : 0 < Nat.card R' := Nat.card_pos
  have hρpos : 0 < Nat.card ↥(R ⊔ R') := Nat.card_pos
  have hnpos : 0 < Nat.card ↥(Nsub S R) := Nat.card_pos
  have hcpos : 0 < Nat.card ↥(Csub S R') := Nat.card_pos
  set r := Nat.card R' with hrdef
  set ρ := Nat.card ↥(R ⊔ R') with hρdef
  set c := Nat.card ↥(Csub S R') with hcdef
  set q := Nat.card ↥(Psub S R') with hqdef
  set n := Nat.card ↥(Nsub S R) with hndef
  set i := (Psub S R').relIndex (Nsub S R) with hidef
  have hk2 : k ≤ 2 := by
    have : r * k ≤ r * 2 := by rw [← hk]; linarith
    exact Nat.le_of_mul_le_mul_left this hr
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hqk : q = ρ * k := by
    have h2 : q * 2 = (ρ * k) * 2 := by
      calc q * 2 = r * c := hq
        _ = r * (r * k) := by rw [hk]
        _ = (r * r) * k := by ring
        _ = (ρ * 2) * k := by rw [← hρ]
        _ = (ρ * k) * 2 := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hi0 : i ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hn
    omega
  have hik : 2 * ρ < i * (ρ * k) := by
    rw [← hqk, hn]; exact hlt
  have hik2 : 2 < i * k := by
    have : ρ * 2 < ρ * (i * k) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  have hi2 : i = 2 ∧ k = 2 := by
    interval_cases i <;> interval_cases k <;> omega
  refine ⟨hi2.1, ?_⟩
  rw [hk, hi2.2]
  ring

theorem relIndex_P_eq (h16 : C25_16 p f)
    (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(Nsub S R)) :
    (Psub S R).relIndex (Nsub S R) = 2 := by
  have hP' := (h.d8_of_lt h11 h16 hlt).1
  have hn := h.card_N
  have h2 := Subgroup.relIndex_mul_card (Psub S R) (Nsub S R)
  rw [inf_eq_left.mpr h.P_le_N] at h2
  have hcard : Nat.card ↥(Psub S R) = Nat.card ↥(Psub S R') := by
    rw [← h.conj_P', AscL62.natCard_conjSub]
  rw [hcard] at h2
  rw [hP'] at hn
  have hq : 0 < Nat.card ↥(Psub S R') := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hq (h2.trans hn.symm)

end Hyp25T

end T7F2

end CFSG.ClassicalInvolution.Asc77
