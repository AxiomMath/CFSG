module

public import CFSG.ClassicalInvolution.Asc77.AscT7TC15
public import CFSG.ClassicalInvolution.Asc77.AscT7U1
public import CFSG.ClassicalInvolution.Asc77.AscT7U7
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ : G}


theorem exists_ff_of_pure_mixed (h11 : C25_11 p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {c : G} (hcS : c ∈ (S : Subgroup G)) (hc2 : c * c = 1) (hcC : ∀ x ∈ R, c * x = x * c)
    (hFc : IsFAut R' c) :
    ∃ e ∈ (S : Subgroup G), e * e = 1 ∧ IsFAut R e ∧ IsFAut R' e := by
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hz2 : z * z = 1 := h.hz.sq
  have ht'inv : t'⁻¹ = t' := h.ht'inv
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hV2 : IsPGroup 2 ↥(T7F2.Nsub S R) := S.isPGroup'.to_le inf_le_left
  have hcN : c ∈ T7F2.Nsub S R :=
    h.mem_N_of_conj_R' hcS (mem_normalizer_iff_conjSub_eq.mp hFc.1)
  obtain ⟨b, hb⟩ : ∃ b : G, b = t' * c * t'⁻¹ := ⟨_, rfl⟩
  have hbN : b ∈ T7F2.Nsub S R := hb ▸ h.N_conj hcN
  have hbS : b ∈ (S : Subgroup G) := (T7F2.mem_Nsub.mp hbN).1
  have hb2 : b * b = 1 := by
    calc b * b = t' * (c * c) * t'⁻¹ := by rw [hb]; group
      _ = 1 := by rw [hc2]; group
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hFb : IsFAut R b := by
    have := T7U.isFAut_conjSub hFc t'
    rwa [h.ht'R', ← hb] at this
  have hbC : ∀ x ∈ R', b * x = x * b := by
    intro x hx
    have hx' : t'⁻¹ * x * t' ∈ R := by
      have : x ∈ conjSub t' R := by rw [h.ht'R]; exact hx
      exact mem_conjSub_iff.mp this
    have h1 := hcC _ hx'
    calc b * x = t' * (c * (t'⁻¹ * x * t')) * t'⁻¹ := by rw [hb]; group
      _ = t' * ((t'⁻¹ * x * t') * c) * t'⁻¹ := by rw [h1]
      _ = x * b := by rw [hb]; group
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, x₀ = c * b * c * b := ⟨_, rfl⟩
  have hx₀S : x₀ ∈ (S : Subgroup G) := by
    rw [hx₀]
    exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hcS hbS)
      hcS) hbS
  have hx₀i : x₀⁻¹ = b * c * b * c := by
    rw [hx₀]; simp only [mul_inv_rev, hbi, hci]; group
  have hbR : ∀ r ∈ R, b * r * b ∈ R := fun r hr => by
    have := conj_mem_conjSub (n := b) hr
    rw [(T7F2.mem_Nsub.mp hbN).2] at this
    simpa [hbi] using this
  have hcR' : ∀ r ∈ R', c * r * c ∈ R' := fun r hr => by
    have := conj_mem_conjSub (n := c) hr
    rw [mem_normalizer_iff_conjSub_eq.mp hFc.1] at this
    simpa [hci] using this
  have hx₀R : ∀ r ∈ R, x₀ * r * x₀⁻¹ = r := by
    intro r hr
    obtain ⟨r₁, hr₁⟩ : ∃ r₁ : G, r₁ = b * r * b := ⟨_, rfl⟩
    have hr₁R : r₁ ∈ R := hr₁ ▸ hbR r hr
    have h1 : c * r₁ = r₁ * c := hcC r₁ hr₁R
    have h2 : c * r = r * c := hcC r hr
    have h3 : b * r₁ * b = r := by
      rw [hr₁]
      calc b * (b * r * b) * b = (b * b) * r * (b * b) := by group
        _ = r := by rw [hb2]; group
    have e1 : c * r₁ * c = r₁ := by
      calc c * r₁ * c = (c * r₁) * c := rfl
        _ = (r₁ * c) * c := by rw [h1]
        _ = r₁ * (c * c) := by rw [mul_assoc]
        _ = r₁ := by rw [hc2, mul_one]
    have e2 : c * r * c = r := by
      calc c * r * c = (r * c) * c := by rw [h2]
        _ = r * (c * c) := by rw [mul_assoc]
        _ = r := by rw [hc2, mul_one]
    calc x₀ * r * x₀⁻¹ = (c * b * c * b) * r * (b * c * b * c) := by rw [hx₀i, hx₀]
      _ = c * b * (c * (b * r * b) * c) * b * c := by group
      _ = c * b * (c * r₁ * c) * b * c := by rw [hr₁]
      _ = c * (b * r₁ * b) * c := by rw [e1]; group
      _ = c * r * c := by rw [h3]
      _ = r := e2
  have hx₀R' : ∀ r ∈ R', x₀ * r * x₀⁻¹ = r := by
    intro r hr
    obtain ⟨r₂, hr₂⟩ : ∃ r₂ : G, r₂ = c * r * c := ⟨_, rfl⟩
    have hr₂R : r₂ ∈ R' := hr₂ ▸ hcR' r hr
    have h1 : b * r = r * b := hbC r hr
    have h2 : b * r₂ = r₂ * b := hbC r₂ hr₂R
    have e1 : b * r * b = r := by
      calc b * r * b = (r * b) * b := by rw [h1]
        _ = r * (b * b) := by rw [mul_assoc]
        _ = r := by rw [hb2, mul_one]
    have e2 : b * r₂ * b = r₂ := by
      calc b * r₂ * b = (r₂ * b) * b := by rw [h2]
        _ = r₂ * (b * b) := by rw [mul_assoc]
        _ = r₂ := by rw [hb2, mul_one]
    have e3 : c * r₂ * c = r := by
      rw [hr₂]
      calc c * (c * r * c) * c = (c * c) * r * (c * c) := by group
        _ = r := by rw [hc2]; group
    calc x₀ * r * x₀⁻¹ = (c * b * c * b) * r * (b * c * b * c) := by rw [hx₀i, hx₀]
      _ = c * b * c * (b * r * b) * c * b * c := by group
      _ = c * b * (c * r * c) * b * c := by rw [e1]; group
      _ = c * (b * r₂ * b) * c := by rw [hr₂]; group
      _ = c * r₂ * c := by rw [e2]
      _ = r := e3
  have hx₀z : x₀ ∈ Subgroup.zpowers z := by
    have hcen : x₀ ∈ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
      have hle : R ⊔ R' ≤ Subgroup.centralizer ({x₀} : Set G) := by
        refine sup_le (fun r hr => ?_) (fun r hr => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (mul_inv_eq_iff_eq_mul.mp (hx₀R r hr)).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (mul_inv_eq_iff_eq_mul.mp (hx₀R' r hr)).symm
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    have := h11 G Ω K K' W S R R' z t u₁ u₂ hyp
    rw [← this]
    exact Subgroup.mem_inf.mpr ⟨hx₀S, hcen⟩
  have hFe : IsFAut R (c * b) := by
    have h1 : c * b = b * (b⁻¹ * c * b) := by group
    rw [h1]
    refine T7U.isFAut_mul_of_centralizes (fun x hx => ?_) hFb
    have hx' : b * x * b⁻¹ ∈ R := by
      have := conj_mem_conjSub (n := b) hx
      rwa [(T7F2.mem_Nsub.mp hbN).2] at this
    have := hcC _ hx'
    calc b⁻¹ * c * b * x = b⁻¹ * (c * (b * x * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * x * b⁻¹) * c) * b := by rw [this]
      _ = x * (b⁻¹ * c * b) := by group
  have hFe' : IsFAut R' (c * b) := T7U.isFAut_mul_of_centralizes hbC hFc
  have heN : c * b ∈ T7F2.Nsub S R := (T7F2.Nsub S R).mul_mem hcN hbN
  have he2 : (c * b) * (c * b) ∈ Subgroup.zpowers z := by
    rw [show (c * b) * (c * b) = x₀ by rw [hx₀]; group]
    exact hx₀z
  obtain ⟨r, hr, hre2, hFr⟩ := T7U.exists_involution_of_isFAut h.hqR h.hzR h.R_le_N hV2
    (fun y hy => (T7F2.mem_Nsub.mp hy).2) heN hFe he2
  refine ⟨c * b * r, (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hcS hbS) (h.hRS hr),
    hre2, hFr, ?_⟩
  exact T7U.isFAut_mul_of_centralizes (fun x hx => h.hcomm r hr x hx) hFe'

theorem exists_ff_of_inner (h11 : C25_11 p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF' : IsFAut R' a)
    (hin : ∃ r ∈ R, ∀ x ∈ R, (r⁻¹ * a) * x = x * (r⁻¹ * a)) :
    ∃ e ∈ (S : Subgroup G), e * e = 1 ∧ IsFAut R e ∧ IsFAut R' e := by
  obtain ⟨r, hrR, hrc⟩ := hin
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hV2 : IsPGroup 2 ↥(T7F2.Nsub S R) := S.isPGroup'.to_le inf_le_left
  have haN : a ∈ T7F2.Nsub S R :=
    h.mem_N_of_conj_R' haS (mem_normalizer_iff_conjSub_eq.mp hF'.1)
  have hrN : r⁻¹ ∈ T7F2.Nsub S R := (T7F2.Nsub S R).inv_mem (h.R_le_N hrR)
  have hc₀N : r⁻¹ * a ∈ T7F2.Nsub S R := (T7F2.Nsub S R).mul_mem hrN haN
  have hc₀S : r⁻¹ * a ∈ (S : Subgroup G) := (T7F2.mem_Nsub.mp hc₀N).1
  have hF₀ : IsFAut R' (r⁻¹ * a) := by
    have h1 : r⁻¹ * a = a * (a⁻¹ * r⁻¹ * a) := by group
    rw [h1]
    refine T7U.isFAut_mul_of_centralizes (fun x hx => ?_) hF'
    have hx' : a * x * a⁻¹ ∈ R' := by
      have := conj_mem_conjSub (n := a) hx
      rwa [mem_normalizer_iff_conjSub_eq.mp hF'.1] at this
    have h2 : r⁻¹ * (a * x * a⁻¹) = (a * x * a⁻¹) * r⁻¹ :=
      (Commute.inv_left (show Commute r (a * x * a⁻¹) from h.hcomm r hrR _ hx')).eq
    calc a⁻¹ * r⁻¹ * a * x = a⁻¹ * (r⁻¹ * (a * x * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * x * a⁻¹) * r⁻¹) * a := by rw [h2]
      _ = x * (a⁻¹ * r⁻¹ * a) := by group
  have hsq : (r⁻¹ * a) * (r⁻¹ * a) ∈ Subgroup.zpowers z := by
    refine T7U.inf_centralizer_le_zpowers h.hqR h.hzR (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have h1 : (r⁻¹ * a) * (r⁻¹ * a) = r⁻¹ * (a * r⁻¹ * a⁻¹) * (a * a) := by group
      rw [h1, ha2, mul_one]
      refine R.mul_mem (R.inv_mem hrR) ?_
      have := conj_mem_conjSub (n := a) (R.inv_mem hrR)
      rwa [(T7F2.mem_Nsub.mp haN).2] at this
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      calc x * ((r⁻¹ * a) * (r⁻¹ * a)) = (x * (r⁻¹ * a)) * (r⁻¹ * a) := by group
        _ = ((r⁻¹ * a) * x) * (r⁻¹ * a) := by rw [hrc x hx]
        _ = (r⁻¹ * a) * (x * (r⁻¹ * a)) := by group
        _ = (r⁻¹ * a) * ((r⁻¹ * a) * x) := by rw [hrc x hx]
        _ = ((r⁻¹ * a) * (r⁻¹ * a)) * x := by group
  obtain ⟨r', hr', hc2, hFc⟩ := T7U.exists_involution_of_isFAut h.hqR' h.hzR' h.R'_le_N hV2
    (fun y hy => h.conj_R'_of_mem_N hy) hc₀N hF₀ hsq
  refine exists_ff_of_pure_mixed h11 hyp (c := r⁻¹ * a * r')
    ((S : Subgroup G).mul_mem hc₀S (h.hR'S hr')) hc2 (fun x hx => ?_) hFc
  calc (r⁻¹ * a * r') * x = (r⁻¹ * a) * (r' * x) := by group
    _ = (r⁻¹ * a) * (x * r') := by rw [(h.hcomm x hx r' hr').symm]
    _ = ((r⁻¹ * a) * x) * r' := by group
    _ = (x * (r⁻¹ * a)) * r' := by rw [hrc x hx]
    _ = x * (r⁻¹ * a * r') := by group

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
