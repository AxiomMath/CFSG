module

public import CFSG.ClassicalInvolution.Asc77.AscC25V5
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Frat
public import CFSG.ClassicalInvolution.Asc77.AscC25V4
public import CFSG.ClassicalInvolution.Asc77.AscT7U1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] {R : Subgroup G} {z : G}

theorem comm_z_of_mem (hz : IsUniqueInvolution R z) {r : G} (hr : r ∈ R) :
    r * z = z * r := by
  have h1 : r * z * r⁻¹ ∈ R := by
    have := conj_mem_conjSub (n := r) hz.mem
    rwa [conjSub_eq_self_of_mem hr] at this
  have h2 : (r * z * r⁻¹) * (r * z * r⁻¹) = 1 := by
    calc (r * z * r⁻¹) * (r * z * r⁻¹) = r * (z * z) * r⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rcases hz.unique _ h1 h2 with h | h
  · exfalso
    apply hz.ne_one
    calc z = r⁻¹ * (r * z * r⁻¹) * r := by group
      _ = 1 := by rw [h]; group
  · calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [h]

end Basic

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem no_sq_eq_z (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {t' g : G}
    (hg : g * z * g⁻¹ = t') (hzt' : z ≠ t') (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t' * z) {b : G}
    (hbt : b * t' = t' * b) : b * b ≠ z := by
  intro hbb
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hx : (g⁻¹ * b * g) * z * (g⁻¹ * b * g)⁻¹ = z := by
    calc (g⁻¹ * b * g) * z * (g⁻¹ * b * g)⁻¹ = g⁻¹ * b * (g * z * g⁻¹) * b⁻¹ * g := by group
      _ = g⁻¹ * b * t' * b⁻¹ * g := by rw [hg]
      _ = g⁻¹ * (b * t' * b⁻¹) * g := by group
      _ = g⁻¹ * t' * g := by rw [hbt]; group
      _ = z := by rw [← hg]; group
  have h1 := T7T.twin_sq hs hx
  have h2 : conjSub (b * b) (conjSub g K) = conjSub g K := by
    calc conjSub (b * b) (conjSub g K) = conjSub ((b * b) * g) K := (conjSub_mul (b * b) g K).symm
      _ = conjSub (g * ((g⁻¹ * b * g) * (g⁻¹ * b * g))) K := by congr 1; group
      _ = conjSub g (conjSub ((g⁻¹ * b * g) * (g⁻¹ * b * g)) K) := by rw [conjSub_mul]
      _ = conjSub g K := by rw [h1]
  rw [hbb] at h2
  exact T7G2.not_normalizes_of_nonfused hyp hg hzt' hnf h2

theorem false_of_comm (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {g : G}
    (hg : g * z * g⁻¹ = t') {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (hF' : IsFAut R' a) (hZ : z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)))
    (hcomm : a * t' = t' * a) : False := by
  have hz2 : z * z = 1 := h.hz.sq
  have hz1 : z ≠ 1 := h.hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := h.hyp.hzS
  have haz : a * z = z * a := hzS a haS
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact T7U.not_isFAut_of_mem h.hqR' h.hzR' R'.one_mem hF'
  have haz' : a ≠ z := by
    rintro rfl
    exact T7U.not_isFAut_of_mem h.hqR' h.hzR' h.hzR'.mem hF'
  have ht'ne : t' ≠ z := by
    intro heq
    apply h.t'_not_mem_N
    rw [heq]
    exact h.R_le_N h.hzR.mem
  have hyp' : Hyp25 p f Ω K K' W S R R' z t' u₁ u₂ :=
    { h.hyp with ht := ⟨h.ht'S, ht'ne, g, hg⟩ }
  obtain ⟨hA4, hAmem⟩ := fourGroup ha2 hz2 haz ha1 hz1 haz'
  have hzA : z ∈ Subgroup.closure ({a, z} : Set G) := Subgroup.subset_closure (by simp)
  have ht'z : t' * z = z * t' := hzS t' h.ht'S
  have hcommA : ∀ x ∈ Subgroup.closure ({a, z} : Set G), x * t' = t' * x := by
    intro x hx
    rcases hAmem x hx with rfl | rfl | rfl | rfl
    · simp
    · exact hcomm
    · exact ht'z.symm
    · calc a * z * t' = a * (z * t') := by rw [mul_assoc]
        _ = a * (t' * z) := by rw [ht'z]
        _ = (a * t') * z := by rw [mul_assoc]
        _ = (t' * a) * z := by rw [hcomm]
        _ = t' * (a * z) := by rw [mul_assoc]
  obtain ⟨a', ha'A, ha'1, hna'⟩ := T7T.c25_3_proved (p := p) (f := f) G Ω K K' W S R R' z t' u₁
    u₂ hyp' _ hA4 hzA hcommA
  have hV2 : IsPGroup 2 ↥(T7F2.Nsub S R) := S.isPGroup'.to_le inf_le_left
  have haN : a ∈ T7F2.Nsub S R :=
    h.mem_N_of_conj_R' haS (mem_normalizer_iff_conjSub_eq.mp hF'.1)
  rcases hAmem a' ha'A with rfl | rfl | rfl | rfl
  · exact ha'1 rfl
  · exact hna' hZ
  · exact hna' (T7T.mem_zStarOf_centralizer_self _)
  · apply hna'
    obtain ⟨r, hr, hra⟩ := exists_conj_az h.hqR' h.hzR' hV2 h.R'_le_N
      (fun y hy => h.conj_R'_of_mem_N hy) haN hF' ⟨0, by rw [ha2]; simp⟩
    have hcz : r⁻¹ * z * r⁻¹⁻¹ = z := by
      have := comm_z_of_mem h.hzR' (R'.inv_mem hr)
      rw [inv_inv]
      calc r⁻¹ * z * r = z * r⁻¹ * r := by rw [this]
        _ = z := by group
    have hconj : a * z = r⁻¹ * a * r⁻¹⁻¹ := by rw [inv_inv, hra]
    rw [hconj]
    exact (zStar_conj_iff hcz).mpr hZ

theorem exists_comm_swap_of_ff (h11 : C25_11 p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R a)
    (hF' : IsFAut R' a) :
    ∃ t' g : G, T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' ∧ g * z * g⁻¹ = t' ∧
      (¬ ∃ y : G, y * z * y⁻¹ = t' * z) ∧ a * t' = t' * a := by
  obtain ⟨t', ht'S, ht'2, ⟨g, hg⟩, ht'R, hnf⟩ := T7G2.exists_swap_nonfused hyp
  have h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' := ⟨hyp, ht'S, ht'2, ht'R⟩
  have hz2 : z * z = 1 := h.hz.sq
  have hz1 : z ≠ 1 := h.hz.ne_one
  have hzt' : z ≠ t' := by
    intro heq
    apply h.t'_not_mem_N
    rw [← heq]
    exact h.R_le_N h.hzR.mem
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have ht'inv : t'⁻¹ = t' := h.ht'inv
  have haz : a * z = z * a := hzS a haS
  have ht'z : t' * z = z * t' := hzS t' ht'S
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hV2 : IsPGroup 2 ↥(T7F2.Nsub S R) := S.isPGroup'.to_le inf_le_left
  have haN : a ∈ T7F2.Nsub S R :=
    h.mem_N_of_conj_R' haS (mem_normalizer_iff_conjSub_eq.mp hF'.1)
  obtain ⟨b, hb⟩ : ∃ b : G, b = t' * a * t'⁻¹ := ⟨_, rfl⟩
  have hbN : b ∈ T7F2.Nsub S R := hb ▸ h.N_conj haN
  have hb2 : b * b = 1 := by
    calc b * b = t' * (a * a) * t'⁻¹ := by rw [hb]; group
      _ = 1 := by rw [ha2]; group
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hFb : IsFAut R b := by
    have := T7U.isFAut_conjSub hF' t'
    rwa [h.ht'R', ← hb] at this
  have hFb' : IsFAut R' b := by
    have := T7U.isFAut_conjSub hF t'
    rwa [h.ht'R, ← hb] at this
  have h1 : a * a ∈ Subgroup.zpowers z := by rw [ha2]; exact Subgroup.one_mem _
  have h1' : b * b ∈ Subgroup.zpowers z := by rw [hb2]; exact Subgroup.one_mem _
  obtain ⟨v₁, hv₁R, hv₁v₁, hav₁, hbv₁, w₁, hw₁, hact₁⟩ := prod_isFAut_inner h.hqR h.hzR hV2
    h.R_le_N (fun y hy => (T7F2.mem_Nsub.mp hy).2) haN hbN hF hFb h1 h1'
  obtain ⟨v₂, hv₂R, hv₂v₂, hav₂, hbv₂, w₂, hw₂, hact₂⟩ := prod_isFAut_inner h.hqR' h.hzR' hV2
    h.R'_le_N (fun y hy => h.conj_R'_of_mem_N hy) haN hbN hF' hFb' h1 h1'
  have hw₁R : w₁ ∈ R := by rcases hw₁ with rfl | rfl; exacts [R.one_mem, hv₁R]
  have hw₂R : w₂ ∈ R' := by rcases hw₂ with rfl | rfl; exacts [R'.one_mem, hv₂R]
  have hRS : R ≤ (S : Subgroup G) := h.hRS
  have hR'S : R' ≤ (S : Subgroup G) := h.hR'S
  obtain ⟨e', he'⟩ : ∃ e' : G, e' = (w₁ * w₂)⁻¹ * (a * b) := ⟨_, rfl⟩
  have hee : a * b = (w₁ * w₂) * e' := by rw [he']; group
  have he'S : e' ∈ (S : Subgroup G) := by
    rw [he']
    refine (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem
      ((S : Subgroup G).mul_mem (hRS hw₁R) (hR'S hw₂R))) ?_
    exact (S : Subgroup G).mul_mem haS ((T7F2.mem_Nsub.mp hbN).1)
  have hcR : ∀ r ∈ R, e' * r * e'⁻¹ = r := by
    intro r hr
    have h2 := hact₁ r hr
    have hw₂r : w₂ * r = r * w₂ := (h.hcomm r hr w₂ hw₂R).symm
    calc e' * r * e'⁻¹ = (w₁ * w₂)⁻¹ * ((a * b) * r * (a * b)⁻¹) * (w₁ * w₂) := by
          rw [he']; group
      _ = (w₁ * w₂)⁻¹ * (w₁ * r * w₁⁻¹) * (w₁ * w₂) := by rw [h2]
      _ = w₂⁻¹ * (r * w₂) := by group
      _ = w₂⁻¹ * (w₂ * r) := by rw [hw₂r]
      _ = r := by group
  have hcR' : ∀ r ∈ R', e' * r * e'⁻¹ = r := by
    intro r hr
    have h2 := hact₂ r hr
    have hw₁r : ∀ x ∈ R', w₁ * x = x * w₁ := fun x hx => h.hcomm w₁ hw₁R x hx
    have h3 : w₁⁻¹ * (w₂ * r * w₂⁻¹) * w₁ = w₂ * r * w₂⁻¹ := by
      have hx : w₂ * r * w₂⁻¹ ∈ R' :=
        R'.mul_mem (R'.mul_mem hw₂R hr) (R'.inv_mem hw₂R)
      calc w₁⁻¹ * (w₂ * r * w₂⁻¹) * w₁ = w₁⁻¹ * ((w₂ * r * w₂⁻¹) * w₁) := by group
        _ = w₁⁻¹ * (w₁ * (w₂ * r * w₂⁻¹)) := by rw [hw₁r _ hx]
        _ = w₂ * r * w₂⁻¹ := by group
    calc e' * r * e'⁻¹ = (w₂⁻¹ * w₁⁻¹) * ((a * b) * r * (a * b)⁻¹) * (w₁ * w₂) := by
          rw [he']; group
      _ = (w₂⁻¹ * w₁⁻¹) * (w₂ * r * w₂⁻¹) * (w₁ * w₂) := by rw [h2]
      _ = w₂⁻¹ * (w₁⁻¹ * (w₂ * r * w₂⁻¹) * w₁) * w₂ := by group
      _ = w₂⁻¹ * (w₂ * r * w₂⁻¹) * w₂ := by rw [h3]
      _ = r := by group
  have hcent : e' ∈ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    have hle : R ⊔ R' ≤ Subgroup.centralizer ({e'} : Set G) := by
      refine sup_le (fun r hr => ?_) (fun r hr => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (mul_inv_eq_iff_eq_mul.mp (hcR r hr)).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (mul_inv_eq_iff_eq_mul.mp (hcR' r hr)).symm
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    exact this
  have he'z : e' ∈ Subgroup.zpowers z := by
    have := h11 G Ω K K' W S R R' z t u₁ u₂ hyp
    rw [← this]
    exact Subgroup.mem_inf.mpr ⟨he'S, hcent⟩
  have he'1z : e' = 1 ∨ e' = z := T7G2.eq_one_or_z_of_mem_zpowers h he'z
  have haw₁ : a * w₁ = w₁ * a := by
    rcases hw₁ with rfl | rfl
    · simp
    · calc a * w₁ = (a * w₁ * a⁻¹) * a := by group
        _ = w₁ * a := by rw [hav₁]
  have haw₂ : a * w₂ = w₂ * a := by
    rcases hw₂ with rfl | rfl
    · simp
    · calc a * w₂ = (a * w₂ * a⁻¹) * a := by group
        _ = w₂ * a := by rw [hav₂]
  have hae' : a * e' = e' * a := by
    rcases he'1z with rfl | rfl
    · simp
    · exact haz
  have hacomm : a * (a * b) = (a * b) * a := by
    rw [hee]
    calc a * (w₁ * w₂ * e') = (a * w₁) * w₂ * e' := by group
      _ = w₁ * (a * w₂) * e' := by rw [haw₁]; group
      _ = w₁ * w₂ * (a * e') := by rw [haw₂]; group
      _ = w₁ * w₂ * (e' * a) := by rw [hae']
      _ = w₁ * w₂ * e' * a := by group
  have hee2 : (a * b) * (a * b) = 1 := by
    have h2 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
      calc a * (a * b) * a⁻¹ = (a * a) * b * a⁻¹ := by group
        _ = b * a := by rw [ha2, hai, one_mul]
        _ = (a * b)⁻¹ := by rw [mul_inv_rev, hai, hbi]
    rw [hacomm] at h2
    have h3 : (a * b) * a * a⁻¹ = a * b := by group
    rw [h3] at h2
    exact mul_eq_one_iff_eq_inv.mpr h2
  have hav₁' : a * v₁ = v₁ * a := by
    calc a * v₁ = (a * v₁ * a⁻¹) * a := by group
      _ = v₁ * a := by rw [hav₁]
  have hav₂' : a * v₂ = v₂ * a := by
    calc a * v₂ = (a * v₂ * a⁻¹) * a := by group
      _ = v₂ * a := by rw [hav₂]
  have hz₁ : v₁ * z = z * v₁ := comm_z_of_mem h.hzR hv₁R
  have hz₂ : v₂ * z = z * v₂ := comm_z_of_mem h.hzR' hv₂R
  have hzR : z ∈ R := h.hzR.mem
  have he'R : e' ∈ R := by
    rcases he'1z with h' | h'
    · rw [h']; exact R.one_mem
    · rw [h']; exact hzR
  have he'v₂ : e' * v₂ = v₂ * e' := by
    rcases he'1z with h' | h'
    · rw [h']; simp
    · rw [h']; exact hz₂.symm
  have he'v₁ : e' * v₁ = v₁ * e' := by
    rcases he'1z with h' | h'
    · rw [h']; simp
    · rw [h']; exact hz₁.symm
  have he'e' : e' * e' = 1 := by
    rcases he'1z with h' | h'
    · rw [h']; simp
    · rw [h']; exact hz2
  have hE : (a * b = 1 ∨ a * b = z) ∨
      ∃ v : G, v ∈ R ∧ v * v = z ∧ a * v = v * a ∧ a * b = v * v₂ := by
    rcases hw₁ with hw₁1 | hw₁v <;> rcases hw₂ with hw₂1 | hw₂v
    · left
      rw [hee, hw₁1, hw₂1]
      rcases he'1z with h' | h' <;> simp [h']
    · exfalso
      have h3 : (a * b) * (a * b) = z := by
        rw [hee, hw₁1, hw₂v]
        calc 1 * v₂ * e' * (1 * v₂ * e') = v₂ * (e' * v₂) * e' := by group
          _ = v₂ * (v₂ * e') * e' := by rw [he'v₂]
          _ = (v₂ * v₂) * (e' * e') := by group
          _ = z := by rw [hv₂v₂, he'e', mul_one]
      rw [hee2] at h3
      exact hz1 h3.symm
    · exfalso
      have h3 : (a * b) * (a * b) = z := by
        rw [hee, hw₁v, hw₂1]
        calc v₁ * 1 * e' * (v₁ * 1 * e') = v₁ * (e' * v₁) * e' := by group
          _ = v₁ * (v₁ * e') * e' := by rw [he'v₁]
          _ = (v₁ * v₁) * (e' * e') := by group
          _ = z := by rw [hv₁v₁, he'e', mul_one]
      rw [hee2] at h3
      exact hz1 h3.symm
    · right
      refine ⟨v₁ * e', R.mul_mem hv₁R he'R, ?_, ?_, ?_⟩
      · calc v₁ * e' * (v₁ * e') = v₁ * (e' * v₁) * e' := by group
          _ = v₁ * (v₁ * e') * e' := by rw [he'v₁]
          _ = (v₁ * v₁) * (e' * e') := by group
          _ = z := by rw [hv₁v₁, he'e', mul_one]
      · calc a * (v₁ * e') = (a * v₁) * e' := by group
          _ = (v₁ * a) * e' := by rw [hav₁']
          _ = v₁ * (a * e') := by group
          _ = v₁ * (e' * a) := by rw [hae']
          _ = v₁ * e' * a := by group
      · rw [hee, hw₁v, hw₂v]
        calc v₁ * v₂ * e' = v₁ * (v₂ * e') := by group
          _ = v₁ * (e' * v₂) := by rw [he'v₂]
          _ = v₁ * e' * v₂ := by group
  rcases hE with (h0 | h0) | ⟨v, hvR, hvv, hav, hev⟩
  ·
    refine ⟨t', g, h, hg, hnf, ?_⟩
    have hba : b = a := by
      have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h0
      rw [this, hai]
    rw [hb, ht'inv] at hba
    calc a * t' = (t' * a * t') * t' := by rw [hba]
      _ = t' * a := by rw [mul_assoc, ht'2, mul_one]
  ·
    exfalso
    apply hnf
    refine ⟨a * g, ?_⟩
    have h2 : a * t' * a = z * t' := by
      have h3 : a * (t' * a * t') = z := by rw [hb, ht'inv] at h0; exact h0
      calc a * t' * a = a * (t' * a * t') * t' := by
            calc a * t' * a = a * t' * a * (t' * t') := by rw [ht'2, mul_one]
              _ = a * (t' * a * t') * t' := by group
        _ = z * t' := by rw [h3]
    calc a * g * z * (a * g)⁻¹ = a * (g * z * g⁻¹) * a⁻¹ := by group
      _ = a * t' * a := by rw [hg, hai]
      _ = z * t' := h2
      _ = t' * z := ht'z.symm
  ·
    exfalso
    have hab' : b * a = a * b := by
      have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hee2
      rw [mul_inv_rev, hai, hbi] at h3
      exact h3
    have ht'e : t' * (a * b) = (a * b) * t' := by
      have h3 : t' * b * t'⁻¹ = a := by
        calc t' * b * t'⁻¹ = (t' * t') * a * (t'⁻¹ * t'⁻¹) := by rw [hb]; group
          _ = a := by rw [ht'2, ← mul_inv_rev, ht'2, inv_one, one_mul, mul_one]
      have h4 : t' * (a * b) * t'⁻¹ = a * b := by
        calc t' * (a * b) * t'⁻¹ = (t' * a * t'⁻¹) * (t' * b * t'⁻¹) := by group
          _ = b * a := by rw [← hb, h3]
          _ = a * b := hab'
      calc t' * (a * b) = (t' * (a * b) * t'⁻¹) * t' := by group
        _ = (a * b) * t' := by rw [h4]
    obtain ⟨q, hqdef⟩ : ∃ q : G, q = t' * v * t'⁻¹ := ⟨_, rfl⟩
    obtain ⟨q', hq'def⟩ : ∃ q' : G, q' = t' * v₂ * t'⁻¹ := ⟨_, rfl⟩
    have hqR' : q ∈ R' := by
      have := conj_mem_conjSub (n := t') hvR
      rw [h.ht'R] at this
      rwa [hqdef]
    have hq'R : q' ∈ R := by
      have := conj_mem_conjSub (n := t') hv₂R
      rw [h.ht'R'] at this
      rwa [hq'def]
    have hqq : q * q' = v * v₂ := by
      calc q * q' = t' * (v * v₂) * t'⁻¹ := by rw [hqdef, hq'def]; group
        _ = t' * (a * b) * t'⁻¹ := by rw [hev]
        _ = a * b := by
          calc t' * (a * b) * t'⁻¹ = ((a * b) * t') * t'⁻¹ := by rw [ht'e]
            _ = a * b := by group
        _ = v * v₂ := hev
    have hvq : v * q = q * v := h.hcomm v hvR q hqR'
    have hm : v⁻¹ * q' = q⁻¹ * v₂ := by
      have hvq' : v⁻¹ * q = q * v⁻¹ := by
        calc v⁻¹ * q = v⁻¹ * (q * v) * v⁻¹ := by group
          _ = v⁻¹ * (v * q) * v⁻¹ := by rw [hvq]
          _ = q * v⁻¹ := by group
      calc v⁻¹ * q' = q⁻¹ * (q * v⁻¹) * q' := by group
        _ = q⁻¹ * (v⁻¹ * q) * q' := by rw [hvq']
        _ = q⁻¹ * (v⁻¹ * (q * q')) := by group
        _ = q⁻¹ * (v⁻¹ * (v * v₂)) := by rw [hqq]
        _ = q⁻¹ * v₂ := by group
    have hmR : v⁻¹ * q' ∈ R := R.mul_mem (R.inv_mem hvR) hq'R
    have hmR' : v⁻¹ * q' ∈ R' := by rw [hm]; exact R'.mul_mem (R'.inv_mem hqR') hv₂R
    have hm1z : v⁻¹ * q' = 1 ∨ v⁻¹ * q' = z := by
      apply T7G2.eq_one_or_z_of_mem_zpowers h
      rw [← T7G2.inf_R_R'_eq h]
      exact Subgroup.mem_inf.mpr ⟨hmR, hmR'⟩
    have hqv : q = v₂ ∨ q = v₂ * z := by
      rcases hm1z with h0 | h0
      · left
        rw [h0] at hm
        exact inv_mul_eq_one.mp hm.symm
      · right
        rw [h0] at hm
        have h6 : q⁻¹ = z * v₂⁻¹ := by
          calc q⁻¹ = (q⁻¹ * v₂) * v₂⁻¹ := by group
            _ = z * v₂⁻¹ := by rw [← hm]
        have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
        calc q = (q⁻¹)⁻¹ := (inv_inv q).symm
          _ = (z * v₂⁻¹)⁻¹ := by rw [h6]
          _ = v₂ * z⁻¹ := by rw [mul_inv_rev, inv_inv]
          _ = v₂ * z := by rw [hzi]
    have hkey : a * t' * a = q * t' * v₂ := by
      have h6 : a * t' * a = (v * v₂) * t' := by
        have h7 : a * (t' * a * t'⁻¹) = v * v₂ := by rw [← hb]; exact hev
        calc a * t' * a = a * t' * a * (t'⁻¹ * t') := by group
          _ = (a * (t' * a * t'⁻¹)) * t' := by group
          _ = (v * v₂) * t' := by rw [h7]
      have h8 : q * t' * v₂ = t' * (a * b) := by
        calc q * t' * v₂ = t' * v * t'⁻¹ * t' * v₂ := by rw [hqdef]
          _ = t' * (v * v₂) := by group
          _ = t' * (a * b) := by rw [hev]
      rw [h6, h8, ht'e, hev]
    have hcp := case_pure (a := a) (t' := t') (v := v₂) (z := z) ha2 hz2 ht'z.symm hz₂.symm
      hv₂v₂ hav₂' hqv hkey
    rcases hcp with hfus | ⟨hcen, hyy⟩
    · apply hnf
      refine ⟨(v₂⁻¹ * a) * g, ?_⟩
      calc (v₂⁻¹ * a) * g * z * ((v₂⁻¹ * a) * g)⁻¹
          = (v₂⁻¹ * a) * (g * z * g⁻¹) * (v₂⁻¹ * a)⁻¹ := by group
        _ = (v₂⁻¹ * a) * t' * (v₂⁻¹ * a)⁻¹ := by rw [hg]
        _ = z * t' := hfus.symm
        _ = t' * z := ht'z.symm
    · have hbt : (v₂⁻¹ * a) * t' = t' * (v₂⁻¹ * a) := by
        calc (v₂⁻¹ * a) * t' = ((v₂⁻¹ * a) * t' * (v₂⁻¹ * a)⁻¹) * (v₂⁻¹ * a) := by group
          _ = t' * (v₂⁻¹ * a) := by rw [hcen]
      exact no_sq_eq_z hyp hg hzt' hnf hbt hyy

theorem false_of_zStar_ff (h11 : C25_11 p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R a)
    (hF' : IsFAut R' a) (hZ : z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))) : False := by
  obtain ⟨t', g, h, hg, -, hcomm⟩ := exists_comm_swap_of_ff h11 hyp haS ha2 hF hF'
  exact false_of_comm h hg haS ha2 hF' hZ hcomm

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
