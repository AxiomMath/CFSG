module

public import CFSG.GH74.GLS.Stage4.T2FourInv
public import CFSG.GH74.GLS.Stage4.T2Bad3
public import CFSG.GH74.GLS.Stage4.T2Leaves
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

section Act

variable {G : Type} [Group G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ a : G}

theorem t2S_a_zu (hF : T2Four z u K₁ K₂ H w₁ w₂) (d1 : a⁻¹ * z * a = u)
    (d2 : a⁻¹ * u * a = z * u) : a⁻¹ * (z * u) * a = z := by
  have e : a⁻¹ * (z * u) * a = (a⁻¹ * z * a) * (a⁻¹ * u * a) := by group
  rw [e, d1, d2]
  calc u * (z * u) = (u * z) * u := by group
    _ = (z * u) * u := by rw [← hF.zu_comm]
    _ = z * (u * u) := by group
    _ = z := by rw [hF.uu, mul_one]

theorem t2S_a_conj_z (hF : T2Four z u K₁ K₂ H w₁ w₂) (d1 : a⁻¹ * z * a = u)
    (d2 : a⁻¹ * u * a = z * u) : a * z * a⁻¹ = z * u := by
  calc a * z * a⁻¹ = a * (a⁻¹ * (z * u) * a) * a⁻¹ := by rw [t2S_a_zu hF d1 d2]
    _ = z * u := by group

theorem t2S_a_conj_u (d1 : a⁻¹ * z * a = u) : a * u * a⁻¹ = z := by
  calc a * u * a⁻¹ = a * (a⁻¹ * z * a) * a⁻¹ := by rw [d1]
    _ = z := by group

theorem t2S_cent_U (hF : T2Four z u K₁ K₂ H w₁ w₂) (d1 : a⁻¹ * z * a = u)
    (d2 : a⁻¹ * u * a = z * u) {v : G} (hv : v ∈ t2U z u) (hc : a⁻¹ * v * a = v) : v = 1 := by
  rcases (t2U_mem hF.zz hF.uu hF.zu_comm).1 hv with hv1 | hv1 | hv1 | hv1
  · exact hv1
  · exfalso
    rw [hv1, d1] at hc
    exact hF.zu_ne hc.symm
  · exfalso
    rw [hv1, d2] at hc
    apply hF.z_ne
    have : z * u = 1 * u := by rw [hc, one_mul]
    exact mul_right_cancel this
  · exfalso
    rw [hv1, t2S_a_zu hF d1 d2] at hc
    apply hF.u_ne
    have : z * 1 = z * u := by rw [mul_one]; exact hc
    exact (mul_left_cancel this).symm

theorem t2S_w₁_z_inv (hF : T2Four z u K₁ K₂ H w₁ w₂) : w₁⁻¹ * z * w₁ = z := by
  calc w₁⁻¹ * z * w₁ = w₁⁻¹ * (z * w₁) := by group
    _ = w₁⁻¹ * (w₁ * z) := by rw [hF.w₁_z]
    _ = z := by group

theorem t2S_w₁_u_inv (hF : T2Four z u K₁ K₂ H w₁ w₂) : w₁⁻¹ * u * w₁ = u * z := by
  have h1 : w₁⁻¹ * (u * z) * w₁ = u := by
    calc w₁⁻¹ * (u * z) * w₁ = w₁⁻¹ * (w₁ * u * w₁⁻¹) * w₁ := by rw [hF.w₁_u]
      _ = u := by group
  have h2 : w₁⁻¹ * (u * z) * w₁ = (w₁⁻¹ * u * w₁) * (w₁⁻¹ * z * w₁) := by group
  rw [h2, t2S_w₁_z_inv hF] at h1
  calc w₁⁻¹ * u * w₁ = (w₁⁻¹ * u * w₁ * z) * z⁻¹ := by group
    _ = u * z⁻¹ := by rw [h1]
    _ = u * z := by rw [hF.z_inv]

theorem t2S_cent_a'' (hF : T2Four z u K₁ K₂ H w₁ w₂) (d1 : a⁻¹ * z * a = u)
    (d2 : a⁻¹ * u * a = z * u) :
    ((w₁ * a * w₁⁻¹) * a) * z = z * ((w₁ * a * w₁⁻¹) * a) ∧
      ((w₁ * a * w₁⁻¹) * a) * u = u * ((w₁ * a * w₁⁻¹) * a) := by
  have hz := t2S_a_conj_z hF d1 d2
  have hu := t2S_a_conj_u d1
  have hzu1 : w₁⁻¹ * (z * u) * w₁ = u := by
    calc w₁⁻¹ * (z * u) * w₁ = (w₁⁻¹ * z * w₁) * (w₁⁻¹ * u * w₁) := by group
      _ = z * (u * z) := by rw [t2S_w₁_z_inv hF, t2S_w₁_u_inv hF]
      _ = (z * u) * z := by group
      _ = (u * z) * z := by rw [hF.zu_comm]
      _ = u * (z * z) := by group
      _ = u := by rw [hF.zz, mul_one]
  have hzu2 : w₁ * (z * u) * w₁⁻¹ = u := by
    calc w₁ * (z * u) * w₁⁻¹ = (w₁ * z * w₁⁻¹) * (w₁ * u * w₁⁻¹) := by group
      _ = z * (u * z) := by rw [hF.w₁_z', hF.w₁_u]
      _ = (z * u) * z := by group
      _ = (u * z) * z := by rw [hF.zu_comm]
      _ = u * (z * z) := by group
      _ = u := by rw [hF.zz, mul_one]
  have c1 : ((w₁ * a * w₁⁻¹) * a) * z * ((w₁ * a * w₁⁻¹) * a)⁻¹ = z := by
    calc ((w₁ * a * w₁⁻¹) * a) * z * ((w₁ * a * w₁⁻¹) * a)⁻¹
        = (w₁ * a * w₁⁻¹) * (a * z * a⁻¹) * (w₁ * a * w₁⁻¹)⁻¹ := by group
      _ = (w₁ * a * w₁⁻¹) * (z * u) * (w₁ * a * w₁⁻¹)⁻¹ := by rw [hz]
      _ = w₁ * a * (w₁⁻¹ * (z * u) * w₁) * a⁻¹ * w₁⁻¹ := by group
      _ = w₁ * (a * u * a⁻¹) * w₁⁻¹ := by rw [hzu1]; group
      _ = w₁ * z * w₁⁻¹ := by rw [hu]
      _ = z := hF.w₁_z'
  have c2 : ((w₁ * a * w₁⁻¹) * a) * u * ((w₁ * a * w₁⁻¹) * a)⁻¹ = u := by
    calc ((w₁ * a * w₁⁻¹) * a) * u * ((w₁ * a * w₁⁻¹) * a)⁻¹
        = (w₁ * a * w₁⁻¹) * (a * u * a⁻¹) * (w₁ * a * w₁⁻¹)⁻¹ := by group
      _ = (w₁ * a * w₁⁻¹) * z * (w₁ * a * w₁⁻¹)⁻¹ := by rw [hu]
      _ = w₁ * a * (w₁⁻¹ * z * w₁) * a⁻¹ * w₁⁻¹ := by group
      _ = w₁ * (a * z * a⁻¹) * w₁⁻¹ := by rw [t2S_w₁_z_inv hF]; group
      _ = w₁ * (z * u) * w₁⁻¹ := by rw [hz]
      _ = u := hzu2
  constructor
  · calc ((w₁ * a * w₁⁻¹) * a) * z
        = (((w₁ * a * w₁⁻¹) * a) * z * ((w₁ * a * w₁⁻¹) * a)⁻¹) * ((w₁ * a * w₁⁻¹) * a) := by group
      _ = z * ((w₁ * a * w₁⁻¹) * a) := by rw [c1]
  · calc ((w₁ * a * w₁⁻¹) * a) * u
        = (((w₁ * a * w₁⁻¹) * a) * u * ((w₁ * a * w₁⁻¹) * a)⁻¹) * ((w₁ * a * w₁⁻¹) * a) := by group
      _ = u * ((w₁ * a * w₁⁻¹) * a) := by rw [c2]

end Act

section Q

variable {G : Type} [Group G] {z u : G} {K₁ K₂ H Q₁ Q₂ : Subgroup G} {w₁ w₂ a : G} {k : ℕ}

theorem t2S_aux_cube {A a : G} {Q : Subgroup G} (ha3 : a ^ 3 = 1) (hcube : A ^ 3 = 1)
    (hτ : ∀ q ∈ Q, A * q * A⁻¹ = (a⁻¹ * q * a)⁻¹) (hτQ : ∀ q ∈ Q, A * q * A⁻¹ ∈ Q) :
    ∀ q ∈ Q, q = q⁻¹ := by
  intro q hq
  have e1 := hτ q hq
  have hq1 := hτQ q hq
  have e2 := hτ _ hq1
  have hq2 := hτQ _ hq1
  have e3 := hτ _ hq2
  have hcube' : A * (A * A) = 1 := by rw [← pow_three]; exact hcube
  have hconj3 : A * (A * (A * q * A⁻¹) * A⁻¹) * A⁻¹ = q := by
    calc A * (A * (A * q * A⁻¹) * A⁻¹) * A⁻¹
        = (A * (A * A)) * q * (A * (A * A))⁻¹ := by group
      _ = q := by rw [hcube']; group
  rw [hconj3] at e3
  rw [e2, e1] at e3
  have e4 : (a⁻¹ * (a⁻¹ * (a⁻¹ * q * a)⁻¹ * a)⁻¹ * a)⁻¹ = (a ^ 3)⁻¹ * q⁻¹ * a ^ 3 := by group
  rw [e4, ha3] at e3
  simpa using e3

theorem t2S_w₁_conj (hF : T2Four z u K₁ K₂ H w₁ w₂) (hQ₁H : Q₁ ≤ H ⊓ K₁) (hQ₂H : Q₂ ≤ H ⊓ K₂) :
    ∀ x ∈ Q₁, ∀ y ∈ Q₂, w₁ * (x * y) * w₁⁻¹ = x⁻¹ * y := by
  intro x hx y hy
  have hw₁y : w₁ * y = y * w₁ := hF.K_comm w₁ hF.w₁_mem y (hQ₂H hy).2
  calc w₁ * (x * y) * w₁⁻¹ = (w₁ * x * w₁⁻¹) * (w₁ * y * w₁⁻¹) := by group
    _ = x⁻¹ * y := by
        rw [hF.w₁_inv_H₁ (hQ₁H hx).1 (hQ₁H hx).2, hw₁y]; group

theorem t2S_fixed_split (hF : T2Four z u K₁ K₂ H w₁ w₂) (hQ₁H : Q₁ ≤ H ⊓ K₁) (hQ₂H : Q₂ ≤ H ⊓ K₂)
    (hk : Odd k) (hQ₁e : ∀ x ∈ Q₁, x ^ k = 1) (hQ₂e : ∀ x ∈ Q₂, x ^ k = 1)
    (hdec : ∀ x ∈ H, ∃ c ∈ t2U z u, ∃ b ∈ Q₁ ⊔ Q₂, x = c * b)
    (haN : a ∈ normalizer (H : Set G)) (ha3 : a ^ 3 = 1) (d1 : a⁻¹ * z * a = u)
    (d2 : a⁻¹ * u * a = z * u) :
    ∀ b ∈ Q₁ ⊔ Q₂, a * b * a⁻¹ = b →
      ∃ b₁ ∈ Q₁, ∃ b₂ ∈ Q₂, b = b₁ * b₂ ∧ a * b₁ * a⁻¹ = b₁ ∧ a * b₂ * a⁻¹ = b₂ := by
  intro b hb hab
  have hcommQ : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := fun x hx y hy =>
    hF.K_comm x (hQ₁H hx).2 y (hQ₂H hy).2
  have hQH : Q₁ ⊔ Q₂ ≤ H := sup_le (fun x hx => (hQ₁H hx).1) (fun x hx => (hQ₂H hx).1)
  have hUH : t2U z u ≤ H := t2U_le_of_mem hF.zz hF.uu hF.zu_comm hF.z_mem_H hF.u_mem_H
  have hQe := t2Q_exp hcommQ hQ₁e hQ₂e
  have hnormQ : ∀ g : G, (∀ x ∈ H, g * x * g⁻¹ ∈ H) → ∀ q ∈ Q₁ ⊔ Q₂, g * q * g⁻¹ ∈ Q₁ ⊔ Q₂ :=
    fun g hg => t2Q_normalized hF.zz hF.uu hF.zu_comm hk hF.H_comm hQH hUH hQe hdec hg
  have haH : ∀ x ∈ H, a * x * a⁻¹ ∈ H := fun x hx => (Subgroup.mem_normalizer_iff.1 haN x).1 hx
  have haiN : a⁻¹ ∈ normalizer (H : Set G) := Subgroup.inv_mem _ haN
  have haiQ : ∀ q ∈ Q₁ ⊔ Q₂, a⁻¹ * q * a ∈ Q₁ ⊔ Q₂ := by
    intro q hq
    have := hnormQ a⁻¹ (fun x hx => (Subgroup.mem_normalizer_iff.1 haiN x).1 hx) q hq
    rwa [inv_inv] at this
  have hw₁Q : ∀ q ∈ Q₁ ⊔ Q₂, w₁ * q * w₁⁻¹ ∈ Q₁ ⊔ Q₂ := hnormQ w₁ hF.w₁_normH
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_sup_iff_of_comm hcommQ b).1 hb
  by_cases hQ : ∀ q ∈ Q₁ ⊔ Q₂, q = 1
  · have h1 : b₁ = 1 := hQ b₁ (Subgroup.mem_sup_left hb₁)
    have h2 : b₂ = 1 := hQ b₂ (Subgroup.mem_sup_right hb₂)
    refine ⟨b₁, hb₁, b₂, hb₂, rfl, ?_, ?_⟩
    · rw [h1]; group
    · rw [h2]; group
  push Not at hQ
  obtain ⟨q₀, hq₀, hq₀1⟩ := hQ
  obtain ⟨hc1, hc2⟩ := t2S_cent_a'' (w₁ := w₁) hF d1 d2
  have hY := hF.Y1 ((w₁ * a * w₁⁻¹) * a) (Subgroup.mem_centralizer_singleton_iff.2 hc1) hc2
  have ha''H : (w₁ * a * w₁⁻¹) * a ∈ H := by
    rcases hY with h1 | ⟨x, hx, h1⟩
    · exact h1
    · exfalso
      have ha' : w₁ * a * w₁⁻¹ = x * (w₁ * w₂) * a⁻¹ := eq_mul_inv_of_mul_eq h1
      have hτ : ∀ q ∈ Q₁ ⊔ Q₂, (w₁ * a * w₁⁻¹) * q * (w₁ * a * w₁⁻¹)⁻¹ = (a⁻¹ * q * a)⁻¹ := by
        intro q hq
        rw [ha']
        have hq' := haiQ q hq
        have h0 := hF.w₀_inv (a⁻¹ * q * a) (hQH hq')
        have hx' : x * (a⁻¹ * q * a)⁻¹ = (a⁻¹ * q * a)⁻¹ * x :=
          hF.H_comm x hx _ (H.inv_mem (hQH hq'))
        calc x * (w₁ * w₂) * a⁻¹ * q * (x * (w₁ * w₂) * a⁻¹)⁻¹
            = x * ((w₁ * w₂) * (a⁻¹ * q * a) * (w₁ * w₂)⁻¹) * x⁻¹ := by group
          _ = x * (a⁻¹ * q * a)⁻¹ * x⁻¹ := by rw [h0]
          _ = (a⁻¹ * q * a)⁻¹ := by rw [hx']; group
      have hτQ : ∀ q ∈ Q₁ ⊔ Q₂, (w₁ * a * w₁⁻¹) * q * (w₁ * a * w₁⁻¹)⁻¹ ∈ Q₁ ⊔ Q₂ := by
        intro q hq
        rw [hτ q hq]
        exact Subgroup.inv_mem _ (haiQ q hq)
      have hcube : (w₁ * a * w₁⁻¹) ^ 3 = 1 := by
        rw [conj_pow, ha3]; group
      have key : ∀ q ∈ Q₁ ⊔ Q₂, q = q⁻¹ := t2S_aux_cube ha3 hcube hτ hτQ
      have hq₀2 : q₀ * q₀ = 1 := by
        have := key q₀ hq₀
        calc q₀ * q₀ = q₀ * q₀⁻¹ := by rw [← this]
          _ = 1 := by group
      exact hq₀1 (t2_pow_odd_trivial hk (hQe q₀ hq₀) hq₀2)
  have hAcomm : ∀ q ∈ Q₁ ⊔ Q₂,
      ((w₁ * a * w₁⁻¹) * a) * q * ((w₁ * a * w₁⁻¹) * a)⁻¹ = q := by
    intro q hq
    have := hF.H_comm _ ha''H q (hQH hq)
    calc ((w₁ * a * w₁⁻¹) * a) * q * ((w₁ * a * w₁⁻¹) * a)⁻¹
        = (q * ((w₁ * a * w₁⁻¹) * a)) * ((w₁ * a * w₁⁻¹) * a)⁻¹ := by rw [this]
      _ = q := by group
  have hy : w₁ * (b₁ * b₂) * w₁⁻¹ = b₁⁻¹ * b₂ := t2S_w₁_conj hF hQ₁H hQ₂H b₁ hb₁ b₂ hb₂
  have hyQ : w₁ * (b₁ * b₂) * w₁⁻¹ ∈ Q₁ ⊔ Q₂ := hw₁Q _ hb
  have hyfix : a * (w₁ * (b₁ * b₂) * w₁⁻¹) * a⁻¹ = w₁ * (b₁ * b₂) * w₁⁻¹ := by
    set y := w₁ * (b₁ * b₂) * w₁⁻¹ with hydef
    have hy'' := hAcomm (a⁻¹ * y * a) (haiQ y hyQ)
    have e1 : ((w₁ * a * w₁⁻¹) * a) * (a⁻¹ * y * a) * ((w₁ * a * w₁⁻¹) * a)⁻¹ =
        (w₁ * a * w₁⁻¹) * y * (w₁ * a * w₁⁻¹)⁻¹ := by group
    have e2 : (w₁ * a * w₁⁻¹) * y * (w₁ * a * w₁⁻¹)⁻¹ = y := by
      calc (w₁ * a * w₁⁻¹) * y * (w₁ * a * w₁⁻¹)⁻¹
          = w₁ * (a * (w₁⁻¹ * y * w₁) * a⁻¹) * w₁⁻¹ := by group
        _ = w₁ * (a * (b₁ * b₂) * a⁻¹) * w₁⁻¹ := by rw [hydef]; group
        _ = w₁ * (b₁ * b₂) * w₁⁻¹ := by rw [hab]
    rw [e1, e2] at hy''
    calc a * y * a⁻¹ = a * (a⁻¹ * y * a) * a⁻¹ := by rw [← hy'']
      _ = y := by group
  rw [hy] at hyfix
  have hs₁Q : a * b₁ * a⁻¹ ∈ Q₁ ⊔ Q₂ := by
    have := hnormQ a haH b₁ (Subgroup.mem_sup_left hb₁)
    exact this
  have hs₂Q : a * b₂ * a⁻¹ ∈ Q₁ ⊔ Q₂ := hnormQ a haH b₂ (Subgroup.mem_sup_right hb₂)
  have hab' : (a * b₁ * a⁻¹) * (a * b₂ * a⁻¹) = b₁ * b₂ := by
    rw [← hab]; group
  have hyfix' : (a * b₁ * a⁻¹)⁻¹ * (a * b₂ * a⁻¹) = b₁⁻¹ * b₂ := by
    rw [← hyfix]; group
  have hsq : (a * b₁ * a⁻¹) * (a * b₁ * a⁻¹) = b₁ * b₁ := by
    have h1 : (a * b₁ * a⁻¹) * (a * b₂ * a⁻¹) * ((a * b₁ * a⁻¹)⁻¹ * (a * b₂ * a⁻¹))⁻¹ =
        (a * b₁ * a⁻¹) * (a * b₁ * a⁻¹) := by group
    have h2 : (b₁ * b₂) * (b₁⁻¹ * b₂)⁻¹ = b₁ * b₁ := by group
    rw [← h1, hab', hyfix', h2]
  have hb₁Q : b₁ ∈ Q₁ ⊔ Q₂ := Subgroup.mem_sup_left hb₁
  have hs₁eq : a * b₁ * a⁻¹ = b₁ := by
    set s₁ := a * b₁ * a⁻¹ with hs₁def
    have hc := hF.H_comm s₁ (hQH hs₁Q) b₁⁻¹ (H.inv_mem (hQH hb₁Q))
    have hx : (s₁ * b₁⁻¹) * (s₁ * b₁⁻¹) = 1 := by
      calc (s₁ * b₁⁻¹) * (s₁ * b₁⁻¹) = s₁ * (b₁⁻¹ * s₁) * b₁⁻¹ := by group
        _ = s₁ * (s₁ * b₁⁻¹) * b₁⁻¹ := by rw [← hc]
        _ = (s₁ * s₁) * (b₁⁻¹ * b₁⁻¹) := by group
        _ = (b₁ * b₁) * (b₁⁻¹ * b₁⁻¹) := by rw [hsq]
        _ = 1 := by group
    have hxQ : s₁ * b₁⁻¹ ∈ Q₁ ⊔ Q₂ :=
      Subgroup.mul_mem _ hs₁Q (Subgroup.inv_mem _ hb₁Q)
    have := t2_pow_odd_trivial hk (hQe _ hxQ) hx
    calc s₁ = (s₁ * b₁⁻¹) * b₁ := by group
      _ = b₁ := by rw [this, one_mul]
  refine ⟨b₁, hb₁, b₂, hb₂, rfl, hs₁eq, ?_⟩
  rw [hs₁eq] at hab'
  exact mul_left_cancel hab'

end Q

section Sing

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H Q₁ Q₂ : Subgroup G} {w₁ w₂ a : G}
  {k : ℕ}

theorem t2S_a_normU (d1 : a⁻¹ * z * a = u) (d2 : a⁻¹ * u * a = z * u) :
    a ∈ normalizer (t2U z u : Set G) := by
  have : a⁻¹ ∈ normalizer (t2U z u : Set G) := by
    refine t2U_norm (z := z) (u := u) ?_ ?_
    · rw [inv_inv, d1]
      exact Subgroup.subset_closure (by simp)
    · rw [inv_inv, d2]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  simpa using Subgroup.inv_mem _ this

omit [Finite G] in
theorem t2S_prime_elt {g : G} (hg1 : g ≠ 1) (hgk : g ^ k = 1) (hk : Odd k) :
    ∃ m : ℕ, (orderOf (g ^ m)).Prime ∧ Odd (orderOf (g ^ m)) := by
  have hd : orderOf g ∣ k := orderOf_dvd_of_pow_eq_one hgk
  have hk0 : k ≠ 0 := by rintro rfl; exact absurd hk (by decide)
  have ho0 : orderOf g ≠ 0 := fun h => hk0 (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have ho1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.1 h)
  have hp : (orderOf g).minFac.Prime := Nat.minFac_prime ho1
  have hpd : (orderOf g).minFac ∣ orderOf g := Nat.minFac_dvd _
  refine ⟨orderOf g / (orderOf g).minFac, ?_, ?_⟩
  · rw [orderOf_pow_orderOf_div ho0 hpd]; exact hp
  · rw [orderOf_pow_orderOf_div ho0 hpd]
    exact Odd.of_dvd_nat hk (hpd.trans hd)

theorem t2S_singular_exists (hF : T2Four z u K₁ K₂ H w₁ w₂) (hQ₁H : Q₁ ≤ H ⊓ K₁)
    (hQ₂H : Q₂ ≤ H ⊓ K₂) (hk : Odd k) (hQ₁e : ∀ x ∈ Q₁, x ^ k = 1) (hQ₂e : ∀ x ∈ Q₂, x ^ k = 1)
    (hdec : ∀ x ∈ H, ∃ c ∈ t2U z u, ∃ b ∈ Q₁ ⊔ Q₂, x = c * b)
    (haN : a ∈ normalizer (H : Set G)) (ha3 : a ^ 3 = 1) (d1 : a⁻¹ * z * a = u)
    (d2 : a⁻¹ * u * a = z * u) {x : G} (hx : x ∈ H) (hx1 : x ≠ 1) (hax : a * x * a⁻¹ = x) :
    ∃ y : G, y ∈ H ∧ (y ∈ K₁ ∨ y ∈ K₂) ∧ y ∉ Subgroup.zpowers z ∧ (orderOf y).Prime ∧
      Odd (orderOf y) ∧ a * y * a⁻¹ = y := by
  have hcommQ : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := fun x hx y hy =>
    hF.K_comm x (hQ₁H hx).2 y (hQ₂H hy).2
  have hQH : Q₁ ⊔ Q₂ ≤ H := sup_le (fun x hx => (hQ₁H hx).1) (fun x hx => (hQ₂H hx).1)
  have hUH : t2U z u ≤ H := t2U_le_of_mem hF.zz hF.uu hF.zu_comm hF.z_mem_H hF.u_mem_H
  have hQe := t2Q_exp hcommQ hQ₁e hQ₂e
  have hUQ : t2U z u ⊓ (Q₁ ⊔ Q₂) = ⊥ := t2U_inf_Q_eq_bot hF.zz hF.uu hF.zu_comm hk hQe
  have haH : ∀ x ∈ H, a * x * a⁻¹ ∈ H := fun x hx => (Subgroup.mem_normalizer_iff.1 haN x).1 hx
  have haQ : ∀ q ∈ Q₁ ⊔ Q₂, a * q * a⁻¹ ∈ Q₁ ⊔ Q₂ :=
    fun q hq => t2Q_normalized hF.zz hF.uu hF.zu_comm hk hF.H_comm hQH hUH hQe hdec haH q hq
  have haU := t2S_a_normU d1 d2
  obtain ⟨c, hc, b, hb, rfl⟩ := hdec x hx
  have hcU : a * c * a⁻¹ ∈ t2U z u := (Subgroup.mem_normalizer_iff.1 haU c).1 hc
  have hbQ : a * b * a⁻¹ ∈ Q₁ ⊔ Q₂ := haQ b hb
  have e : (a * c * a⁻¹) * (a * b * a⁻¹) = c * b := by
    calc (a * c * a⁻¹) * (a * b * a⁻¹) = a * (c * b) * a⁻¹ := by group
      _ = c * b := hax
  have e1 : c⁻¹ * (a * c * a⁻¹) = b * (a * b * a⁻¹)⁻¹ := by
    calc c⁻¹ * (a * c * a⁻¹)
        = c⁻¹ * ((a * c * a⁻¹) * (a * b * a⁻¹)) * (a * b * a⁻¹)⁻¹ := by group
      _ = c⁻¹ * (c * b) * (a * b * a⁻¹)⁻¹ := by rw [e]
      _ = b * (a * b * a⁻¹)⁻¹ := by group
  have hmem : c⁻¹ * (a * c * a⁻¹) ∈ t2U z u ⊓ (Q₁ ⊔ Q₂) :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hcU, by
      rw [e1]; exact Subgroup.mul_mem _ hb (Subgroup.inv_mem _ hbQ)⟩
  rw [hUQ] at hmem
  have e2 : c⁻¹ * (a * c * a⁻¹) = 1 := Subgroup.mem_bot.1 hmem
  have hac : a * c * a⁻¹ = c := by
    calc a * c * a⁻¹ = c * (c⁻¹ * (a * c * a⁻¹)) := by group
      _ = c := by rw [e2, mul_one]
  have hab : a * b * a⁻¹ = b := by
    rw [e2] at e1
    have : b * (a * b * a⁻¹)⁻¹ = 1 := e1.symm
    calc a * b * a⁻¹ = (b * (a * b * a⁻¹)⁻¹)⁻¹ * b := by group
      _ = b := by rw [this]; group
  have hc1 : c = 1 := by
    refine t2S_cent_U hF d1 d2 hc ?_
    calc a⁻¹ * c * a = a⁻¹ * (a * c * a⁻¹) * a := by rw [hac]
      _ = c := by group
  have hb1 : b ≠ 1 := by
    intro h1; apply hx1; rw [hc1, h1]; simp
  obtain ⟨b₁, hb₁, b₂, hb₂, hbe, hab₁, hab₂⟩ :=
    t2S_fixed_split hF hQ₁H hQ₂H hk hQ₁e hQ₂e hdec haN ha3 d1 d2 b hb hab
  have hone : (b₁ ≠ 1) ∨ (b₂ ≠ 1) := by
    by_contra hcon
    push Not at hcon
    apply hb1
    rw [hbe, hcon.1, hcon.2]; simp
  have hfinish : ∀ (g : G) (Qi Ki : Subgroup G), Qi ≤ H ⊓ Ki → (∀ x ∈ Qi, x ^ k = 1) → g ∈ Qi →
      g ≠ 1 → a * g * a⁻¹ = g → (Ki = K₁ ∨ Ki = K₂) →
      ∃ y : G, y ∈ H ∧ (y ∈ K₁ ∨ y ∈ K₂) ∧ y ∉ Subgroup.zpowers z ∧ (orderOf y).Prime ∧
        Odd (orderOf y) ∧ a * y * a⁻¹ = y := by
    intro g Qi Ki hQi hQie hg hg1 hgfix hKi
    obtain ⟨m, hmp, hmodd⟩ := t2S_prime_elt hg1 (hQie g hg) hk
    refine ⟨g ^ m, (hQi (Subgroup.pow_mem _ hg m)).1, ?_, ?_, hmp, hmodd, ?_⟩
    · rcases hKi with rfl | rfl
      · exact Or.inl (hQi (Subgroup.pow_mem _ hg m)).2
      · exact Or.inr (hQi (Subgroup.pow_mem _ hg m)).2
    · intro hmem
      rcases t2C_zpowers_cases hF.zz hmem with h1 | h1
      · rw [h1, orderOf_one] at hmp; exact Nat.not_prime_one hmp
      · have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hF.zz) hF.z_ne
        rw [h1, hzo] at hmodd
        exact absurd hmodd (by decide)
    · calc a * g ^ m * a⁻¹ = (a * g * a⁻¹) ^ m := conj_pow.symm
        _ = g ^ m := by rw [hgfix]
  rcases hone with h1 | h1
  · exact hfinish b₁ Q₁ K₁ hQ₁H hQ₁e hb₁ h1 hab₁ (Or.inl rfl)
  · exact hfinish b₂ Q₂ K₂ hQ₂H hQ₂e hb₂ h1 hab₂ (Or.inr rfl)

end Sing

section Cyc

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}

omit [Finite G] in
theorem t2S_no_cent (hF : T2Four z u K₁ K₂ H w₁ w₂) (hH3 : ¬ 3 ∣ Nat.card ↥H) {g : G}
    (hg3 : orderOf g = 3) (hgz : g * z = z * g) (hgu : g * u = u * g) : False := by
  rcases hF.Y1 g (Subgroup.mem_centralizer_singleton_iff.2 hgz) hgu with hgH | ⟨x, hx, hgx⟩
  · apply hH3
    have := Subgroup.orderOf_dvd_natCard H hgH
    rwa [hg3] at this
  · have h2 : g * g = 1 := by rw [hgx]; exact hF.Hw_sq hx
    have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hg3] at this
    omega

theorem t2S_cycling (hF : T2Four z u K₁ K₂ H w₁ w₂) (hr : CFSG.pRank 2 G = 3)
    (hH3 : ¬ 3 ∣ Nat.card ↥H) {a : G} (haN : a ∈ normalizer (H : Set G)) (ha3 : orderOf a = 3) :
    ∃ b : G, (b = a ∨ b = a⁻¹) ∧ b ^ 3 = 1 ∧ b⁻¹ * z * b = u ∧ b⁻¹ * u * b = z * u := by
  have haH : ∀ x ∈ H, a * x * a⁻¹ ∈ H := fun x hx => (Subgroup.mem_normalizer_iff.1 haN x).1 hx
  have ha3' : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
  have ha3'' : a * (a * a) = 1 := by rw [← pow_three]; exact ha3'
  have hcyc3 : ∀ x : G, a * (a * (a * x * a⁻¹) * a⁻¹) * a⁻¹ = x := by
    intro x
    calc a * (a * (a * x * a⁻¹) * a⁻¹) * a⁻¹ = (a * (a * a)) * x * (a * (a * a))⁻¹ := by group
      _ = x := by rw [ha3'']; group
  have hinv : ∀ x : G, x * x = 1 → (a * x * a⁻¹) * (a * x * a⁻¹) = 1 := by
    intro x hx
    calc (a * x * a⁻¹) * (a * x * a⁻¹) = a * (x * x) * a⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have hcz : a * z * a⁻¹ ∈ t2U z u :=
    (t2U_mem hF.zz hF.uu hF.zu_comm).2 (hF.omega1 hr _ (haH z hF.z_mem_H) (hinv z hF.zz))
  have hcu : a * u * a⁻¹ ∈ t2U z u :=
    (t2U_mem hF.zz hF.uu hF.zu_comm).2 (hF.omega1 hr _ (haH u hF.u_mem_H) (hinv u hF.uu))
  have hz1 : a * z * a⁻¹ ≠ 1 := by
    intro h; apply hF.z_ne
    calc z = a⁻¹ * (a * z * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group
  have hu1 : a * u * a⁻¹ ≠ 1 := by
    intro h; apply hF.u_ne
    calc u = a⁻¹ * (a * u * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group
  have hne : a * z * a⁻¹ ≠ a * u * a⁻¹ := by
    intro h; apply hF.zu_ne
    have := mul_right_cancel (mul_left_cancel (a := a) (show a * (z * a⁻¹) = a * (u * a⁻¹) by
      simpa [mul_assoc] using h))
    exact this
  have hzuc : a * (z * u) * a⁻¹ = (a * z * a⁻¹) * (a * u * a⁻¹) := by group
  have hzz : z * z = 1 := hF.zz
  have huu : u * u = 1 := hF.uu
  have hzu : z * u = u * z := hF.zu_comm
  have hz_zu : z * (z * u) = u := by rw [← mul_assoc, hzz, one_mul]
  have hu_zu : u * (z * u) = z := by
    calc u * (z * u) = (u * z) * u := by group
      _ = (z * u) * u := by rw [← hzu]
      _ = z * (u * u) := by group
      _ = z := by rw [huu, mul_one]
  have hzu_z : (z * u) * z = u := by
    calc (z * u) * z = (u * z) * z := by rw [hzu]
      _ = u * (z * z) := by group
      _ = u := by rw [hzz, mul_one]
  have hzu_u : (z * u) * u = z := by
    calc (z * u) * u = z * (u * u) := by group
      _ = z := by rw [huu, mul_one]
  rcases (t2U_mem hzz huu hzu).1 hcz with h1 | h1 | h1 | h1 <;>
    rcases (t2U_mem hzz huu hzu).1 hcu with h2 | h2 | h2 | h2
  · exact absurd h1 hz1
  · exact absurd h1 hz1
  · exact absurd h1 hz1
  · exact absurd h1 hz1
  · exact absurd h2 hu1
  ·
    exact absurd (h1.trans h2.symm) hne
  ·
    exfalso
    refine t2S_no_cent hF hH3 ha3 ?_ ?_
    · calc a * z = (a * z * a⁻¹) * a := by group
        _ = z * a := by rw [h1]
    · calc a * u = (a * u * a⁻¹) * a := by group
        _ = u * a := by rw [h2]
  ·
    exfalso
    have e1 : a * (z * u) * a⁻¹ = u := by rw [hzuc, h1, h2, hz_zu]
    have := hcyc3 u
    rw [h2, e1, h2] at this
    exact hF.z_ne (by simpa using mul_right_cancel (this.trans (one_mul u).symm))
  · exact absurd h2 hu1
  ·
    exfalso
    have e1 : a * (z * u) * a⁻¹ = z * u := by rw [hzuc, h1, h2, hzu]
    have := hcyc3 z
    rw [h1, h2, h1] at this
    exact hF.zu_ne this.symm
  · exact absurd (h1.trans h2.symm) hne
  ·
    refine ⟨a⁻¹, Or.inr rfl, ?_, ?_, ?_⟩
    · rw [inv_pow, ha3', inv_one]
    · rw [inv_inv]; exact h1
    · rw [inv_inv]; exact h2
  · exact absurd h2 hu1
  ·
    refine ⟨a, Or.inl rfl, ha3', ?_, ?_⟩
    · calc a⁻¹ * z * a = a⁻¹ * (a * u * a⁻¹) * a := by rw [h2]
        _ = u := by group
    · have e1 : a * (z * u) * a⁻¹ = u := by rw [hzuc, h1, h2, hzu_z]
      calc a⁻¹ * u * a = a⁻¹ * (a * (z * u) * a⁻¹) * a := by rw [e1]
        _ = z * u := by group
  ·
    exfalso
    have e1 : a * (z * u) * a⁻¹ = z := by rw [hzuc, h1, h2, hzu_u]
    have := hcyc3 z
    rw [h1, e1, h1] at this
    exact hF.u_ne (mul_left_cancel (this.trans (mul_one z).symm))
  · exact absurd (h1.trans h2.symm) hne

end Cyc

section Val

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z : G} {K₁ K₂ : Subgroup G}
  {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2S_val3 {n : ℕ} (hn : n ≠ 0) (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂)
    (hidx : (K₁ ⊔ K₂).relIndex (centralizer ({z} : Set G)) = 2) (hBad : Ch6Bad3 G) :
    (Nat.card G).factorization 3 = 2 * n := by
  have := hSet.finite₁
  have := hSet.finite₂
  rw [t2_card3 hSet hBad]
  have hC : 2 * Nat.card ↥(K₁ ⊔ K₂) = Nat.card ↥(centralizer ({z} : Set G)) := by
    have h := Subgroup.relIndex_mul_card (H := K₁ ⊔ K₂) (K := centralizer ({z} : Set G))
    rwa [inf_of_le_left hSet.le_centralizer, hidx] at h
  have hK : Nat.card ↥(K₁ ⊔ K₂) * 2 = Nat.card ↥K₁ * Nat.card ↥K₂ := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K₁ K₂ hSet.comm).1
    rwa [hSet.inter_card] at h
  have hK₁ : Nat.card ↥K₁ = 3 ^ n * ((3 ^ n) ^ 2 - 1) := by
    obtain ⟨e⟩ := hSet.iso₁
    rw [Nat.card_congr e.toEquiv, t2C_card_sl2, hSet.card₁]
  have hK₂ : Nat.card ↥K₂ = 3 ^ n * ((3 ^ n) ^ 2 - 1) := by
    obtain ⟨e⟩ := hSet.iso₂
    rw [Nat.card_congr e.toEquiv, t2C_card_sl2, hSet.card₂]
  have hCsq : Nat.card ↥(centralizer ({z} : Set G)) = (3 ^ n * ((3 ^ n) ^ 2 - 1)) ^ 2 := by
    calc Nat.card ↥(centralizer ({z} : Set G)) = Nat.card ↥(K₁ ⊔ K₂) * 2 := by rw [← hC, mul_comm]
      _ = Nat.card ↥K₁ * Nat.card ↥K₂ := hK
      _ = (3 ^ n * ((3 ^ n) ^ 2 - 1)) * (3 ^ n * ((3 ^ n) ^ 2 - 1)) := by rw [hK₁, hK₂]
      _ = (3 ^ n * ((3 ^ n) ^ 2 - 1)) ^ 2 := (sq _).symm
  have h3n : 3 ∣ 3 ^ n := dvd_pow_self 3 hn
  have h2n : 2 ≤ 3 ^ n := by
    have := Nat.le_of_dvd (by positivity) h3n
    have h0 : 0 < 3 ^ n := by positivity
    omega
  have hm : (3 ^ n) ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ (3 ^ n) ^ 2 := by nlinarith
    omega
  have hnd : ¬ 3 ∣ (3 ^ n) ^ 2 - 1 := by
    have h3 : 3 ∣ (3 ^ n) ^ 2 := dvd_pow h3n (by norm_num)
    have h1 : 1 ≤ (3 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    generalize (3 ^ n) ^ 2 = X at h3 h1 ⊢
    omega
  rw [hCsq, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.factorization_mul (by positivity) hm, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, Nat.Prime.factorization_pow Nat.prime_three]
  simp

end Val

section Final

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t : G} {K₁ K₂ H Q₁ Q₂ : Subgroup G}
  {w₁ w₂ a : G} {k : ℕ} {F₁ F₂ : Type} [Field F₁] [Field F₂]

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank in
theorem t2S_cent_trivial {n : ℕ} (hOrd : Ch6P56bOrder) (hStd : Std G) (hr : pRank 2 G = 3)
    (hn : 2 ≤ n) (hAt : IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n)) (hBad : Ch6Bad3 G)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hF : T2Four z t K₁ K₂ H w₁ w₂) (hQ₁H : Q₁ ≤ H ⊓ K₁) (hQ₂H : Q₂ ≤ H ⊓ K₂) (hk : Odd k)
    (hQ₁e : ∀ x ∈ Q₁, x ^ k = 1) (hQ₂e : ∀ x ∈ Q₂, x ^ k = 1)
    (hdec : ∀ x ∈ H, ∃ c ∈ t2U z t, ∃ b ∈ Q₁ ⊔ Q₂, x = c * b)
    (haN : a ∈ normalizer (H : Set G)) (ha3 : a ^ 3 = 1) (d1 : a⁻¹ * z * a = t)
    (d2 : a⁻¹ * t * a = z * t) : ∀ x ∈ H, a * x * a⁻¹ = x → x = 1 := by
  intro x hx hax
  by_contra hx1
  obtain ⟨y, hyH, hyK, hyz, hyp, hyodd, hay⟩ :=
    t2S_singular_exists hF hQ₁H hQ₂H hk hQ₁e hQ₂e hdec haN ha3 d1 d2 hx hx1 hax
  have h3 := hOrd G hStd hr Gs n hn hAt z t K₁ K₂ F₁ F₂ hSet hRem H w₁ w₂ hF a haN ha3 d1 d2 y hyH
    hyK hyz hyp hyodd hay
  have h3' : 3 ^ (3 * n) ∣ Nat.card G := h3.trans (Subgroup.card_subgroup_dvd_card _)
  have hv := t2S_val3 (by omega) hSet hF.C_idx hBad
  have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).1 h3'
  omega

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank in
theorem t2S_tns_of_order {n : ℕ} (hOrd : Ch6P56bOrder) (hStd : Std G) (hr : pRank 2 G = 3)
    (hn : 2 ≤ n) (hAt : IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n)) (hBad : Ch6Bad3 G)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hF : T2Four z t K₁ K₂ H w₁ w₂) (hQ₁H : Q₁ ≤ H ⊓ K₁) (hQ₂H : Q₂ ≤ H ⊓ K₂) (hk : Odd k)
    (hQ₁e : ∀ x ∈ Q₁, x ^ k = 1) (hQ₂e : ∀ x ∈ Q₂, x ^ k = 1)
    (hdec : ∀ x ∈ H, ∃ c ∈ t2U z t, ∃ b ∈ Q₁ ⊔ Q₂, x = c * b) (hH3 : ¬ 3 ∣ Nat.card ↥H)
    (haN : a ∈ normalizer (H : Set G)) (ha3 : orderOf a = 3) :
    ∀ x ∈ H, x ≠ 1 → a * x * a⁻¹ ≠ x := by
  intro x hx hx1 hax
  obtain ⟨b, hb, hb3, d1, d2⟩ := t2S_cycling hF hr hH3 haN ha3
  have hbN : b ∈ normalizer (H : Set G) := by
    rcases hb with hb | hb
    · rw [hb]; exact haN
    · rw [hb]; exact Subgroup.inv_mem _ haN
  have hbx : b * x * b⁻¹ = x := by
    rcases hb with hb | hb
    · rw [hb]; exact hax
    · rw [hb]
      calc a⁻¹ * x * a⁻¹⁻¹ = a⁻¹ * (a * x * a⁻¹) * a := by rw [hax, inv_inv]
        _ = x := by group
  exact hx1 (t2S_cent_trivial hOrd hStd hr hn hAt hBad hSet hRem hF hQ₁H hQ₂H hk hQ₁e hQ₂e hdec hbN
    hb3 d1 d2 x hx hbx)

end Final

section Data

variable {G : Type} [Group G]

@[expose] def T2TnsData (z t : G) (K₁ K₂ : Subgroup G) : Prop :=
  ∀ (H : Subgroup G) (w₁ w₂ : G), T2Four z t K₁ K₂ H w₁ w₂ → ∀ (Q₁ Q₂ : Subgroup G) (k : ℕ),
    Odd k → Q₁ ≤ H ⊓ K₁ → Q₂ ≤ H ⊓ K₂ → (∀ x ∈ Q₁, x ^ k = 1) → (∀ x ∈ Q₂, x ^ k = 1) →
    (∀ x ∈ H, ∃ c ∈ t2U z t, ∃ b ∈ Q₁ ⊔ Q₂, x = c * b) → ¬ 3 ∣ Nat.card ↥H →
      ∀ a : G, a ∈ normalizer (H : Set G) → orderOf a = 3 → ∀ x ∈ H, x ≠ 1 → a * x * a⁻¹ ≠ x

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank in
theorem T2TnsData.of_order [Finite G] {Gs : Type} [Group Gs] {z t : G} {K₁ K₂ : Subgroup G}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] {n : ℕ} (hOrd : Ch6P56bOrder) (hStd : Std G)
    (hr : pRank 2 G = 3) (hn : 2 ≤ n) (hAt : IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n))
    (hBad : Ch6Bad3 G) (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂)
    (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) : T2TnsData z t K₁ K₂ :=
  fun _ _ _ hT _ _ _ hk hQ₁H hQ₂H hQ₁e hQ₂e hdec hH3 _ haN ha3 =>
    t2S_tns_of_order hOrd hStd hr hn hAt hBad hSet hRem hT hQ₁H hQ₂H hk hQ₁e hQ₂e hdec hH3 haN ha3

end Data

end CFSG.GH74.GLS.Stage4.Rest
