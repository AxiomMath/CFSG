module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem s7fActs_mul {φ : (Fin 5 → ZMod 2) → G} {h₁ h₂ : G} {σ₁ σ₂ : Equiv.Perm (Fin 5)}
    (h1 : s7fActs φ h₁ σ₁) (h2 : s7fActs φ h₂ σ₂) : s7fActs φ (h₁ * h₂) (σ₁ * σ₂) := by
  intro v hv
  have hv' : IsEvenVec (permVec σ₂ v) := isEvenVec_permVec σ₂ hv
  calc h₁ * h₂ * φ v * (h₁ * h₂)⁻¹ = h₁ * (h₂ * φ v * h₂⁻¹) * h₁⁻¹ := by group
    _ = h₁ * φ (permVec σ₂ v) * h₁⁻¹ := by rw [h2 v hv]
    _ = φ (permVec σ₁ (permVec σ₂ v)) := h1 _ hv'
    _ = φ (permVec (σ₁ * σ₂) v) := rfl

theorem s7fActs_inv {φ : (Fin 5 → ZMod 2) → G} {h : G} {σ : Equiv.Perm (Fin 5)}
    (hh : s7fActs φ h σ) : s7fActs φ h⁻¹ σ⁻¹ := by
  intro v hv
  have hv' : IsEvenVec (permVec σ⁻¹ v) := isEvenVec_permVec σ⁻¹ hv
  have h1 := hh (permVec σ⁻¹ v) hv'
  have h2 : permVec σ (permVec σ⁻¹ v) = v := by
    show permVec (σ * σ⁻¹) v = v
    rw [mul_inv_cancel]
    rfl
  rw [h2] at h1
  rw [← h1]
  group

theorem s7fActs_one (φ : (Fin 5 → ZMod 2) → G) : s7fActs φ 1 1 := by
  intro v _
  show 1 * φ v * 1⁻¹ = φ v
  group

theorem s7f_comm_mod {B E : Subgroup G} (hcomm : ∀ e ∈ E, ∀ b ∈ B, e * b = b * e)
    (hsq : ∀ e ∈ E, e * e ∈ B) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    (x * y)⁻¹ * (y * x) ∈ B := by
  have hxy : x * y ∈ E := E.mul_mem hx hy
  have hyx : y * x ∈ E := E.mul_mem hy hx
  have hc : (x * y) * (x * y) ∈ B := hsq _ hxy
  have hyy : y * y ∈ B := hsq y hy
  have hxx : x * x ∈ B := hsq x hx
  have h1 : y * x * ((x * y) * (x * y))⁻¹ = ((x * y) * (x * y))⁻¹ * (y * x) :=
    hcomm _ hyx _ (B.inv_mem hc)
  have h2 : x * (y * y) = (y * y) * x := hcomm x hx _ hyy
  have key : (x * y)⁻¹ * (y * x) = (y * y) * (x * x) * ((x * y) * (x * y))⁻¹ := by
    calc (x * y)⁻¹ * (y * x) = (x * y) * (((x * y) * (x * y))⁻¹ * (y * x)) := by group
      _ = (x * y) * (y * x * ((x * y) * (x * y))⁻¹) := by rw [h1]
      _ = (x * (y * y)) * x * ((x * y) * (x * y))⁻¹ := by group
      _ = ((y * y) * x) * x * ((x * y) * (x * y))⁻¹ := by rw [h2]
      _ = (y * y) * (x * x) * ((x * y) * (x * y))⁻¹ := by group
  rw [key]
  exact B.mul_mem (B.mul_mem hyy hxx) (B.inv_mem hc)

namespace S7FFrame

variable {t : G} {B E H : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}

theorem t_inv (F : S7FFrame t B E H φ) : t⁻¹ = t := by
  exact inv_eq_of_mul_eq_one_right F.t_sq

theorem t_comm (F : S7FFrame t B E H φ) {b : G} (hb : b ∈ B) : t * b = b * t := by
  exact F.comm_B t F.t_mem b hb

theorem mem_B_iff (F : S7FFrame t B E H φ) {x : G} : x ∈ B ↔ ∃ v, IsEvenVec v ∧ φ v = x := by
  exact F.perm.2.2.1 x

theorem acts (F : S7FFrame t B E H φ) {h : G} (hh : h ∈ H) :
    ∃ σ : Equiv.Perm (Fin 5), s7fActs φ h σ := by
  obtain ⟨σ, -, hσ⟩ := F.perm.2.2.2.1 h hh
  exact ⟨σ, hσ⟩

theorem realize (F : S7FFrame t B E H φ) (σ : Equiv.Perm (Fin 5)) :
    ∃ h ∈ H, s7fActs φ h σ := by
  obtain ⟨h, hh, hσ⟩ := F.perm.2.2.2.2 σ (Subgroup.mem_top σ)
  exact ⟨h, hh, hσ⟩

theorem H_B (F : S7FFrame t B E H φ) {h b : G} (hh : h ∈ H) (hb : b ∈ B) : h * b * h⁻¹ ∈ B := by
  obtain ⟨v, hv, rfl⟩ := F.mem_B_iff.mp hb
  obtain ⟨σ, hσ⟩ := F.acts hh
  rw [hσ v hv]
  exact F.mem_B_iff.mpr ⟨_, isEvenVec_permVec σ hv, rfl⟩

theorem comm_of_acts_one (F : S7FFrame t B E H φ) {h : G} (h1 : s7fActs φ h 1) :
    ∀ b ∈ B, h * b = b * h := by
  intro b hb
  obtain ⟨v, hv, rfl⟩ := F.mem_B_iff.mp hb
  have h2 : h * φ v * h⁻¹ = φ v := h1 v hv
  calc h * φ v = h * φ v * h⁻¹ * h := by group
    _ = φ v * h := by rw [h2]

theorem triv_of_acts_one (F : S7FFrame t B E H φ) {h : G} (hh : h ∈ H) (h1 : s7fActs φ h 1) :
    ∀ e ∈ E, e⁻¹ * (h * e * h⁻¹) ∈ B := by
  exact F.triv h hh (F.comm_of_acts_one h1)

theorem comm_mod (F : S7FFrame t B E H φ) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    (x * y)⁻¹ * (y * x) ∈ B :=
  s7f_comm_mod F.comm_B F.sq_mem hx hy

theorem conj_mem_of_B_le (F : S7FFrame t B E H φ) {U : Subgroup G} (hUE : U ≤ E) (hBU : B ≤ U)
    {e u : G} (he : e ∈ E) (hu : u ∈ U) : e * u * e⁻¹ ∈ U := by
  have hu' : u ∈ E := hUE hu
  have h := F.comm_mod (E.inv_mem he) hu'
  have heq : e * u * e⁻¹ = u * ((e⁻¹ * u)⁻¹ * (u * e⁻¹)) := by group
  rw [heq]
  exact U.mul_mem hu (hBU h)

theorem kap_mul (F : S7FFrame t B E H φ) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    s7fKap t (x * y) = s7fKap t x * s7fKap t y := by
  have hky : s7fKap t y ∈ B := F.kap_mem y hy
  have hkx : s7fKap t x ∈ B := F.kap_mem x hx
  have h1 : x * s7fKap t y = s7fKap t y * x := F.comm_B x hx _ hky
  have h2 : s7fKap t x * s7fKap t y = s7fKap t y * s7fKap t x :=
    F.comm_B _ (F.B_le hkx) _ hky
  calc s7fKap t (x * y) = x * s7fKap t y * (t * x⁻¹ * t⁻¹) := by unfold s7fKap; group
    _ = s7fKap t y * x * (t * x⁻¹ * t⁻¹) := by rw [h1]
    _ = s7fKap t y * s7fKap t x := by unfold s7fKap; group
    _ = s7fKap t x * s7fKap t y := h2.symm

theorem kap_inv (F : S7FFrame t B E H φ) {x : G} (hx : x ∈ E) :
    s7fKap t x⁻¹ = (s7fKap t x)⁻¹ := by
  have h := F.kap_mul hx (E.inv_mem hx)
  rw [mul_inv_cancel] at h
  have h1 : s7fKap t (1 : G) = 1 := by unfold s7fKap; group
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem kap_B (F : S7FFrame t B E H φ) {b : G} (hb : b ∈ B) : s7fKap t b = 1 := by
  have h := F.t_comm hb
  unfold s7fKap
  calc b * t * b⁻¹ * t⁻¹ = (b * t) * b⁻¹ * t⁻¹ := rfl
    _ = (t * b) * b⁻¹ * t⁻¹ := by rw [h]
    _ = 1 := by group

theorem kap_conj (F : S7FFrame t B E H φ) {h x : G} (hh : h ∈ H) (hx : x ∈ E) :
    s7fKap t (h * x * h⁻¹) = h * s7fKap t x * h⁻¹ := by
  set c := t⁻¹ * (h * t * h⁻¹) with hc
  have hcB : c ∈ B := F.H_t h hh
  have hx' : h * x * h⁻¹ ∈ E := F.H_E h hh x hx
  have hcomm : (h * x * h⁻¹)⁻¹ * c = c * (h * x * h⁻¹)⁻¹ :=
    F.comm_B _ (E.inv_mem hx') c hcB
  have hht : h * t * h⁻¹ = t * c := by rw [hc]; group
  calc s7fKap t (h * x * h⁻¹)
      = (h * x * h⁻¹) * t * ((h * x * h⁻¹)⁻¹ * c) * c⁻¹ * t⁻¹ := by unfold s7fKap; group
    _ = (h * x * h⁻¹) * t * (c * (h * x * h⁻¹)⁻¹) * c⁻¹ * t⁻¹ := by rw [hcomm]
    _ = (h * x * h⁻¹) * (t * c) * (h * x * h⁻¹)⁻¹ * (t * c)⁻¹ := by group
    _ = (h * x * h⁻¹) * (h * t * h⁻¹) * (h * x * h⁻¹)⁻¹ * (h * t * h⁻¹)⁻¹ := by rw [hht]
    _ = h * s7fKap t x * h⁻¹ := by unfold s7fKap; group

end S7FFrame

end CFSG.OddStandard.SmallF3.Omega
