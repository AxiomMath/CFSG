module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16E
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem c16_comm_mul_of_abelian {A : Subgroup G} {t : G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAt : ∀ f ∈ A, ⁅f, t⁆ ∈ A) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) : ⁅a * b, t⁆ = ⁅a, t⁆ * ⁅b, t⁆ := by
  have hbA : ⁅b, t⁆ ∈ A := hAt b hb
  have haA : ⁅a, t⁆ ∈ A := hAt a ha
  have hconj : a * ⁅b, t⁆ * a⁻¹ = ⁅b, t⁆ := by
    rw [hA a ha (⁅b, t⁆) hbA]
    group
  rw [commutatorElement_mul_left_eq_conj_mul, hconj]
  exact (hA (⁅a, t⁆) haA (⁅b, t⁆) hbA).symm

structure C16Ab (K Y Q : Subgroup G) (t rho z u fz fu : G) : Prop where
  kb : C16KBasis K z u
  K_le_Y : K ≤ Y
  Y_comm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a
  fz_mem : fz ∈ Y
  fu_mem : fu ∈ Y
  K_comm_t : ∀ k ∈ K, k * t = t * k
  comm_t : ∀ f ∈ Y, ⁅f, t⁆ ∈ K
  ker_t : ∀ f ∈ Y, ⁅f, t⁆ = 1 → f ∈ K
  fz_t : ⁅fz, t⁆ = z
  fu_t : ⁅fu, t⁆ = u
  fu_def : fu = rho * fz * rho⁻¹
  rho_z : rho * z * rho⁻¹ = u
  rho_u : rho * u * rho⁻¹ = z * u
  rho_cube : rho ^ 3 = 1
  rho_t : rho * t = t * rho
  rho_Y : ∀ f ∈ Y, rho * f * rho⁻¹ ∈ Y
  Q_comm_Y : ∀ q ∈ Q, ∀ f ∈ Y, ⁅q, f⁆ ∈ K
  Q_cent_K : ∀ q ∈ Q, ∀ k ∈ K, q * k = k * q
  rho_Q : ∀ q ∈ Q, rho * q * rho⁻¹ ∈ Q

variable {K Y Q : Subgroup G} {t rho z u fz fu : G}

private theorem c16_inv_conj_self {x c : G} (h : x * c = c * x) : x⁻¹ * c * x = c := by
  rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem c16_inv_comm {x c : G} (h : x * c = c * x) : x⁻¹ * c = c * x⁻¹ := by
  have h' : x⁻¹ * c * x = c := c16_inv_conj_self h
  calc x⁻¹ * c = x⁻¹ * c * x * x⁻¹ := by group
    _ = c * x⁻¹ := by rw [h']

private theorem c16_conj_comm (x y c : G) (h : x * c = c * x) :
    ⁅x * y * x⁻¹, c⁆ = x * ⁅y, c⁆ * x⁻¹ := by
  have h' : x⁻¹ * c * x = c := c16_inv_conj_self h
  have key : ⁅x * y * x⁻¹, c⁆ = x * ⁅y, x⁻¹ * c * x⁆ * x⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [key, h']

private theorem c16_rho_inv_mem (H : C16Ab K Y Q t rho z u fz fu) {f : G} (hf : f ∈ Y) :
    rho⁻¹ * f * rho ∈ Y := by
  have hsq : (rho * rho) * rho = 1 := by
    calc (rho * rho) * rho = rho ^ 3 := by rw [pow_succ, pow_two]
      _ = 1 := H.rho_cube
  have h1 : rho⁻¹ = rho * rho := (eq_inv_of_mul_eq_one_left hsq).symm
  have h2 : rho = (rho * rho)⁻¹ := eq_inv_of_mul_eq_one_right hsq
  have heq : rho⁻¹ * f * rho = (rho * rho) * f * (rho * rho)⁻¹ := by
    rw [h1, ← h2]
  have heq2 : (rho * rho) * f * (rho * rho)⁻¹ = rho * (rho * f * rho⁻¹) * rho⁻¹ := by
    group
  rw [heq, heq2]
  exact H.rho_Y (rho * f * rho⁻¹) (H.rho_Y f hf)

theorem c16_N_mul (H : C16Ab K Y Q t rho z u fz fu) {a b : G} (ha : a ∈ Y) (hb : b ∈ Y) :
    ⁅a * b, t⁆ = ⁅a, t⁆ * ⁅b, t⁆ :=
  c16_comm_mul_of_abelian H.Y_comm (fun f hf => H.K_le_Y (H.comm_t f hf)) ha hb

theorem c16_N_inv (H : C16Ab K Y Q t rho z u fz fu) {a : G} (ha : a ∈ Y) :
    ⁅a⁻¹, t⁆ = (⁅a, t⁆)⁻¹ := by
  have h1 : ⁅a⁻¹, t⁆ * ⁅a, t⁆ = 1 := by
    rw [← c16_N_mul H (Y.inv_mem ha) ha, inv_mul_cancel, commutatorElement_one_left]
  exact eq_inv_of_mul_eq_one_left h1

theorem c16_Y_cases (H : C16Ab K Y Q t rho z u fz fu) {f : G} (hf : f ∈ Y) :
    ∃ κ ∈ K, f = κ ∨ f = κ * fz ∨ f = κ * fu ∨ f = κ * (fz * fu) := by
  have hfzY : fz ∈ Y := H.fz_mem
  have hfuY : fu ∈ Y := H.fu_mem
  have hfzfuY : fz * fu ∈ Y := Y.mul_mem hfzY hfuY
  rcases (H.kb.mem_iff (⁅f, t⁆)).mp (H.comm_t f hf) with h0 | hz | hu | hzu
  · exact ⟨f, H.ker_t f hf h0, Or.inl rfl⟩
  · let g : G := fz⁻¹ * f
    have hgY : g ∈ Y := Y.mul_mem (Y.inv_mem hfzY) hf
    have hgz : ⁅g, t⁆ = 1 := by
      have h1 : ⁅g, t⁆ = ⁅fz⁻¹, t⁆ * ⁅f, t⁆ := c16_N_mul H (Y.inv_mem hfzY) hf
      have h2 : ⁅fz⁻¹, t⁆ = (⁅fz, t⁆)⁻¹ := c16_N_inv H hfzY
      rw [h1, h2, H.fz_t, hz, inv_mul_cancel]
    have hgK : g ∈ K := H.ker_t g hgY hgz
    have hfg : f = g * fz := by
      calc f = fz * g := by dsimp [g]; group
        _ = g * fz := H.Y_comm fz hfzY g hgY
    exact ⟨g, hgK, Or.inr (Or.inl hfg)⟩
  · let g : G := fu⁻¹ * f
    have hgY : g ∈ Y := Y.mul_mem (Y.inv_mem hfuY) hf
    have hgz : ⁅g, t⁆ = 1 := by
      have h1 : ⁅g, t⁆ = ⁅fu⁻¹, t⁆ * ⁅f, t⁆ := c16_N_mul H (Y.inv_mem hfuY) hf
      have h2 : ⁅fu⁻¹, t⁆ = (⁅fu, t⁆)⁻¹ := c16_N_inv H hfuY
      rw [h1, h2, H.fu_t, hu, inv_mul_cancel]
    have hgK : g ∈ K := H.ker_t g hgY hgz
    have hfg : f = g * fu := by
      calc f = fu * g := by dsimp [g]; group
        _ = g * fu := H.Y_comm fu hfuY g hgY
    exact ⟨g, hgK, Or.inr (Or.inr (Or.inl hfg))⟩
  · let g : G := (fz * fu)⁻¹ * f
    have hgY : g ∈ Y := Y.mul_mem (Y.inv_mem hfzfuY) hf
    have hgz : ⁅g, t⁆ = 1 := by
      have h1 : ⁅g, t⁆ = ⁅(fz * fu)⁻¹, t⁆ * ⁅f, t⁆ := c16_N_mul H (Y.inv_mem hfzfuY) hf
      have h2 : ⁅(fz * fu)⁻¹, t⁆ = (⁅fz * fu, t⁆)⁻¹ := c16_N_inv H hfzfuY
      have h3 : ⁅fz * fu, t⁆ = z * u := by rw [c16_N_mul H hfzY hfuY, H.fz_t, H.fu_t]
      rw [h1, h2, h3, hzu, inv_mul_cancel]
    have hgK : g ∈ K := H.ker_t g hgY hgz
    have hfg : f = g * (fz * fu) := by
      calc f = (fz * fu) * g := by dsimp [g]; group
        _ = g * (fz * fu) := H.Y_comm (fz * fu) hfzfuY g hgY
    exact ⟨g, hgK, Or.inr (Or.inr (Or.inr hfg))⟩

theorem c16_rho_inv_fz (H : C16Ab K Y Q t rho z u fz fu) :
    ∃ κ ∈ K, rho⁻¹ * fz * rho = fz * fu * κ := by
  have hfzY : fz ∈ Y := H.fz_mem
  have hfuY : fu ∈ Y := H.fu_mem
  have hfzfuY : fz * fu ∈ Y := Y.mul_mem hfzY hfuY
  let w : G := rho⁻¹ * fz * rho
  have hwY : w ∈ Y := c16_rho_inv_mem H hfzY
  have hrt : rho⁻¹ * t = t * rho⁻¹ := c16_inv_comm H.rho_t
  have hwt : ⁅w, t⁆ = rho⁻¹ * z * rho := by
    have h := c16_conj_comm rho⁻¹ fz t hrt
    rw [H.fz_t] at h
    simpa [w] using h
  have hzu_conj : rho * (z * u) * rho⁻¹ = z := by
    calc rho * (z * u) * rho⁻¹
        = (rho * z * rho⁻¹) * (rho * u * rho⁻¹) := by group
      _ = u * (z * u) := by rw [H.rho_z, H.rho_u]
      _ = z := by rw [H.kb.comm, ← mul_assoc, H.kb.u_sq, one_mul]
  have hz_conj : rho⁻¹ * z * rho = z * u := by
    have h : rho⁻¹ * (rho * (z * u) * rho⁻¹) * rho = rho⁻¹ * z * rho :=
      congrArg (fun x => rho⁻¹ * x * rho) hzu_conj
    have hL : rho⁻¹ * (rho * (z * u) * rho⁻¹) * rho = z * u := by group
    rw [hL] at h
    exact h.symm
  have hwt' : ⁅w, t⁆ = z * u := by rw [hwt, hz_conj]
  let g : G := (fz * fu)⁻¹ * w
  have hgY : g ∈ Y := Y.mul_mem (Y.inv_mem hfzfuY) hwY
  have hgz : ⁅g, t⁆ = 1 := by
    have h1 : ⁅g, t⁆ = ⁅(fz * fu)⁻¹, t⁆ * ⁅w, t⁆ :=
      c16_N_mul H (Y.inv_mem hfzfuY) hwY
    have h2 : ⁅(fz * fu)⁻¹, t⁆ = (⁅fz * fu, t⁆)⁻¹ := c16_N_inv H hfzfuY
    have h3 : ⁅fz * fu, t⁆ = z * u := by rw [c16_N_mul H hfzY hfuY, H.fz_t, H.fu_t]
    rw [h1, h2, h3, hwt', inv_mul_cancel]
  have hgK : g ∈ K := H.ker_t g hgY hgz
  have hwg : w = fz * fu * g := by
    dsimp [g]
    group
  exact ⟨g, hgK, by rw [← hwg]⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
