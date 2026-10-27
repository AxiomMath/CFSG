module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDDataCore

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SD

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.HSFLit

variable {X : Type} [Group X] {t : X} {L : Subgroup X}

@[expose] noncomputable def ψX (A : SDData t L) (g : X) : Perm (ZMod 8) :=
  open Classical in if h : g ∈ A.T then A.ψ ⟨g, h⟩ else 1

variable {A : SDData t L}

theorem ψX_of_mem {g : X} (hg : g ∈ A.T) : ψX A g = A.ψ ⟨g, hg⟩ := by
  simp [ψX, hg]

theorem ψX_mul {g h : X} (hg : g ∈ A.T) (hh : h ∈ A.T) : ψX A (g * h) = ψX A g * ψX A h := by
  rw [ψX_of_mem hg, ψX_of_mem hh, ψX_of_mem (mul_mem hg hh), ← map_mul]
  rfl

theorem ψX_inv {g : X} (hg : g ∈ A.T) : ψX A g⁻¹ = (ψX A g)⁻¹ := by
  rw [ψX_of_mem hg, ψX_of_mem (inv_mem hg), ← map_inv]
  rfl

theorem ψX_one : ψX A (1 : X) = 1 := by
  rw [ψX_of_mem (one_mem _), show (⟨1, _⟩ : A.T) = 1 from rfl, map_one]

theorem ψX_pow {g : X} (hg : g ∈ A.T) (n : ℕ) : ψX A (g ^ n) = ψX A g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ψX_one]
  | succ n ih => rw [pow_succ, ψX_mul (pow_mem hg n) hg, ih, pow_succ]

theorem ψX_conj {g h : X} (hg : g ∈ A.T) (hh : h ∈ A.T) :
    ψX A (g * h * g⁻¹) = ψX A g * ψX A h * (ψX A g)⁻¹ := by
  rw [ψX_mul (mul_mem hg hh) (inv_mem hg), ψX_mul hg hh, ψX_inv hg]

theorem ψX_comm {g h : X} (hg : g ∈ A.T) (hh : h ∈ A.T) :
    ψX A (g * h * g⁻¹ * h⁻¹) = ψX A g * ψX A h * (ψX A g)⁻¹ * (ψX A h)⁻¹ := by
  rw [ψX_mul (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh), ψX_conj hg hh, ψX_inv hh]

theorem ψX_eq_one_iff {g : X} (hg : g ∈ A.T) : ψX A g = 1 ↔ g ∈ A.K := by
  rw [ψX_of_mem hg, A.mem_K_iff hg]

theorem ψX_mem_R8 {g : X} (hg : g ∈ A.R) : ψX A g ∈ R8 := by
  rw [ψX_of_mem hg.1]
  exact A.ψ_mem_R8' hg

theorem ψX_mem_S16 {g : X} (hg : g ∈ A.T) (hL : g ∈ L) : ψX A g ∈ S16 := by
  rw [ψX_of_mem hg]
  exact A.ψ_mem_S16 ⟨g, hg⟩ hL

theorem ψX_t : ψX A t = 1 := (ψX_eq_one_iff A.t_mem_T).mpr A.t_mem_K

theorem ψX_mem_H8' {g : X} (hg : g ∈ A.T) : ψX A g ∈ H8 := by
  rw [ψX_of_mem hg]
  exact A.ψ_mem_H8 _

theorem exists_mem_R_ψX_eq {σ : Perm (ZMod 8)} (hσ : σ ∈ R8) : ∃ r ∈ A.R, ψX A r = σ := by
  obtain ⟨r, hr, hψ⟩ := A.exists_mem_R_ψ_eq hσ
  exact ⟨r, hr, by rw [ψX_of_mem hr.1, hψ]⟩

include A in
theorem t_ne_one : t ≠ 1 := by
  intro h
  have := A.orderOf_t
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

include A in
theorem t_sq : t ^ 2 = 1 := by
  rw [← A.orderOf_t]
  exact pow_orderOf_eq_one t

theorem t_mem_C : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl

theorem commute_t_of_mem_C {g : X} (hg : g ∈ centralizer ({t} : Set X)) : g * t = t * g :=
  mem_centralizer_singleton_iff.mp hg

structure Gens (A : SDData t L) where
  x₀ : X
  y₀ : X
  x₀_mem : x₀ ∈ A.R
  y₀_mem : y₀ ∈ A.R
  ψ_x₀ : ψX A x₀ = x8
  ψ_y₀ : ψX A y₀ = y8

include A in
theorem nonempty_gens : Nonempty (Gens A) := by
  obtain ⟨x₀, hx, hψx⟩ := exists_mem_R_ψX_eq (A := A) x8_mem_R8
  obtain ⟨y₀, hy, hψy⟩ := exists_mem_R_ψX_eq (A := A) y8_mem_R8
  exact ⟨⟨x₀, y₀, hx, hy, hψx, hψy⟩⟩

namespace Gens

variable (S : Gens A)

abbrev z : X := S.x₀ ^ 2

theorem z_mem : S.z ∈ A.R := pow_mem S.x₀_mem 2

theorem ψ_z : ψX A S.z = z8 := by rw [ψX_pow S.x₀_mem.1, S.ψ_x₀, x8_sq]

theorem z_ne_one : S.z ≠ 1 := by
  intro h
  have := S.ψ_z
  rw [h, ψX_one] at this
  exact z8_ne_one this.symm

end Gens

variable [Finite X]

include A in
theorem le_normalizer : centralizer ({t} : Set X) ≤ normalizer (L : Set X) :=
  A.config.le_normalizer

include A in
theorem conj_mem_L {g l : X} (hg : g ∈ centralizer ({t} : Set X)) (hl : l ∈ L) :
    g * l * g⁻¹ ∈ L :=
  (mem_normalizer_iff.mp (le_normalizer (A := A) hg) l).mp hl

theorem conj_mem_R_of_mem_T {g r : X} (hg : g ∈ A.T) (hr : r ∈ A.R) : g * r * g⁻¹ ∈ A.R := by
  have hgr : g * r * g⁻¹ ∈ A.T := mul_mem (mul_mem hg hr.1) (inv_mem hg)
  refine ⟨hgr, (A.mem_D hgr).mpr ⟨conj_mem_L (A := A) (A.T_le_centralizer hg) (A.R_le_L hr), ?_⟩⟩
  rw [← ψX_of_mem hgr, ψX_conj hg hr.1]
  exact conj_mem_R8 (ψX_mem_H8' hg) (ψX_mem_R8 hr)

theorem eq_of_ψX_eq {g h : X} (hg : g ∈ A.R) (hh : h ∈ A.R)
    (hgh : ψX A g = ψX A h) : g = h := by
  rw [ψX_of_mem hg.1, ψX_of_mem hh.1] at hgh
  exact A.eq_of_ψ_eq hg hh hgh

theorem eq_one_of_ψX {g : X} (hg : g ∈ A.R) (h1 : ψX A g = 1) : g = 1 :=
  eq_of_ψX_eq hg (one_mem _) (by rw [h1, ψX_one])

namespace Gens

variable (S : Gens A)

theorem x₀_pow_four : S.x₀ ^ 4 = 1 :=
  eq_one_of_ψX (pow_mem S.x₀_mem 4) (by rw [ψX_pow S.x₀_mem.1, S.ψ_x₀, x8_pow_four])

theorem orderOf_x₀ : orderOf S.x₀ = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by rw [pow_one]; exact S.z_ne_one)
    (by rw [show (2 : ℕ) ^ (1 + 1) = 4 by rfl]; exact S.x₀_pow_four)

theorem y₀_sq : S.y₀ ^ 2 = 1 :=
  eq_one_of_ψX (pow_mem S.y₀_mem 2) (by rw [ψX_pow S.y₀_mem.1, S.ψ_y₀, y8_sq])

theorem y₀_x₀_y₀ : S.y₀ * S.x₀ * S.y₀⁻¹ = S.x₀⁻¹ := by
  have hm : S.y₀ * S.x₀ * S.y₀⁻¹ ∈ A.R := mul_mem (mul_mem S.y₀_mem S.x₀_mem) (inv_mem S.y₀_mem)
  refine eq_of_ψX_eq hm (inv_mem S.x₀_mem) ?_
  rw [ψX_conj S.y₀_mem.1 S.x₀_mem.1, ψX_inv S.x₀_mem.1, S.ψ_x₀, S.ψ_y₀, y8_x8_y8]

theorem z_comm_R {r : X} (hr : r ∈ A.R) : S.z * r = r * S.z := by
  have hm : S.z * r * S.z⁻¹ * r⁻¹ ∈ A.R :=
    mul_mem (mul_mem (mul_mem S.z_mem hr) (inv_mem S.z_mem)) (inv_mem hr)
  have h1 : S.z * r * S.z⁻¹ * r⁻¹ = 1 := by
    refine eq_one_of_ψX hm ?_
    obtain ⟨u, c, -, hc⟩ := ψX_mem_R8 hr
    rw [ψX_comm S.z_mem.1 hr.1, S.ψ_z, ← hc, ← z8_comm_aff8']
    group
  calc S.z * r = S.z * r * S.z⁻¹ * r⁻¹ * (r * S.z) := by group
    _ = r * S.z := by rw [h1, one_mul]

end Gens

end CFSG.OddStandard.SmallF3.L33.KD.SD
