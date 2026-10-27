module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P21Hyp

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section Certs4

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

theorem p21_alpha_t_ne_one (h19 : Node19 d z₀) (h20 : Node20 d z₀) (ht : d.t ∈ Ig d) :
    alpha d d.t ≠ 1 := by
  intro h
  have hle : Ws d ≤ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    exact ((actFun_fixes_iff (Ws d) (star_mem_normalizer_Ws ht) ⟨w, hw⟩).1
      (show alpha d d.t ⟨w, hw⟩ = ⟨w, hw⟩ by rw [h]; rfl)).symm
  have hWU : Ws d = Us d := by
    rw [← h20.2.2.2.1]
    exact (inf_eq_left.2 hle).symm
  have h2 : (Us d).relIndex (Ws d) = 2 ^ 4 := h19.2.2.2.2.2.1.2.2.2.2
  rw [← hWU, Subgroup.relIndex_self] at h2
  norm_num at h2

end Certs4

section Heavy

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem p21_y1_sq (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀) {y₁ : G}
    (hy : IsV1 d z₀ y₁) : y₁ * y₁ = d.pv 2 ∨ y₁ * y₁ = d.pv 2 * d.z := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hpv2, -⟩ := h09
  obtain ⟨-, hyz, hyC, hρ⟩ := hy
  obtain ⟨s1, -, s5, -, -⟩ := Model.parrott_squares
  have hcomm : Model.parrottV 1 * Model.parrottV 5 = Model.parrottV 5 * Model.parrottV 1 :=
    Model.parrottV_commute le_rfl (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide)
  have h2D : Model.parrottV 2 ∈ titsD :=
    (Model.parrottV_mem_titsD_iff (by norm_num)).2 (by decide)
  have hyy : y₁ * y₁ ∈ centralizer ({d.t} : Set G) := mul_mem hyC hyC
  have hρyy : (d.ρ ⟨y₁ * y₁, hyy⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 2 ∨
      (d.ρ ⟨y₁ * y₁, hyy⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 2 * titsZ := by
    have e : (⟨y₁ * y₁, hyy⟩ : centralizer ({d.t} : Set G)) = ⟨y₁, hyC⟩ * ⟨y₁, hyC⟩ := rfl
    rw [e, map_mul, Subgroup.coe_mul]
    rcases hρ with h | h
    · left
      rw [h, s1]
    · right
      rw [h, Commute.mul_mul_mul_comm (show Commute (Model.parrottV 5) (Model.parrottV 1) from
        hcomm.symm), s1, s5, Model.parrottV_twelve]
  have hD : (d.ρ ⟨y₁ * y₁, hyy⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
    rcases hρyy with h | h
    · rw [h]
      exact h2D
    · rw [h]
      exact mul_mem h2D titsZ_mem_titsD
  have hL : d.lift (d.ρ ⟨y₁ * y₁, hyy⟩) = d.pv 2 ∨
      d.lift (d.ρ ⟨y₁ * y₁, hyy⟩) = d.pv 2 * d.z := by
    rcases hρyy with h | h
    · left
      rw [h]
      rfl
    · right
      rw [h, d.lift_mul h2D titsZ_mem_titsD, d.lift_titsZ]
      rfl
  have hzz0 : d.z * z₀ = z₀ * d.z := (hz.cen hd.s56_z_mem_E).symm
  have hv2z0 : d.pv 2 * z₀ = z₀ * d.pv 2 := mem_centralizer_singleton_iff.1 hpv2
  have hLc : d.lift (d.ρ ⟨y₁ * y₁, hyy⟩) * z₀ = z₀ * d.lift (d.ρ ⟨y₁ * y₁, hyy⟩) := by
    rcases hL with h | h
    · rw [h]
      exact hv2z0
    · rw [h, mul_assoc, hzz0, ← mul_assoc, hv2z0, mul_assoc]
  have h0 := hd.eq_lift_or hyy hD
  generalize d.lift (d.ρ ⟨y₁ * y₁, hyy⟩) = L at h0 hL hLc
  rcases h0 with h | h
  · rw [h]
    exact hL
  · exfalso
    apply t_not_comm_z0 hd hz
    have h1 : d.t * L * z₀ = z₀ * (d.t * L) := by
      rw [← h]
      exact (Commute.mul_left hyz hyz).eq
    have h2 : d.t * z₀ * L = z₀ * d.t * L := by
      calc d.t * z₀ * L = d.t * (z₀ * L) := by rw [mul_assoc]
        _ = d.t * (L * z₀) := by rw [hLc]
        _ = d.t * L * z₀ := by rw [mul_assoc]
        _ = z₀ * (d.t * L) := h1
        _ = z₀ * d.t * L := by rw [mul_assoc]
    exact mul_right_cancel h2

theorem p21_alpha_y1_sq (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h09 : Node09 d z₀) (h20 : Node20 d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    alpha d y₁ * alpha d y₁ = alpha d (d.pv 2) := by
  have hy1 := p21_y1_mem_Ig h20 hy
  rw [← alpha_mul hy1 hy1]
  rcases p21_y1_sq hd hz h09 hy with h | h
  · rw [h]
  · rw [h, alpha_mul (p21_pv2_mem_Ig hd h20) (p21_z_mem_Ig h49 hd), p21_alpha_z h49 hd, mul_one]

end Heavy

end CFSG.LocalAnalysis.EvenBN.Tits.N
