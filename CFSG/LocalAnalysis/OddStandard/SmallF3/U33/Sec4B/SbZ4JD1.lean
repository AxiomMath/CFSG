module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

theorem comm_t_mem_E (g : H) : g * t * g⁻¹ * t⁻¹ ∈ centralizer (Y : Set H) := by
  have hmem : zjMat y z v₁ v₂ (g⁻¹ * t) = zjMat y z v₁ v₂ (t * g⁻¹) := by
    rw [h.mat_mul, h.mat_mul, h.mat_t]
    exact (ZJFin.T_central (zjMat y z v₁ v₂ g⁻¹) (h.mat_mem_S48 g⁻¹)).symm
  have hc : (g⁻¹ * t)⁻¹ * (t * g⁻¹) ∈ centralizer (Y : Set H) :=
    (h.mat_eq_iff (g⁻¹ * t) (t * g⁻¹)).mp hmem
  have h1 : t * ((g⁻¹ * t)⁻¹ * (t * g⁻¹)) * t⁻¹ ∈ centralizer (Y : Set H) :=
    h.E_normal (g := t) hc
  have hgoal : t * ((g⁻¹ * t)⁻¹ * (t * g⁻¹)) * t⁻¹ = g * t * g⁻¹ * t⁻¹ := by group
  rw [hgoal] at h1
  exact h1

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

theorem Mh_cent_V {m v : H} (hm : m ∈ Mh) (hv : v ∈ V) : m * v * m⁻¹ = v := by
  have hVY : V ≤ Y := by
    rw [h.Y_eq]
    exact le_sup_left
  have hvY : v ∈ Y := hVY hv
  have hmM : zjMat y z v₁ v₂ m ∈ ZJFin.Mlist := (hMh m).mp hm
  have hn4 : zjCode y z v₁ v₂ v < 4 := (h.code_lt_four_iff hvY).mpr hv
  have hn16 : zjCode y z v₁ v₂ v < 16 := by omega
  have happ := h.mat_app hn16 m
  have hfix := ZJFin.M_triv_V4 (zjMat y z v₁ v₂ m) hmM (zjCode y z v₁ v₂ v)
    (List.mem_range.mpr hn4)
  have hcode : zjCode y z v₁ v₂ (m * v * m⁻¹) = zjCode y z v₁ v₂ v := by
    have e : m * zjVec y z v₁ v₂ (zjCode y z v₁ v₂ v) * m⁻¹ = m * v * m⁻¹ := by
      rw [h.vec_code hvY]
    rw [← e, ← happ, hfix]
  have hmemY : m * v * m⁻¹ ∈ Y := h.normal_Y m v hvY
  exact h.eq_of_code_eq hmemY hvY hcode

theorem Mh_comm_Y {m u : H} (hm : m ∈ Mh) (hu : u ∈ Y) : m * u * m⁻¹ * u⁻¹ ∈ V := by
  have hmM : zjMat y z v₁ v₂ m ∈ ZJFin.Mlist := (hMh m).mp hm
  have hn16 : zjCode y z v₁ v₂ u < 16 := h.code_lt hu
  have happ := h.mat_app hn16 m
  have htriv := ZJFin.M_triv_YV (zjMat y z v₁ v₂ m) hmM (zjCode y z v₁ v₂ u)
    (List.mem_range.mpr hn16)
  have hconjY : m * u * m⁻¹ ∈ Y := h.normal_Y m u hu
  have hcode1 : zjCode y z v₁ v₂ (m * u * m⁻¹) ^^^ zjCode y z v₁ v₂ u < 4 := by
    have e : m * zjVec y z v₁ v₂ (zjCode y z v₁ v₂ u) * m⁻¹ = m * u * m⁻¹ := by
      rw [h.vec_code hu]
    rw [← e, ← happ]
    exact htriv
  have hwu : u⁻¹ = u := inv_eq_of_mul_eq_one_right (h.Y_sq u hu)
  have hwY : m * u * m⁻¹ * u⁻¹ ∈ Y := mul_mem hconjY (Y.inv_mem hu)
  have hw : m * u * m⁻¹ * u⁻¹ = (m * u * m⁻¹) * u := by rw [hwu]
  have hcodew : zjCode y z v₁ v₂ (m * u * m⁻¹ * u⁻¹) < 4 := by
    rw [hw, h.code_mul hconjY hu]
    exact hcode1
  exact (h.code_lt_four_iff hwY).mp hcodew

theorem Mh_cent_Y {m u : H} (hm : m ∈ Mh) (hmE : m ∉ centralizer (Y : Set H)) (hu : u ∈ Y)
    (hc : m * u * m⁻¹ = u) : u ∈ V := by
  have hmM : zjMat y z v₁ v₂ m ∈ ZJFin.Mlist := (hMh m).mp hm
  have hne : zjMat y z v₁ v₂ m ≠ ZJFin.one := by
    intro h1
    apply hmE
    have h2 : zjMat y z v₁ v₂ (1 : H) = zjMat y z v₁ v₂ m := by rw [h.mat_one, h1]
    simpa using (h.mat_eq_iff 1 m).mp h2
  have hn16 : zjCode y z v₁ v₂ u < 16 := h.code_lt hu
  have happ := h.mat_app hn16 m
  have hcode : ZJFin.app (zjMat y z v₁ v₂ m) (zjCode y z v₁ v₂ u) = zjCode y z v₁ v₂ u := by
    rw [happ]
    rw [h.vec_code hu, hc]
  have hn4 : zjCode y z v₁ v₂ u < 4 :=
    ZJFin.M_cent_Y (zjMat y z v₁ v₂ m) hmM hne (zjCode y z v₁ v₂ u)
      (List.mem_range.mpr hn16) hcode
  exact (h.code_lt_four_iff hu).mp hn4

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
