module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Orb
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Tri

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

theorem y7a_exclude13 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {X : Subgroup G}
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G))
    (u : Fin 3 → G) (huA : ∀ i, u i ∈ A) (hne : ∀ i j, i ≠ j → (u i)⁻¹ * u j ∉ V)
    (hnO : ∀ i, u i * t ∉ y7aO X V t)
    (hcov : ∀ w ∈ A ⊔ C0, w ∉ A ⊔ V → w ∈ y7aO X V t ∨ ∃ i, (u i * t)⁻¹ * w ∈ V)
    (r : G) (hrA : r ∈ A) (hrV : r ∉ V) (hr : r * t ∈ y7aO X V t) : False := by
  have htC : t ∈ A ⊔ C0 := Subgroup.mem_sup_right (y7a_t_mem_C0 h)
  have hAV_le : A ⊔ V ≤ A ⊔ C0 := y7a_AV_le_C1 h
  have hV_le : V ≤ A ⊔ C0 := le_trans le_sup_right hAV_le
  have hmul : ∀ i j, (u i * t)⁻¹ * (u j * t) = (u i)⁻¹ * u j := by
    intro i j
    have htj : u j * t = t * u j := h.cfg.t_cent (u j) (huA j)
    have hti : (u i)⁻¹ * t = t * (u i)⁻¹ := h.cfg.t_cent (u i)⁻¹ (A.inv_mem (huA i))
    calc (u i * t)⁻¹ * (u j * t)
        = t⁻¹ * (u i)⁻¹ * (u j * t) := by rw [mul_inv_rev]
      _ = t⁻¹ * (u i)⁻¹ * (t * u j) := by rw [htj]
      _ = t⁻¹ * ((u i)⁻¹ * t) * u j := by group
      _ = t⁻¹ * (t * (u i)⁻¹) * u j := by rw [hti]
      _ = (u i)⁻¹ * u j := by group
  have hpC : ∀ i, u i * t ∈ A ⊔ C0 := fun i =>
    (A ⊔ C0).mul_mem (Subgroup.mem_sup_left (huA i)) htC
  have hpAV : ∀ i, u i * t ∉ A ⊔ V := by
    intro i hmem
    have hmem' : (u i)⁻¹ * (u i * t) ∈ A ⊔ V :=
      (A ⊔ V).mul_mem (Subgroup.mem_sup_left (A.inv_mem (huA i))) hmem
    have heq : (u i)⁻¹ * (u i * t) = t := by group
    rw [heq] at hmem'
    exact y7a_t_not_mem_AV h hmem'
  have hne' : ∀ i j, i ≠ j → (u i * t)⁻¹ * (u j * t) ∉ V := by
    intro i j hij hmem
    rw [hmul i j] at hmem
    exact hne i j hij hmem
  have hinv : ∀ x ∈ X, ∀ i, ∃ j, (u j * t)⁻¹ * (x * (u i * t) * x⁻¹) ∈ V := by
    intro x hx i
    have hwC : x * (u i * t) * x⁻¹ ∈ A ⊔ C0 :=
      (Subgroup.mem_normalizer_iff.mp (hX1 hx) (u i * t)).mp (hpC i)
    have hwAV : x * (u i * t) * x⁻¹ ∉ A ⊔ V := by
      intro hw
      exact hpAV i ((y7a_conj_AV h (hX1 hx) (hX2 hx) (u i * t)).mpr hw)
    rcases hcov (x * (u i * t) * x⁻¹) hwC hwAV with hwO | hwj
    · exact absurd ((y7a_O_conj_iff hX2 hx).mp hwO) (hnO i)
    · exact hwj
  obtain ⟨s, hsC, hsAV, hsinv, hsne⟩ :=
    y7a_triple_sum (C := A ⊔ C0) (AV := A ⊔ V) (X := X) hV_le hAV_le
      (y7a_index_AV h) (y7a_comm_C1 h) (y7a_sq_C1 h)
      (fun x hx => ⟨hX1 hx, hX2 hx⟩) (fun i => u i * t)
      (fun i => ⟨hpC i, hpAV i⟩) hne' hinv
  have hsO : s ∈ y7aO X V t := by
    rcases hcov s hsC hsAV with hO | ⟨i, hi⟩
    · exact hO
    · exact absurd hi (hsne i)
  obtain ⟨y, hyX, hyv⟩ := hsO
  have hKey : ∀ x ∈ X, (y * t * y⁻¹)⁻¹ * ((x * y) * t * (x * y)⁻¹) ∈ V := by
    intro x hx
    have hw : x * ((y * t * y⁻¹)⁻¹ * s) * x⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hX2 hx) ((y * t * y⁻¹)⁻¹ * s)).mp hyv
    have hz : ((y * t * y⁻¹)⁻¹ * s) * (s⁻¹ * (x * s * x⁻¹)) *
        (x * ((y * t * y⁻¹)⁻¹ * s) * x⁻¹)⁻¹ ∈ V :=
      V.mul_mem (V.mul_mem hyv (hsinv x hx)) (V.inv_mem hw)
    have hZ : (y * t * y⁻¹)⁻¹ * ((x * y) * t * (x * y)⁻¹) =
        ((y * t * y⁻¹)⁻¹ * s) * (s⁻¹ * (x * s * x⁻¹)) *
          (x * ((y * t * y⁻¹)⁻¹ * s) * x⁻¹)⁻¹ := by group
    rw [hZ]
    exact hz
  have hyt : (y * t * y⁻¹)⁻¹ * t ∈ V := by
    have := hKey y⁻¹ (X.inv_mem hyX)
    simpa using this
  have hAll : ∀ x' ∈ X, (x' * t * x'⁻¹)⁻¹ * t ∈ V := by
    intro x' hx'
    have hk := hKey (x' * y⁻¹) (X.mul_mem hx' (X.inv_mem hyX))
    have hk' : (y * t * y⁻¹)⁻¹ * (x' * t * x'⁻¹) ∈ V := by simpa using hk
    have h1 := V.inv_mem hk'
    have h2 := V.mul_mem h1 hyt
    have heq : (x' * t * x'⁻¹)⁻¹ * t =
        ((y * t * y⁻¹)⁻¹ * (x' * t * x'⁻¹))⁻¹ * ((y * t * y⁻¹)⁻¹ * t) := by
      group
    rw [heq]
    exact h2
  obtain ⟨x', hx'X, hx'v⟩ := hr
  have h1 : ((x' * t * x'⁻¹)⁻¹ * t)⁻¹ ∈ V := V.inv_mem (hAll x' hx'X)
  have h2 : ((x' * t * x'⁻¹)⁻¹ * t)⁻¹ * ((x' * t * x'⁻¹)⁻¹ * (r * t)) ∈ V :=
    V.mul_mem h1 hx'v
  have heq : ((x' * t * x'⁻¹)⁻¹ * t)⁻¹ * ((x' * t * x'⁻¹)⁻¹ * (r * t)) = r := by
    have hrt : r * t = t * r := h.cfg.t_cent r hrA
    have htinv : t⁻¹ * r * t = r := by
      calc t⁻¹ * r * t = t⁻¹ * (r * t) := by group
        _ = t⁻¹ * (t * r) := by rw [hrt]
        _ = r := by group
    calc ((x' * t * x'⁻¹)⁻¹ * t)⁻¹ * ((x' * t * x'⁻¹)⁻¹ * (r * t))
        = t⁻¹ * r * t := by group
      _ = r := htinv
  rw [heq] at h2
  exact hrV h2

end CFSG.OddStandard.HigherRank.YamadaG23
