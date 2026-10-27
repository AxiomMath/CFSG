module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JC1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JC4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JB4

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {H : Type} [Group H] [Finite H]
variable {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

private theorem mmul_rho_comm {a : ℕ} (ha : a ∈ ZJFin.Clist) :
    ZJFin.mmul a (zjMat y z v₁ v₂ ρ) = ZJFin.mmul (zjMat y z v₁ v₂ ρ) a := by
  have hc := ZJFin.Clist_comm a ha
  rcases h.mat_rho with hR | hR
  · rw [hR]; exact hc.1
  · rw [hR]; exact hc.2

private theorem commutator_mem_E {u v : H}
    (huv : zjMat y z v₁ v₂ (u * v) = zjMat y z v₁ v₂ (v * u)) :
    u * v * u⁻¹ * v⁻¹ ∈ centralizer (Y : Set H) := by
  have hc : (u * v)⁻¹ * (v * u) ∈ centralizer (Y : Set H) :=
    (h.mat_eq_iff (u * v) (v * u)).mp huv
  have h1 : u * ((u * v)⁻¹ * (v * u)) * u⁻¹ ∈ centralizer (Y : Set H) :=
    h.E_normal (g := u) hc
  have h2 : v * (u * ((u * v)⁻¹ * (v * u)) * u⁻¹) * v⁻¹ ∈ centralizer (Y : Set H) :=
    h.E_normal (g := v) h1
  have hgoal : v * (u * ((u * v)⁻¹ * (v * u)) * u⁻¹) * v⁻¹ =
      (u * v * u⁻¹ * v⁻¹)⁻¹ := by group
  rw [hgoal] at h2
  simpa using (centralizer (Y : Set H)).inv_mem h2

private theorem sq_mem_E {g : H}
    (hg : ZJFin.mmul (zjMat y z v₁ v₂ g) (zjMat y z v₁ v₂ g) = ZJFin.one) :
    g * g ∈ centralizer (Y : Set H) := by
  have hm : zjMat y z v₁ v₂ (g * g) = ZJFin.one := by rw [h.mat_mul, hg]
  have h1 : zjMat y z v₁ v₂ (1 : H) = zjMat y z v₁ v₂ (g * g) := by
    rw [h.mat_one, hm]
  have h2 := (h.mat_eq_iff 1 (g * g)).mp h1
  simpa using h2

private theorem pow_four_mem_E {g : H}
    (hg : ZJFin.mmul (ZJFin.mmul (zjMat y z v₁ v₂ g) (zjMat y z v₁ v₂ g))
      (ZJFin.mmul (zjMat y z v₁ v₂ g) (zjMat y z v₁ v₂ g)) = ZJFin.one) :
    g * g * (g * g) ∈ centralizer (Y : Set H) := by
  have h1 : zjMat y z v₁ v₂ (g * g) =
      ZJFin.mmul (zjMat y z v₁ v₂ g) (zjMat y z v₁ v₂ g) := h.mat_mul g g
  have h2 : zjMat y z v₁ v₂ ((g * g) * (g * g)) =
      ZJFin.mmul (zjMat y z v₁ v₂ (g * g)) (zjMat y z v₁ v₂ (g * g)) :=
    h.mat_mul (g * g) (g * g)
  have hm : zjMat y z v₁ v₂ (g * g * (g * g)) = ZJFin.one := by
    rw [show g * g * (g * g) = (g * g) * (g * g) by group, h2, h1, hg]
  have h3 : zjMat y z v₁ v₂ (1 : H) = zjMat y z v₁ v₂ (g * g * (g * g)) := by
    rw [h.mat_one, hm]
  have h4 := (h.mat_eq_iff 1 (g * g * (g * g))).mp h3
  simpa using h4

theorem mat_range : Set.range (zjMat y z v₁ v₂) = {x | x ∈ ZJFin.S48} := by
  apply ZJFin.ff1
  · rintro x ⟨g, rfl⟩
    exact h.mat_mem_P g
  · exact ⟨1, h.mat_one⟩
  · rintro a ⟨g, rfl⟩ b ⟨g', rfl⟩
    exact ⟨g * g', h.mat_mul g g'⟩
  · exact ⟨t, h.mat_t⟩
  · exact ⟨l, h.mat_l⟩
  · rcases h.mat_rho with hρ | hρ
    · exact ⟨ρ, hρ⟩
    · exact ⟨ρ * ρ, by rw [h.mat_mul, hρ, ZJFin.R2_sq.1]⟩
  · rintro (⟨a, haS, haCl, ha1, ha2, ha4⟩ |
      ⟨a, haS, b, hbS, haCl, hbCl, ha1, hb1, ha2, hb2, habne, habc⟩)
    · rcases haS with ⟨g, rfl⟩
      refine h.no_order_four (commutator_mem_E h ?_) ?_ (pow_four_mem_E h ha4)
      · rw [h.mat_mul, h.mat_mul, mmul_rho_comm h haCl]
      · intro hmem
        apply ha2
        have h1 : zjMat y z v₁ v₂ (1 : H) = zjMat y z v₁ v₂ (g * g) :=
          (h.mat_eq_iff 1 (g * g)).mpr (by simpa using hmem)
        rw [h.mat_one] at h1
        exact (h1.trans (h.mat_mul g g)).symm
    · rcases haS with ⟨g, rfl⟩
      rcases hbS with ⟨g', rfl⟩
      refine h.no_klein (commutator_mem_E h ?_) (commutator_mem_E h ?_)
        (sq_mem_E h ha2) (sq_mem_E h hb2) ?_ ?_ ?_ (commutator_mem_E h ?_)
      · rw [h.mat_mul, h.mat_mul, mmul_rho_comm h haCl]
      · rw [h.mat_mul, h.mat_mul, mmul_rho_comm h hbCl]
      · intro hmem
        apply ha1
        have h1 : zjMat y z v₁ v₂ (1 : H) = zjMat y z v₁ v₂ g :=
          (h.mat_eq_iff 1 g).mpr (by simpa using hmem)
        rw [h.mat_one] at h1
        exact h1.symm
      · intro hmem
        apply hb1
        have h1 : zjMat y z v₁ v₂ (1 : H) = zjMat y z v₁ v₂ g' :=
          (h.mat_eq_iff 1 g').mpr (by simpa using hmem)
        rw [h.mat_one] at h1
        exact h1.symm
      · intro hmem
        exact habne ((h.mat_eq_iff g g').mpr hmem)
      · rw [h.mat_mul, h.mat_mul, habc]
  · have hS : Nat.card (Set.range (zjMat y z v₁ v₂)) * 128 = Nat.card H := by
      rw [← h.card_E]
      exact h.card_range_mat
    have hdiv : 2 ^ 10 ∣ Nat.card (Set.range (zjMat y z v₁ v₂)) * 128 := by
      rw [hS]
      exact h.two_pow_ten
    have hpow : 2 ^ 10 = 8 * 128 := by norm_num
    rw [hpow] at hdiv
    have h8 : 8 ∣ Nat.card (Set.range (zjMat y z v₁ v₂)) :=
      Nat.dvd_of_mul_dvd_mul_right (by norm_num) hdiv
    simpa using h8

theorem mat_mem_S48 (g : H) : zjMat y z v₁ v₂ g ∈ ZJFin.S48 := by
  have hmem : zjMat y z v₁ v₂ g ∈ Set.range (zjMat y z v₁ v₂) := Set.mem_range_self g
  rw [mat_range h] at hmem
  exact hmem

theorem exists_mat {x : ℕ} (hx : x ∈ ZJFin.S48) : ∃ g : H, zjMat y z v₁ v₂ g = x := by
  have hrange := mat_range h
  have hx' : x ∈ Set.range (zjMat y z v₁ v₂) := by rwa [hrange]
  exact Set.mem_range.mp hx'

theorem card_H : Nat.card H = 6144 := by
  have hcard48 : Nat.card (Set.range (zjMat y z v₁ v₂)) = 48 := by
    rw [mat_range h]
    rw [show {x : ℕ | x ∈ ZJFin.S48} = (↑ZJFin.S48.toFinset : Set ℕ) by ext x; simp]
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup ZJFin.S48_card.2]
    exact ZJFin.S48_card.1
  have hEq : 48 * 128 = Nat.card H := by
    rw [← hcard48, ← h.card_E]
    exact h.card_range_mat
  calc Nat.card H = 48 * 128 := hEq.symm
    _ = 6144 := by norm_num

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
