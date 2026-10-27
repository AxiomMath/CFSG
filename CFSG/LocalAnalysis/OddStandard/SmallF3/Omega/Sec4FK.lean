module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FKA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FKB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FKconj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FSixSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G}
  {x : G} {φ : (Fin 7 → ZMod 2) → G}

private lemma sec4FK_sq_conj {G : Type*} [Group G] {t g : G} (ht : t * t = 1) :
    (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
  calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
    _ = 1 := by rw [ht]; group

private lemma sec4FK_inv_conj {G : Type*} [Group G] {t g : G} (ht : t * t = 1) :
    (g⁻¹ * t * g)⁻¹ = g⁻¹ * t * g := by
  rw [show (g⁻¹ * t * g)⁻¹ = g⁻¹ * t⁻¹ * g by group, inv_eq_of_mul_eq_one_right ht]

private lemma sec4FK_comm_of_conj_eq_self {G : Type*} [Group G] {y κ : G} (hyy : y * y = 1)
    (h : y * κ * y = κ) : κ * y = y * κ := by
  have h2 : y * κ = κ * y := by
    calc y * κ = y * κ * (y * y) := by rw [hyy, mul_one]
      _ = (y * κ * y) * y := by group
      _ = κ * y := by rw [h]
  exact h2.symm

theorem Sec4FSetup.K_core (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) {y : G}
    (hy : ∃ g : G, y = g⁻¹ * t * g)
    (h1 : ∀ a, ∃ e, y * sec4MPt t φ a * y = sec4FD t φ x e)
    (h2 : ∀ c, ∃ q, y * sec4FD t φ x c * y = sec4MPt t φ q) : False := by
  have hyy : y * y = 1 := by
    obtain ⟨g, hg⟩ := hy
    rw [hg]
    exact sec4FK_sq_conj h.t_sq
  obtain ⟨a₁', c₁, c₁', hb₁⟩ := h.blocks hT none
  by_cases hfix₁ : y * (sec4MPt t φ none * sec4MPt t φ a₁') * y
      = sec4MPt t φ none * sec4MPt t φ a₁'
  · obtain ⟨b, hbnone, hba'⟩ : ∃ b : Option (Fin 7), b ≠ none ∧ b ≠ a₁' := by
      by_cases h0 : a₁' = some 0
      · exact ⟨some 1, by decide, by rw [h0]; decide⟩
      · exact ⟨some 0, by decide, fun hh => h0 hh.symm⟩
    obtain ⟨b', e, e', hb₂⟩ := h.blocks hT b
    by_cases hfix₂ : y * (sec4MPt t φ b * sec4MPt t φ b') * y
        = sec4MPt t φ b * sec4MPt t φ b'
    · have hdisj := sec4F_block_disjoint hb₁ hb₂ hbnone hba'
      have hκ₁ne : sec4MPt t φ none * sec4MPt t φ a₁' ≠ 1 := by
        intro hprod
        have h1' : sec4MPt t φ none = (sec4MPt t φ a₁')⁻¹ :=
          mul_eq_one_iff_eq_inv.mp hprod
        have h2' : (sec4MPt t φ a₁')⁻¹ = sec4MPt t φ a₁' :=
          inv_eq_of_mul_eq_one_right (h.A_sq (sec4MPt_mem_A h.data a₁'))
        exact hb₁.1 (h.pt_injective (h1'.trans h2'))
      have hκ₂ne : sec4MPt t φ b * sec4MPt t φ b' ≠ 1 := by
        intro hprod
        have h1' : sec4MPt t φ b = (sec4MPt t φ b')⁻¹ :=
          mul_eq_one_iff_eq_inv.mp hprod
        have h2' : (sec4MPt t φ b')⁻¹ = sec4MPt t φ b' :=
          inv_eq_of_mul_eq_one_right (h.A_sq (sec4MPt_mem_A h.data b'))
        exact hb₂.1 (h.pt_injective (h1'.trans h2'))
      have hκ₁y : (sec4MPt t φ none * sec4MPt t φ a₁') * y
          = y * (sec4MPt t φ none * sec4MPt t φ a₁') :=
        sec4FK_comm_of_conj_eq_self hyy hfix₁
      have hκ₂y : (sec4MPt t φ b * sec4MPt t φ b') * y
          = y * (sec4MPt t φ b * sec4MPt t φ b') :=
        sec4FK_comm_of_conj_eq_self hyy hfix₂
      have hκ₁mem : sec4MPt t φ none * sec4MPt t φ a₁' ∈ A :=
        mul_mem (sec4MPt_mem_A h.data none) (sec4MPt_mem_A h.data a₁')
      have hκ₂mem : sec4MPt t φ b * sec4MPt t φ b' ∈ A :=
        mul_mem (sec4MPt_mem_A h.data b) (sec4MPt_mem_A h.data b')
      have hκ₁₂ : (sec4MPt t φ none * sec4MPt t φ a₁') * (sec4MPt t φ b * sec4MPt t φ b')
          = (sec4MPt t φ b * sec4MPt t φ b') * (sec4MPt t φ none * sec4MPt t φ a₁') :=
        h.A_comm hκ₁mem hκ₂mem
      obtain ⟨k₁, hyκ₁⟩ := h.K_fixed hT hy h1 hb₁ hfix₁
      obtain ⟨k₂, hyκ₂⟩ := h.K_fixed hT hy h1 hb₂ hfix₂
      obtain ⟨hz, -⟩ := h.four_pts hb₁.1 hbnone.symm hdisj.1.symm hba'.symm hdisj.2.symm hb₂.1
      exact sec4F_sixsix_contra h.inputs h.ctx h.not_tz hy hκ₁ne hκ₂ne hκ₁y hκ₂y hκ₁₂
        ⟨k₁, hyκ₁⟩ ⟨k₂, hyκ₂⟩ hz
    · exact h.K_moved hT hy h1 h2 hb₂ hfix₂
  · exact h.K_moved hT hy h1 h2 hb₁ hfix₁

theorem Sec4FSetup.K (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) {p : G}
    (hp : p ∈ P) (hy : ∃ g : G, x * p = g⁻¹ * t * g) : False := by
  have hinv : (x * p)⁻¹ = x * p := by
    obtain ⟨g, hg⟩ := hy
    rw [hg]
    exact sec4FK_inv_conj h.t_sq
  exact h.K_core hT hy
    (fun a => by
      obtain ⟨e, he⟩ := h.K_to_d hT hp a
      exact ⟨e, by simpa only [hinv] using he⟩)
    (fun c => by
      obtain ⟨q, hq⟩ := h.K_to_pt hT hp c
      exact ⟨q, by simpa only [hinv] using hq⟩)

end CFSG.OddStandard.SmallF3.Omega
