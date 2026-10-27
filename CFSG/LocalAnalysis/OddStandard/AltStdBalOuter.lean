module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalJ
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem exists_outer_sq_mem (h : Setting G L n) (d : Cyc L Q z)
    (hO : ¬ centralizer ({z} : Set G) ≤ L ⊔ Q) :
    ∃ u ∈ centralizer ({z} : Set G), u ∉ L ⊔ Q ∧ u ^ 2 ∈ Q := by
  obtain ⟨e⟩ := h.iso
  obtain ⟨c, hcC, hcQ⟩ := Set.not_subset.1 hO
  have hcN : c ∈ normalizer (L : Set G) := centralizer_le_normalizer h d hcC
  have hn := h.hn
  have hsgn : sign (rho e h.hn ⟨c, hcN⟩) = -1 := signHom_eq_neg_one h d e hcC hcQ
  let τ : Perm (Fin n) := swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
  have hτsgn : sign τ = -1 := sign_swap (by simp [Fin.ext_iff])
  have hmem : τ * (rho e h.hn ⟨c, hcN⟩)⁻¹ ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, map_mul, map_inv, hτsgn, hsgn]
    decide
  let l : L := e.symm ⟨τ * (rho e h.hn ⟨c, hcN⟩)⁻¹, hmem⟩
  have hlN : (l : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer l.2
  have hρl : rho e h.hn ⟨l, hlN⟩ = τ * (rho e h.hn ⟨c, hcN⟩)⁻¹ := by
    rw [rho_of_mem e h.hn l hlN]
    simp [l]
  have hlC : (l : G) ∈ centralizer ({z} : Set G) := le_centralizer_single h d l.2
  have hucC : (l : G) * c ∈ centralizer ({z} : Set G) := mul_mem hlC hcC
  refine ⟨(l : G) * c, hucC, ?_, ?_⟩
  · intro hu
    apply hcQ
    have : c = (l : G)⁻¹ * ((l : G) * c) := by group
    rw [this]
    exact mul_mem (inv_mem (mem_sup_left l.2)) hu
  · have hu2C : ((l : G) * c) ^ 2 ∈ centralizer ({z} : Set G) := pow_mem hucC 2
    have huN : (l : G) * c ∈ normalizer (L : Set G) := mul_mem hlN hcN
    let u' : normalizer (L : Set G) := ⟨(l : G) * c, huN⟩
    have hu' : u' = ⟨l, hlN⟩ * ⟨c, hcN⟩ := rfl
    have hρ : rho e h.hn (u' ^ 2) = 1 := by
      rw [hu', map_pow, map_mul, hρl]
      simp [τ, sq]
    have hK' := (rho_eq_one_iff e h.hn (u' ^ 2)).1 hρ
    have hK : ((l : G) * c) ^ 2 ∈ centralizer (L : Set G) := hK'
    rw [← cent_inf_eq h d]
    exact ⟨hK, hu2C⟩

theorem exists_outer_sq_eq (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hO : ¬ centralizer ({z} : Set G) ≤ L ⊔ Q) :
    ∃ u ∈ centralizer ({z} : Set G), u ∉ L ⊔ Q ∧ (u ^ 2 = 1 ∨ u ^ 2 = z) := by
  obtain ⟨u, hu, huQ, hu2⟩ := exists_outer_sq_mem h d hO
  exact ⟨u, hu, huQ, eq_one_or_eq_of_card_eq_two d hQ2 hu2⟩

end CFSG.OddStandard.AltStdBal
