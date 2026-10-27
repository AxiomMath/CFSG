module

public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.U3Edge
public import CFSG.ClassicalInvolution.Uniform.UThmStmtB

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly
open scoped MatrixGroups

section Top

variable {p f : ℕ} {G : Type} [Group G] [Finite G] {z : G}

theorem IsClassicalMemberU.false_of_top [IsSimpleGroup G]
    (h : IsClassicalMemberU (.sl2 p f) (⊤ : Subgroup G) z) : False := by
  have hcen : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact (h.comm_of_mem (Subgroup.mem_top g)).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h' | h'
  · rw [h', Subgroup.mem_bot] at hcen
    exact h.ne_one hcen
  · obtain ⟨x, -, y, -, hxy⟩ := h.exists_noncomm
    have hy : y ∈ Subgroup.center G := h' ▸ Subgroup.mem_top y
    exact hxy (Subgroup.mem_center_iff.mp hy x)

end Top

section Thm6

theorem thm6TypedBelowU_three_of_citBelowT {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) :
    Thm6TypedBelowU 3 1 n := by
  intro hp2 _ G _ _ _ hlt Ω hΩ _ hne _ hDE
  obtain ⟨D, hcard⟩ := exists_omegaLieU_of_simple hn hlt hΩ hne
  let i : Fin D.card := ⟨0, by omega⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · have hLie : HasLieTypeU 3 1 Ω t k := ⟨D, hcard, i, e, he, ht, hadm, hc⟩
    by_cases hG2 : t = .G2
    · subst hG2
      obtain ⟨hk, -⟩ := hadm.2.2
      subst hk
      exact Or.inr (Or.inr (Or.inl hLie))
    by_cases hD4 : t = .trialityD4
    · subst hD4
      have hk : k = 0 := hadm.2.2
      subst hk
      exact Or.inr (Or.inr (Or.inr (Or.inl hLie)))
    by_cases hL3 : t = .PSL ∧ k = 3
    · obtain ⟨rfl, rfl⟩ := hL3
      exact Or.inl hLie
    by_cases hU3 : t = .PSU ∧ k = 3
    · obtain ⟨rfl, rfl⟩ := hU3
      exact Or.inr (Or.inl hLie)
    exfalso
    have hef : e = 1 := (he.resolve_right fun h => hD4 h.1)
    subst hef
    have hA1 : ¬ (t = .PSL ∧ k = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hadm.2.2.2.2 (by simp)
    have h3' : ¬ ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) := by
      rintro (h | h)
      · exact hL3 h
      · exact hU3 h
    let M := D.toIh8Model hΩ hne hcard i ht hadm he hc
    obtain ⟨R₀, hR₀⟩ := M.cls_nonempty hne
    obtain ⟨R, hR, S, hS, hRS⟩ := exists_commuting_fund hp2 ht hadm hG2 hD4 hA1 h3' (M.cls_sub hR₀)
    have hK := M.map_mem (M.fund_subset_cls hne hG2 hD4 hR)
    have hJ := M.map_mem (M.fund_subset_cls hne hG2 hD4 hS)
    have hcomm : Commutes (R.map M.ψ) (S.map M.ψ) := ih8_commutes_map M.ψ hRS
    obtain ⟨z, hz⟩ := hΩ.classical _ hK
    obtain ⟨x, hx, y, hy, hxy⟩ := hz.exists_noncomm
    have hne' : R.map M.ψ ≠ S.map M.ψ := by
      intro h
      rw [← h] at hcomm
      exact hxy (hcomm x hx y hy)
    exact hDE _ hK _ hJ (Disconnected.dAdj_of_commutes hJ hne' hcomm)
  ·
    exfalso
    obtain ⟨K, hK⟩ := hne
    obtain ⟨z, hz⟩ := hΩ.classical K hK
    obtain ⟨j, R, hR, hKR⟩ := D.fundamental K hK
    obtain rfl : j = i := Fin.ext (by have := i.2; have := j.2; omega)
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom i) hR
    have hR'top : R' = ⊤ := Set.mem_singleton_iff.mp hR'
    have hsurj := D.hom_surjective_of_simple hΩ ⟨K, hK⟩ i
    have hKtop : K = ⊤ := by
      rw [hKR, ← hRR, hR'top, Subgroup.map_top, range_castHom]
      exact MonoidHom.range_eq_top.mpr hsurj
    rw [hKtop] at hz
    exact hz.false_of_top
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, D, hcard, i, hc⟩)))

end Thm6

end CFSG.ClassicalInvolution.Uniform
