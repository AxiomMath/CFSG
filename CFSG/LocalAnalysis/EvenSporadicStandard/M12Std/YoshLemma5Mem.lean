module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshWordCard

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b

theorem v2Perm_eq : v2Perm = wX := rfl


section Gen5Mem

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)


set_option linter.unusedSectionVars false

variable {d : G} {α β : ℕ}

theorem mem_Wsub_of_inWT {w : List (Fin 5 × Bool)} (h : inWT (tblW w) = true)
    (he : epsT (tblW w) = 0) : (wordVal w).2 ∈ Wsub := by
  have hfst := fst_eq_one_of_epsT he
  have hrep := rep_tblW w
  have hkap : kapM (wordVal w) = extHom ((wordVal w).2 : Equiv.Perm (Fin 12)) := by
    have : wordVal w = (1, (wordVal w).2) := Prod.ext hfst rfl
    rw [this, kapM_apply]
    simp [kapP_apply, tauPow_one]
  rw [mem_Wsub_iff]
  have hσ : ∀ σ : Equiv.Perm (Fin 12), tblEq 14 (tblW w) (tbl14 σ) = true →
      ((wordVal w).2 : Equiv.Perm (Fin 12)) = σ := by
    intro σ hσ
    have := (tblEq_iff_eq hrep (rep_tbl14 σ)).1 hσ
    rw [hkap] at this
    exact extHom_injective this
  unfold inWT wTabs at h
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at h
  rcases h with h | h | h | h | h | h | h | h
  · left
    have := (tblEq_idT_iff (by norm_num) hrep).1 h
    rw [hkap] at this
    exact extHom_injective (this.trans (map_one extHom).symm)
  · exact Or.inr (Or.inl (hσ _ h))
  · exact Or.inr (Or.inr (Or.inl (hσ _ h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ((hσ _ h).trans v2Perm_eq))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hσ _ h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((hσ _ h).trans (by rw [v2Perm_eq])))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ((hσ _ h).trans (by rw [v2Perm_eq]))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((hσ _ h).trans (by rw [v2Perm_eq]))))))))

theorem kWords_commT : ∀ w ∈ kWords, commT (tblW w) (tblW wJ) = true := by
  have h : kCheck = true := lemma5_parts.2.1
  unfold kCheck at h
  rw [Bool.and_eq_true] at h
  exact List.all_eq_true.1 h.2

theorem valG_mem_Nn_of_mem {w : List (Fin 5 × Bool)} (hw : w ∈ kWords) : valG e₀ w ∈ Nn e₀ :=
  HcG_le_Nn e₀ (valG_mem_HcG e₀ (kWords_commT w hw))

theorem gen5_a1_mem : gen5 e₀ d α β 0 ∈ Nn e₀ := by
  rw [gen5_a1]; exact valG_mem_Nn_of_mem e₀ (by simp [kWords])

theorem gen5_a2_mem : gen5 e₀ d α β 1 ∈ Nn e₀ := by
  rw [gen5_a2]; exact valG_mem_Nn_of_mem e₀ (by simp [kWords])

theorem gen5_b1_mem : gen5 e₀ d α β 2 ∈ Nn e₀ := by
  rw [gen5_b1]; exact valG_mem_Nn_of_mem e₀ (by simp [kWords])

theorem gen5_b2_mem : gen5 e₀ d α β 3 ∈ Nn e₀ := by
  rw [gen5_b2]; exact valG_mem_Nn_of_mem e₀ (by simp [kWords])

theorem gen5_e_mem : gen5 e₀ d α β 5 ∈ Nn e₀ := by
  rw [gen5_e]; exact valG_mem_Nn_of_mem e₀ (by simp [kWords])

theorem gen5_s_mem : gen5 e₀ d α β 7 ∈ Nn e₀ := by
  rw [gen5_s, ← valG_wSP e₀]; exact valG_mem_Nn_of_mem e₀ (by simp [kWords])

theorem gen5_t_mem : gen5 e₀ d α β 8 ∈ Nn e₀ := by
  rw [gen5_t]; exact valG_mem_Nn_of_mem e₀ (by simp [kWords])

theorem gen5_d_mem (he2 : orderOf e = 2) (hd : CentralSwap e₀ α d) : gen5 e₀ d α β 4 ∈ Nn e₀ := by
  rw [gen5_d, ← dW_one (e₀ := e₀) (d := d)]
  exact dW_mem_Nn e₀ he2 hd (by simpa using Jelt_mem_Wsub)

theorem dW_μS_mem (he2 : orderOf e = 2) (hd : CentralSwap e₀ α d) :
    dW e₀ d μS⁻¹ ∈ Nn e₀ := by
  have hw : wMemCheck = true := lemma5_parts.2.2.2.1
  unfold wMemCheck at hw
  simp only [Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩ := hw
  have hm := mem_Wsub_of_inWT h1 h2
  rw [wordVal_append, wordVal_append, wordVal_invW, wordVal_wJ] at hm
  refine dW_mem_Nn e₀ he2 hd ?_
  simpa [μS] using hm

end Gen5Mem

end CFSG.EvenSporadicStandard.M12Std.Yosh
