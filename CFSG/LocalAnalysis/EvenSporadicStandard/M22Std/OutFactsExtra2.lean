module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsExtra

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup Equiv Equiv.Perm CFSG.EvenSporadicStandard.M22Std.TabCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.M23Std

section Hexad

variable {F : Subgroup (Carrier .M22)}

theorem fixes_iff_rho {α : MulAut (Carrier .M22)} (hα : ∀ y, y ∈ F ↔ α y ∈ F) (x : Fin 22) :
    (∀ f ∈ F, toPerm f x = x) ↔ ∀ f ∈ F, toPerm f (rho α x) = rho α x := by
  constructor
  · intro h f hf
    have hf' : α⁻¹ f ∈ F := (hα (α⁻¹ f)).2 (by rw [MulAut.apply_inv_self]; exact hf)
    have h1 := toPerm_apply_rho α (α⁻¹ f)
    rw [MulAut.apply_inv_self] at h1
    rw [h1]
    simp only [Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [h _ hf']
  · intro h f hf
    have h2 := h (α f) ((hα f).1 hf)
    rw [toPerm_apply_rho α f] at h2
    simp only [Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h2
    exact (rho α).injective h2

theorem preserves_hexad_aut (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1) {α : MulAut (Carrier .M22)}
    (hα : ∀ y, y ∈ F ↔ α y ∈ F) (x : Fin 22) :
    x ∈ Set.range bpt ↔ rho α x ∈ Set.range bpt := by
  rw [mem_range_bpt_iff_fix hF, mem_range_bpt_iff_fix hF]
  exact fixes_iff_rho hα x

@[expose] noncomputable def hexadAut (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1)
    (n : normalizer ((innerImage (Carrier .M22) F : Subgroup (MulAut (Carrier .M22))) :
      Set (MulAut (Carrier .M22)))) : Perm (Fin 6) :=
  (Equiv.permCongr (Equiv.ofInjective bpt bpt_injective)).symm
    ((rho (n : MulAut (Carrier .M22))).subtypePerm
      (fun x => (preserves_hexad_aut hF
        ((mem_normalizer_innerImage_iff conj_injective_m22).1 n.2) x).symm))

theorem bpt_hexadAut (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1)
    (n : normalizer ((innerImage (Carrier .M22) F : Subgroup (MulAut (Carrier .M22))) :
      Set (MulAut (Carrier .M22)))) (i : Fin 6) :
    bpt (hexadAut hF n i) = rho (n : MulAut (Carrier .M22)) (bpt i) := by
  simp only [hexadAut, Equiv.permCongr_symm, Equiv.permCongr_apply, Equiv.symm_symm]
  rw [Equiv.apply_ofInjective_symm bpt_injective]
  rfl

@[expose] noncomputable def rhoAut (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1) :
    normalizer ((innerImage (Carrier .M22) F : Subgroup (MulAut (Carrier .M22))) :
      Set (MulAut (Carrier .M22))) →* Perm (Fin 6) where
  toFun := hexadAut hF
  map_one' := by
    refine Equiv.ext fun i => bpt_injective ?_
    rw [bpt_hexadAut]
    simp
  map_mul' n m := by
    refine Equiv.ext fun i => bpt_injective ?_
    rw [bpt_hexadAut]
    simp only [Subgroup.coe_mul, map_mul, Perm.mul_apply, bpt_hexadAut]

theorem bpt_rhoAut (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1)
    (n : normalizer ((innerImage (Carrier .M22) F : Subgroup (MulAut (Carrier .M22))) :
      Set (MulAut (Carrier .M22)))) (i : Fin 6) :
    bpt (rhoAut hF n i) = rho (n : MulAut (Carrier .M22)) (bpt i) :=
  bpt_hexadAut hF n i

theorem conj_mem_normalizer {n : Carrier .M22} (hn : n ∈ normalizer (F : Set (Carrier .M22))) :
    MulAut.conj n ∈ normalizer ((innerImage (Carrier .M22) F : Subgroup (MulAut (Carrier .M22))) :
      Set (MulAut (Carrier .M22))) := by
  rw [mem_normalizer_innerImage_iff conj_injective_m22]
  intro x
  simpa [MulAut.conj_apply] using Subgroup.mem_normalizer_iff.1 hn x

theorem rhoAut_conj (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1)
    (n : normalizer (F : Set (Carrier .M22))) :
    rhoAut hF ⟨MulAut.conj (n : Carrier .M22), conj_mem_normalizer n.2⟩ = rhoHom hF n := by
  refine Equiv.ext fun i => bpt_injective ?_
  rw [bpt_rhoAut, bpt_rhoHom, rho_conj]

theorem rhoAut_betaAut (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1) :
    rhoAut hF ⟨betaAut, betaAut_mem_normalizer hF⟩ = Equiv.swap 2 3 := by
  refine Equiv.ext fun i => bpt_injective ?_
  rw [bpt_rhoAut]
  have hrho : ∀ j : Fin 22, ((rho betaAut j : Fin 22) : ℕ) = betaTab.getD j.val 0 := by
    intro j
    have := getD_tabP (rho betaAut) j
    rw [← this, show tabP (rho betaAut) = betaTab from autTab_betaAut]
  refine Fin.ext ?_
  show ((rho betaAut (bpt i) : Fin 22) : ℕ) = ((bpt (Equiv.swap 2 3 i) : Fin 22) : ℕ)
  rw [hrho]
  fin_cases i <;> decide

end Hexad

section Final

variable {F : Subgroup (Carrier .M22)}

theorem subgroupOf_le_ker_rhoAut (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1) :
    (innerImage (Carrier .M22) F).subgroupOf
      (normalizer ((innerImage (Carrier .M22) F : Subgroup (MulAut (Carrier .M22))) :
        Set (MulAut (Carrier .M22)))) ≤ (rhoAut hF).ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  obtain ⟨f, hf, hfn⟩ : (n : MulAut (Carrier .M22)) ∈ innerImage (Carrier .M22) F := hn
  refine Equiv.ext fun i => bpt_injective ?_
  rw [bpt_rhoAut, ← hfn, rho_conj]
  have := (mem_range_bpt_iff_fix hF (bpt i)).1 ⟨i, rfl⟩ f hf
  simpa using this

theorem range_rhoAut (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1) : (rhoAut hF).range = ⊤ := by
  set R := (rhoAut hF).range with hR
  have hmemR : ∀ n : normalizer (F : Set (Carrier .M22)), rhoHom hF n ∈ R := fun n =>
    ⟨⟨MulAut.conj (n : Carrier .M22), conj_mem_normalizer n.2⟩, rhoAut_conj hF n⟩
  have hAR : alternatingGroup (Fin 6) ≤ R :=
    alternatingGroup_le_of_five_cycle R (p := 4) (rhoHom_g5_isCycle hF) (rhoHom_g5_fix hF)
      (rhoHom_g5_moves hF) (hmemR _) (rhoHom_g3_isThreeCycle hF) (hmemR _) (hmemR _)
      (rhoHom_g3_moves hF)
  have hs : Equiv.swap (2 : Fin 6) 3 ∈ R :=
    ⟨⟨betaAut, betaAut_mem_normalizer hF⟩, rhoAut_betaAut hF⟩
  rw [eq_top_iff]
  intro σ _
  by_cases hσ : σ ∈ alternatingGroup (Fin 6)
  · exact hAR hσ
  · have hσs : σ * Equiv.swap 2 3 ∈ alternatingGroup (Fin 6) := by
      rw [mem_alternatingGroup] at hσ ⊢
      rw [map_mul, Perm.sign_swap (by decide)]
      rcases Int.units_eq_one_or (Perm.sign σ) with h | h
      · exact absurd h hσ
      · rw [h]
        decide
    have := R.mul_mem (hAR hσs) (R.inv_mem hs)
    simpa using this

theorem normQuot_aut (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1)
    (D : NData (⊤ : Subgroup (Carrier .M22)) F) :
    NormQuot (Perm (Fin 6))
      (normalizer ((innerImage (Carrier .M22) F : Subgroup (MulAut (Carrier .M22))) :
        Set (MulAut (Carrier .M22)))) (innerImage (Carrier .M22) F) := by
  refine ⟨rhoAut hF, MonoidHom.range_eq_top.1 (range_rhoAut hF), ?_⟩
  have hFN : innerImage (Carrier .M22) F ≤ normalizer ((innerImage (Carrier .M22) F :
      Subgroup (MulAut (Carrier .M22))) : Set (MulAut (Carrier .M22))) := Subgroup.le_normalizer
  refine (Subgroup.eq_of_le_of_card_ge (subgroupOf_le_ker_rhoAut hF) ?_).symm
  have h1 := Subgroup.card_ker_mul_card_range (rhoAut hF)
  rw [range_rhoAut, Subgroup.card_top, card_normalizer_innerImage hF D,
    Nat.card_eq_fintype_card (α := Perm (Fin 6)), Fintype.card_perm, Fintype.card_fin] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv, card_innerImage D.F_card]
  have h2 : Nat.card (rhoAut hF).ker * 720 = 11520 := by
    rw [← h1]
    simp [Nat.factorial]
  omega

end Final

end CFSG.EvenSporadicStandard.M22Std
