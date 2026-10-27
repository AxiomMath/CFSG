module

public import CFSG.ClassicalInvolution.Phan.PhanDn.CompGraph

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem exists_mem_ptsOn_of_isFlipLine (hσ : IsUnitaryInvolution σ) {n : ℕ}
    {L : Submodule K (Fin n ⊕ Fin n → K)} (hL : IsFlipLine σ L) :
    (ptsOn σ L).Nonempty := by
  have hne : L ≠ ⊥ := by
    intro hbot
    have h := hL.2
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨v, hvL, hvh⟩ :=
    exists_anisotropic_of_isFlipflopSub hσ.invol hσ.exists_ne hL.1 hne
  have hv0 : v ≠ 0 := fun h => hvh (by rw [h]; simp)
  refine ⟨K ∙ v, ?_, ?_⟩
  · exact (isFlipflopPt_span_singleton_iff hv0).mpr ⟨hL.1.total v hvL, hvh⟩
  · exact (Submodule.span_singleton_le_iff_mem v L).mpr hvL

theorem sup_eq_of_mem_ptsOn {n : ℕ} {L p q : Submodule K (Fin n ⊕ Fin n → K)}
    (hL : IsFlipLine σ L) (hp : p ∈ ptsOn σ L) (hq : q ∈ ptsOn σ L) (hpq : p ≠ q) :
    p ⊔ q = L := by
  have hcol : FlipColl σ p q := flipColl_of_le_line hL hp hq hpq
  obtain ⟨hppt, hpL⟩ := hp
  obtain ⟨hqpt, hqL⟩ := hq
  have hline : IsFlipLine σ (p ⊔ q) := hcol.isFlipLine hppt hqpt
  exact Submodule.eq_of_le_of_finrank_eq (sup_le hpL hqL) (by rw [hline.2, hL.2])

theorem exists_compVert_flagGraph_adj_of_finrank_two (hσ : IsUnitaryInvolution σ)
    {U : FlagVert σ 3} (hU : Module.finrank K U.1 = 2) :
    ∃ P : CompVert σ, P.1.1 < U.1 ∧ (flagGraph σ 3).Adj P.1 U := by
  have hline : IsFlipLine σ U.1 := ⟨U.2.1, hU⟩
  obtain ⟨p, hppt, hpL⟩ := exists_mem_ptsOn_of_isFlipLine hσ hline
  obtain ⟨v, rfl, hvq, hvh⟩ := hppt.exists_eq_span
  have hv0 : v ≠ 0 := fun h => hvh (by rw [h]; simp)
  have hpsub : IsFlipflopSub σ (K ∙ v) :=
    (isFlipflopSub_span_singleton_iff hv0).mpr ⟨hvq, hvh⟩
  have hpfin : Module.finrank K (K ∙ v) = 1 := finrank_span_singleton hv0
  have hpne : K ∙ v ≠ ⊥ := by
    intro hbot
    have h := hpfin
    rw [hbot, finrank_bot] at h
    omega
  have hp3 : Module.finrank K (K ∙ v) ≠ 3 := by rw [hpfin]; norm_num
  have hpcv : Module.finrank K (K ∙ v) ≠ 2 := by rw [hpfin]; norm_num
  let P : CompVert σ := ⟨⟨K ∙ v, hpsub, hpne, hp3⟩, hpcv⟩
  have hlt' : (K ∙ v) < U.1 := by
    refine lt_of_le_of_ne hpL ?_
    intro hEq
    rw [hEq, hU] at hpfin
    omega
  have hlt : P.1.1 < U.1 := hlt'
  exact ⟨P, hlt, Or.inl hlt⟩

end CFSG.ClassicalInvolution.PhanDn

end
