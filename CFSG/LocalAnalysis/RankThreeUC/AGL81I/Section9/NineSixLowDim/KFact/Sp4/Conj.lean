module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

variable {F : Type} [Field F]

theorem fixSetSp_mono {p : ℕ} {E E' : Subgroup (GL (Fin 2 ⊕ Fin 2) F)} (h : E' ≤ E) :
    fixSetSp p E' ⊆ fixSetSp p E := by
  rintro x ⟨hx, hp, g, hg, hne, hc⟩
  exact ⟨hx, hp, g, h hg, hne, hc⟩

private theorem conj_inv_mem_fixSetSp {p : ℕ} {P : GL (Fin 2 ⊕ Fin 2) F}
    (hP : P ∈ CFSG.Open.StatedSp 2 F) {E : Subgroup (GL (Fin 2 ⊕ Fin 2) F)}
    {x : GL (Fin 2 ⊕ Fin 2) F} (hx : x ∈ fixSetSp p (E.map (MulAut.conj P).toMonoidHom)) :
    P⁻¹ * x * P ∈ fixSetSp p E := by
  obtain ⟨hxS, hpx, _, ⟨g, hg, rfl⟩, hne, hc⟩ := hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hne hc
  refine ⟨mul_mem (mul_mem (inv_mem hP) hxS) hP, ?_, g, hg, ?_, ?_⟩
  · have h := (MulAut.conj P⁻¹).orderOf_eq x
    simp only [MulAut.conj_apply, inv_inv] at h
    rwa [h]
  · rintro rfl
    exact hne (by group)
  · calc g * (P⁻¹ * x * P) = P⁻¹ * ((P * g * P⁻¹) * x) * P := by group
      _ = P⁻¹ * (x * (P * g * P⁻¹)) * P := by rw [hc]
      _ = P⁻¹ * x * P * g := by group

theorem closure_fixSetSp_of_le_conj {p : ℕ} {P : GL (Fin 2 ⊕ Fin 2) F}
    (hP : P ∈ CFSG.Open.StatedSp 2 F) {E E' : Subgroup (GL (Fin 2 ⊕ Fin 2) F)}
    (hle : E' ≤ E.map (MulAut.conj P).toMonoidHom)
    (h : Subgroup.closure (fixSetSp p E') = CFSG.Open.StatedSp 2 F) :
    Subgroup.closure (fixSetSp p E) = CFSG.Open.StatedSp 2 F := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) fun x hx => ?_
  have hx' : P * x * P⁻¹ ∈ Subgroup.closure (fixSetSp p E') := by
    rw [h]
    exact mul_mem (mul_mem hP hx) (inv_mem hP)
  have hmap : Subgroup.closure (fixSetSp p E') ≤
      (Subgroup.closure (fixSetSp p E)).comap (MulAut.conj P⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    have := Subgroup.subset_closure (conj_inv_mem_fixSetSp hP (fixSetSp_mono hle hy))
    simpa using this
  simpa [mul_assoc] using hmap hx'

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
