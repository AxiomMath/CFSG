module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix

variable {F : Type} [Field F] {p : ℕ}

theorem fixSetThree_mono {A B : Subgroup (GL (Fin 3) F)} (h : A ≤ B) :
    fixSetThree p A ⊆ fixSetThree p B := by
  rintro x ⟨hdet, hord, g, hg, hgZ, hgx⟩
  exact ⟨hdet, hord, g, h hg, hgZ, hgx⟩

private theorem det_conj (P x : GL (Fin 3) F) :
    ((MulAut.conj P x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det =
      (x : Matrix (Fin 3) (Fin 3) F).det := by
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, det_mul, det_mul, mul_right_comm,
    ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul]

private theorem conj_mem_center_iff (P g : GL (Fin 3) F) :
    MulAut.conj P g ∈ Subgroup.center (GL (Fin 3) F) ↔ g ∈ Subgroup.center (GL (Fin 3) F) := by
  constructor
  · intro h
    have := (Subgroup.center (GL (Fin 3) F)).normal_of_characteristic.conj_mem _ h P⁻¹
    simpa [MulAut.conj_apply, mul_assoc] using this
  · intro h
    exact (Subgroup.center (GL (Fin 3) F)).normal_of_characteristic.conj_mem _ h P

private theorem conj_mem_fixSetThree_iff (P : GL (Fin 3) F) (A : Subgroup (GL (Fin 3) F))
    (x : GL (Fin 3) F) :
    MulAut.conj P x ∈ fixSetThree p (A.map (MulAut.conj P).toMonoidHom) ↔ x ∈ fixSetThree p A := by
  simp only [fixSetThree, Set.mem_setOf_eq, det_conj, MulEquiv.orderOf_eq]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨g', ⟨g, hg, rfl⟩, hgZ, hgx⟩
    refine ⟨g, hg, fun h => hgZ ((conj_mem_center_iff P g).2 h), ?_⟩
    apply (MulAut.conj P).injective
    rw [map_mul, map_mul]
    exact hgx
  · rintro ⟨g, hg, hgZ, hgx⟩
    refine ⟨MulAut.conj P g, ⟨g, hg, rfl⟩, fun h => hgZ ((conj_mem_center_iff P g).1 h), ?_⟩
    simp only [← map_mul, hgx]

private theorem fixSetThree_map_conj (P : GL (Fin 3) F) (A : Subgroup (GL (Fin 3) F)) :
    fixSetThree p (A.map (MulAut.conj P).toMonoidHom) =
      (MulAut.conj P).toMonoidHom '' fixSetThree p A := by
  ext y
  constructor
  · intro hy
    refine ⟨(MulAut.conj P).symm y, ?_, (MulAut.conj P).apply_symm_apply y⟩
    rw [← conj_mem_fixSetThree_iff P, MulEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    exact (conj_mem_fixSetThree_iff P A x).2 hx

theorem closure_fixSetThree_map_conj (P : GL (Fin 3) F) (A : Subgroup (GL (Fin 3) F)) :
    Subgroup.closure (fixSetThree p (A.map (MulAut.conj P).toMonoidHom)) =
      (Subgroup.closure (fixSetThree p A)).map (MulAut.conj P).toMonoidHom := by
  rw [MonoidHom.map_closure, fixSetThree_map_conj]

theorem statedSL_map_conj (P : GL (Fin 3) F) :
    (CFSG.Open.StatedSL 3 F).map (MulAut.conj P).toMonoidHom = CFSG.Open.StatedSL 3 F := by
  rw [CFSG.Open.StatedSL, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (det_conj P x).trans hx
  · intro hy
    refine ⟨(MulAut.conj P).symm y, ?_, (MulAut.conj P).apply_symm_apply y⟩
    have := det_conj P ((MulAut.conj P).symm y)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm.trans hy

theorem closure_fixSetThree_le (A : Subgroup (GL (Fin 3) F)) :
    Subgroup.closure (fixSetThree p A) ≤ CFSG.Open.StatedSL 3 F :=
  Subgroup.closure_mono fun _ hx => hx.1

private theorem map_conj_center (P : GL (Fin 3) F) :
    (Subgroup.center (GL (Fin 3) F)).map (MulAut.conj P).toMonoidHom =
      Subgroup.center (GL (Fin 3) F) :=
  Subgroup.map_center_eq (MulAut.conj P)

theorem IsElemModScalars.map_conj {A : Subgroup (GL (Fin 3) F)} (hA : IsElemModScalars p A)
    (P : GL (Fin 3) F) : IsElemModScalars p (A.map (MulAut.conj P).toMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_conj_center P]
    exact Subgroup.map_mono hA.center_le
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow]
    exact (conj_mem_center_iff P _).2 (hA.pow_mem g hg)
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    simp only [← map_mul, ← map_inv]
    exact (conj_mem_center_iff P _).2 (hA.commutator_mem g hg h hh)
  · have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj P).toMonoidHom)
      (Subgroup.center (GL (Fin 3) F)) A (MulAut.conj P).injective
    rw [map_conj_center] at h
    rw [← hA.card_eq]
    exact h

theorem closure_fixSetThree_eq_of_le_conj {A A' : Subgroup (GL (Fin 3) F)} (P : GL (Fin 3) F)
    (hle : A' ≤ A.map (MulAut.conj P).toMonoidHom)
    (h : Subgroup.closure (fixSetThree p A') = CFSG.Open.StatedSL 3 F) :
    Subgroup.closure (fixSetThree p A) = CFSG.Open.StatedSL 3 F := by
  refine le_antisymm (closure_fixSetThree_le A) ?_
  have h1 : CFSG.Open.StatedSL 3 F ≤
      (Subgroup.closure (fixSetThree p A)).map (MulAut.conj P).toMonoidHom := by
    rw [← h, ← closure_fixSetThree_map_conj]
    exact Subgroup.closure_mono (fixSetThree_mono hle)
  intro x hx
  have hx' : MulAut.conj P x ∈ CFSG.Open.StatedSL 3 F := by
    rw [← statedSL_map_conj P]
    exact ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := h1 hx'
  rwa [(MulAut.conj P).injective hyx] at hy

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
