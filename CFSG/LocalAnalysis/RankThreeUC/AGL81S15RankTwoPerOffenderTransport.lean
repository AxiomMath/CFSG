module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderNat

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Matrix

theorem NatSchur.of_range_eq {L L' : Type*} [Group L] [Group L'] {F : Type*} [Field F] {r : ℕ}
    {Mat : L →* Matrix.GeneralLinearGroup (Fin r) F}
    {Mat' : L' →* Matrix.GeneralLinearGroup (Fin r) F} (h : Mat.range = Mat'.range)
    (hS : NatSchur Mat') : NatSchur Mat := by
  intro c hc
  refine hS c ?_
  intro l' u
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp (h.symm ▸ MonoidHom.mem_range.mpr ⟨l', rfl⟩)
  rw [← hl, hc l u]

theorem NatOut.of_range_eq {L L' : Type*} [Group L] [Group L'] {F : Type*} [Field F] {r : ℕ}
    {Mat : L →* Matrix.GeneralLinearGroup (Fin r) F}
    {Mat' : L' →* Matrix.GeneralLinearGroup (Fin r) F} (h : Mat.range = Mat'.range)
    (hO : NatOut Mat') : NatOut Mat := by
  intro M hM hnorm
  have hnorm' : ∀ l' : L', ∃ l'' : L', Mat' l'' = M * Mat' l' * M⁻¹ := by
    intro l'
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp (h.symm ▸ MonoidHom.mem_range.mpr ⟨l', rfl⟩)
    obtain ⟨l₁, hl₁⟩ := hnorm l
    obtain ⟨l'', hl''⟩ := MonoidHom.mem_range.mp (h ▸ MonoidHom.mem_range.mpr ⟨l₁, rfl⟩)
    exact ⟨l'', by rw [hl'', hl₁, hl]⟩
  obtain ⟨l₀', hl₀'⟩ := hO M hM hnorm'
  exact MonoidHom.mem_range.mp (h.symm ▸ MonoidHom.mem_range.mpr ⟨l₀', hl₀'⟩)

theorem PerfStab.of_range_eq {L L' : Type*} [Group L] [Group L'] {F : Type*} [Field F] {r : ℕ}
    {Mat : L →* Matrix.GeneralLinearGroup (Fin r) F} (hinj : Function.Injective Mat)
    {Mat' : L' →* Matrix.GeneralLinearGroup (Fin r) F} (hinj' : Function.Injective Mat')
    (h : Mat.range = Mat'.range) (hP : PerfStab Mat') : PerfStab Mat := by
  intro u
  let φ : L ≃* L' := (MonoidHom.ofInjective hinj).trans
    ((MulEquiv.subgroupCongr h).trans (MonoidHom.ofInjective hinj').symm)
  have hφ : ∀ l : L, Mat' (φ l) = Mat l := by
    intro l
    change Mat' ((MonoidHom.ofInjective hinj').symm
      ((MulEquiv.subgroupCongr h) (MonoidHom.ofInjective hinj l))) = Mat l
    rw [MonoidHom.apply_ofInjective_symm hinj', MulEquiv.subgroupCongr_apply h,
      MonoidHom.ofInjective_apply hinj]
  have hmap : stabL Mat u = (stabL Mat' u).map (φ.symm : L' →* L) := by
    ext l
    constructor
    · intro hl
      have hl' : (Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u = u := hl
      refine ⟨φ l, ?_, φ.symm_apply_apply l⟩
      show (Mat' (φ l) : Matrix (Fin r) (Fin r) F) *ᵥ u = u
      rw [hφ l]
      exact hl'
    · rintro ⟨s, hs, hsl⟩
      have hs' : (Mat' s : Matrix (Fin r) (Fin r) F) *ᵥ u = u := hs
      rw [← hsl]
      show (Mat (φ.symm s) : Matrix (Fin r) (Fin r) F) *ᵥ u = u
      rw [← hφ (φ.symm s), φ.apply_symm_apply]
      exact hs'
  rw [hmap, ← Subgroup.map_commutator, hP u]

end CFSG.LocalAnalysis.RankThreeUC.S15

end
