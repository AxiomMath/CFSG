module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisGen

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Module CFSG.RankThree.PartOne.KCLinPlane

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_mixing_of_homog [FiniteDimensional K V] {ι : Type*} (f : ι → Module.End K V)
    (hidem : ∀ i v, f i (f i v) = f i v) (horth : ∀ i j, i ≠ j → ∀ v, f i (f j v) = 0)
    (hdim : ∀ i, 2 ≤ finrank K (LinearMap.range (f i))) {G : Subgroup (V ≃ₗ[K] V)}
    (hsupp : ∀ i, suppGroup (f i) ≤ G) {r s j : ι} (hjr : j ≠ r) (hjs : j ≠ s) (hrs : r ≠ s)
    {x : V ≃ₗ[K] V} (hx : x ∈ G) {β : Module.End K V} (hxβ : ∀ v, x v = v + β v)
    (hββ : ∀ v, β (β v) = 0) (hβ1 : ∀ v, f r (β (f j v)) = β (f j v))
    (hβ2 : ∀ v, f j (β v) = f j (β (f s v))) {a : V} (ha : f j a = a) {α : Module.Dual K V}
    (hα : ∀ v, α (f j v) = α v) (hαa : α a = 0) (hβa : β a ≠ 0) (hαβ : ∃ u, α (β u) ≠ 0) :
    ∃ w, f r w = w ∧ w ≠ 0 ∧ ∃ φ : Module.Dual K V, (∀ v, φ (f s v) = φ v) ∧ φ ≠ 0 ∧
      IsTv G w φ := by
  have hT0 : IsTv G a α := (isTv_suppGroup ha hα hαa).mono (hsupp j)
  have hT1 := hT0.conj hx
  have hxa : x a = a + β a := hxβ a
  have hsymm : ∀ v, x.symm v = v - β v := by
    intro v
    rw [LinearEquiv.symm_apply_eq, hxβ, map_sub, hββ]
    simp
  set φ1 : Module.Dual K V := α - α.comp β with hφ1
  have e1 : α.comp (x.symm : V →ₗ[K] V) = φ1 := by
    ext v
    simp [hsymm, hφ1]
  rw [e1, hxa] at hT1
  have hfja : ∀ i, i ≠ j → f i a = 0 := fun i hi => by
    have := horth i j hi a
    rwa [ha] at this
  have hβa_r : f r (β a) = β a := by
    have := hβ1 a
    rwa [ha] at this
  have hfs_βa : f s (β a) = 0 := by
    conv_lhs => rw [← hβa_r]
    exact horth s r hrs.symm _
  have hfs_w1 : f s (a + β a) = 0 := by
    rw [map_add, hfja s hjs.symm, hfs_βa, add_zero]
  have hαfs : ∀ v, α (f s v) = 0 := fun v => by
    rw [← hα, horth j s hjs v, map_zero]
  have hαβfs : ∀ v, α (β (f s v)) = α (β v) := fun v => by
    rw [← hα (β (f s v)), ← hβ2, hα]
  have hφ1fs : ∀ v, φ1 (f s v) = -α (β v) := fun v => by
    simp [hφ1, hαfs, hαβfs]
  obtain ⟨u, hu⟩ := hαβ
  set a' : V := f s u with ha'def
  have ha' : f s a' = a' := hidem s u
  have hφ1a' : φ1 a' ≠ 0 := by
    rw [ha'def, hφ1fs]
    exact neg_ne_zero.2 hu
  have ha'0 : a' ≠ 0 := fun h => hφ1a' (by rw [h, map_zero])
  obtain ⟨x', hx'f, hx'⟩ := exists_block_indep (hidem s) (hdim s) a'
  obtain ⟨l, hl1, hl2, hl3⟩ := exists_block_dual (hidem s) ha' hx'f hx'
  have hT2 := hT1.peel_fun (hsupp s) hfs_w1 ha' hl1 hl2
  set φ2 : Module.Dual K V := (φ1 a') • l with hφ2
  have hφ2s : ∀ v, φ2 (f s v) = φ2 v := fun v => by simp [hφ2, hl1]
  have hφ20 : φ2 ≠ 0 := by
    intro h
    have : φ2 x' = 0 := by rw [h]; rfl
    simp only [hφ2, LinearMap.smul_apply, smul_eq_mul] at this
    exact (mul_ne_zero hφ1a' hl3) this
  have hφ2r : ∀ v, φ2 (f r v) = 0 := fun v => by
    have : l (f r v) = 0 := by
      rw [← hl1, horth s r hrs.symm, map_zero]
    simp [hφ2, this]
  obtain ⟨l0, hl0⟩ := Module.Projective.exists_dual_ne_zero K hβa
  set l'' : Module.Dual K V := l0.comp (f r) with hl''def
  have hl'' : ∀ v, l'' (f r v) = l'' v := fun v => by
    simp [hl''def, hidem r v]
  have hl''βa : l'' (β a) = l0 (β a) := by
    simp [hl''def, hβa_r]
  have hl''ne : l'' (β a) ≠ 0 := by rw [hl''βa]; exact hl0
  obtain ⟨x'', hx''f, hx''⟩ := exists_block_indep (hidem r) (hdim r) (β a)
  set a'' : V := x'' - (l'' x'' / l'' (β a)) • β a with ha''def
  have ha''f : f r a'' = a'' := by
    rw [ha''def, map_sub, map_smul, hx''f, hβa_r]
  have hl''a'' : l'' a'' = 0 := by
    rw [ha''def, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hl''ne, sub_self]
  have ha''0 : a'' ≠ 0 := by
    intro h
    apply hx''
    have : x'' = (l'' x'' / l'' (β a)) • β a := sub_eq_zero.1 h
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hT3 := hT2.peel_dir (hsupp r) hφ2r ha''f hl'' hl''a''
  have hc : l'' (a + β a) ≠ 0 := by
    have : l'' (a + β a) = l0 (β a) := by
      rw [map_add, hl''βa]
      have : l'' a = 0 := by simp [hl''def, hfja r hjr.symm]
      rw [this, zero_add]
    rw [this]; exact hl0
  refine ⟨(l'' (a + β a)) • a'', ?_, smul_ne_zero hc ha''0, φ2, hφ2s, hφ20, hT3⟩
  rw [map_smul, ha''f]

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
