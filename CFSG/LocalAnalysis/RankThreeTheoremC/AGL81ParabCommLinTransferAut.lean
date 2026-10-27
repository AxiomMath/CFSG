module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

open CFSG.ComponentClassification.PerfectAutomorphisms CFSG.LocalAnalysis.ComponentInitial
  LinearFlag Matrix

variable {A : Type} [Group A] {Y P : Subgroup A} {n : ℕ} {K : Type} [Field K] {I : Set ℕ}
  (C : LinCover Y P n K I)

@[expose] noncomputable def LinCover.autHom :
    ↥(Subgroup.normalizer (Y : Set A)) →* MulAut (projectiveSL n K) :=
  (MulAut.congr C.e).toMonoidHom.comp ((centerQuotientHom ↥Y).comp Y.normalizerMonoidHom)

theorem LinCover.autHom_apply_proj (b : ↥(Subgroup.normalizer (Y : Set A)))
    (g : SpecialLinearGroup (Fin n) K) :
    C.autHom b (proj n K g) =
      C.e (QuotientGroup.mk (Y.normalizerMonoidHom b (C.σ g))) := by
  have h1 : C.e.symm (proj n K g) = QuotientGroup.mk (C.σ g) :=
    C.e.symm_apply_eq.mpr (C.compat g).symm
  show (MulAut.congr C.e) (centerQuotientHom ↥Y (Y.normalizerMonoidHom b)) (proj n K g) = _
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
  exact congrArg C.e (onCenterQuotient_apply_mk (Y.normalizerMonoidHom b) (C.σ g))

theorem LinCover.autHom_pow_eq_one (b : ↥(Subgroup.normalizer (Y : Set A))) {p k : ℕ}
    (hb : (b : A) ^ p ^ k = 1) : C.autHom b ^ p ^ k = 1 := by
  have h : b ^ p ^ k = 1 := Subtype.ext (by simpa using hb)
  rw [← map_pow, h, map_one]

theorem LinCover.odd_orderOf_autHom (b : ↥(Subgroup.normalizer (Y : Set A))) {p k : ℕ}
    (hp : Odd p) (hb : (b : A) ^ p ^ k = 1) : Odd (orderOf (C.autHom b)) :=
  (hp.pow (n := k)).of_dvd_nat (orderOf_dvd_of_pow_eq_one (C.autHom_pow_eq_one b hb))

theorem LinCover.centralizes_of_autHom_eq_one [Group.IsPerfect ↥Y]
    (c : ↥(Subgroup.normalizer (Y : Set A))) (h : C.autHom c = 1) :
    ∀ y ∈ Y, (c : A) * y = y * c := by
  have h1 : centerQuotientHom ↥Y (Y.normalizerMonoidHom c) = 1 := by
    apply (MulAut.congr C.e).injective
    rw [map_one]
    exact h
  have h2 : Y.normalizerMonoidHom c = 1 := by
    apply centerQuotientHom_injective ↥Y
    rw [h1, map_one]
  intro y hy
  have h3 := congrArg (fun γ : MulAut ↥Y => ((γ ⟨y, hy⟩ : ↥Y) : A)) h2
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h3
  have h4 : (c : A) * y * (c : A)⁻¹ * (c : A) = y * c := by rw [h3]
  simpa using h4

theorem LinCover.map_projFlag (b : ↥(Subgroup.normalizer (Y : Set A)))
    (hbP : (b : A) ∈ Subgroup.normalizer (P : Set A)) :
    (projFlag K n I).map (C.autHom b).toMonoidHom = projFlag K n I := by
  have hbP' : ((b⁻¹ : ↥(Subgroup.normalizer (Y : Set A))) : A) ∈ Subgroup.normalizer (P : Set A) :=
    Subgroup.inv_mem _ hbP
  have key : ∀ (c : ↥(Subgroup.normalizer (Y : Set A))),
      (c : A) ∈ Subgroup.normalizer (P : Set A) → ∀ g ∈ flagStabilizer n K I,
      ∃ g' ∈ flagStabilizer n K I, C.σ g' = Y.normalizerMonoidHom c (C.σ g) := by
    intro c hc g hg
    have hgP : ((C.σ g : ↥Y) : A) ∈ P := (C.mem_flag_iff g).mp hg
    have hy : ((Y.normalizerMonoidHom c (C.σ g) : ↥Y) : A) ∈ P := by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp hc _).mp hgP
    obtain ⟨g', hg'⟩ := C.surjective (Y.normalizerMonoidHom c (C.σ g))
    refine ⟨g', ?_, hg'⟩
    rw [C.mem_flag_iff, hg']
    exact hy
  ext z
  simp only [Subgroup.mem_map, MonoidHom.coe_coe, MulEquiv.toMonoidHom_eq_coe]
  constructor
  · rintro ⟨w, ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨g', hg', h'⟩ := key b hbP g hg
    refine ⟨g', hg', ?_⟩
    rw [C.autHom_apply_proj, ← h', C.compat]
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨g', hg', h'⟩ := key b⁻¹ hbP' g hg
    refine ⟨proj n K g', ⟨g', hg', rfl⟩, ?_⟩
    rw [C.autHom_apply_proj, h', ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      MulAut.one_apply, C.compat]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
