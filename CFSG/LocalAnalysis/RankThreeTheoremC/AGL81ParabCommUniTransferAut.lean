module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniTransferCover
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni

open CFSG.ComponentClassification.PerfectAutomorphisms CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {A : Type} [Group A] {Y P : Subgroup A} {p f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData p f K} {r ε : ℕ} {I : Finset ℕ} (C : UniCover Y P h r ε ↑I)

@[expose] noncomputable def UniCover.autHom :
    ↥(Subgroup.normalizer (Y : Set A)) →* MulAut (hypPSU h r ε) :=
  (MulAut.congr C.e).toMonoidHom.comp ((centerQuotientHom ↥Y).comp Y.normalizerMonoidHom)

theorem UniCover.autHom_apply_proj (b : ↥(Subgroup.normalizer (Y : Set A)))
    (g : hypSU h r ε) :
    C.autHom b (hypProj h r ε g) =
      C.e (QuotientGroup.mk (Y.normalizerMonoidHom b (C.σ g))) := by
  have h1 : C.e.symm (hypProj h r ε g) = QuotientGroup.mk (C.σ g) :=
    C.e.symm_apply_eq.mpr (C.compat g).symm
  show (MulAut.congr C.e) (centerQuotientHom ↥Y (Y.normalizerMonoidHom b))
    (hypProj h r ε g) = _
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
  exact congrArg C.e (onCenterQuotient_apply_mk (Y.normalizerMonoidHom b) (C.σ g))

theorem UniCover.autHom_pow_eq_one (b : ↥(Subgroup.normalizer (Y : Set A))) {q k : ℕ}
    (hb : (b : A) ^ q ^ k = 1) : C.autHom b ^ q ^ k = 1 := by
  have hb' : b ^ q ^ k = 1 := Subtype.ext (by simpa using hb)
  rw [← map_pow, hb', map_one]

theorem UniCover.odd_orderOf_autHom (b : ↥(Subgroup.normalizer (Y : Set A))) {q k : ℕ}
    (hq : Odd q) (hb : (b : A) ^ q ^ k = 1) : Odd (orderOf (C.autHom b)) :=
  (hq.pow (n := k)).of_dvd_nat (orderOf_dvd_of_pow_eq_one (C.autHom_pow_eq_one b hb))

theorem UniCover.centralizes_of_autHom_eq_one [Group.IsPerfect ↥Y]
    (c : ↥(Subgroup.normalizer (Y : Set A))) (hc : C.autHom c = 1) :
    ∀ y ∈ Y, (c : A) * y = y * c := by
  have h1 : centerQuotientHom ↥Y (Y.normalizerMonoidHom c) = 1 := by
    apply (MulAut.congr C.e).injective
    rw [map_one]
    exact hc
  have h2 : Y.normalizerMonoidHom c = 1 := by
    apply centerQuotientHom_injective ↥Y
    rw [h1, map_one]
  intro y hy
  have h3 := congrArg (fun γ : MulAut ↥Y => ((γ ⟨y, hy⟩ : ↥Y) : A)) h2
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h3
  have h4 : (c : A) * y * (c : A)⁻¹ * (c : A) = y * c := by rw [h3]
  simpa using h4

theorem UniCover.mem_flag_iff (g : hypSU h r ε) :
    g ∈ UnitaryHigher.flagStabilizer h r ε ↑I ↔ ((C.σ g : ↥Y) : A) ∈ P := by
  rw [← C.comap_eq]
  rfl

theorem UniCover.map_projFlag (b : ↥(Subgroup.normalizer (Y : Set A)))
    (hbP : (b : A) ∈ Subgroup.normalizer (P : Set A)) :
    (projFlag h r ε I).map (C.autHom b).toMonoidHom = projFlag h r ε I := by
  have hbP' : ((b⁻¹ : ↥(Subgroup.normalizer (Y : Set A))) : A) ∈ Subgroup.normalizer (P : Set A) :=
    Subgroup.inv_mem _ hbP
  have key : ∀ (c : ↥(Subgroup.normalizer (Y : Set A))),
      (c : A) ∈ Subgroup.normalizer (P : Set A) →
      ∀ g ∈ UnitaryHigher.flagStabilizer h r ε ↑I,
      ∃ g' ∈ UnitaryHigher.flagStabilizer h r ε ↑I,
        C.σ g' = Y.normalizerMonoidHom c (C.σ g) := by
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
    refine ⟨hypProj h r ε g', ⟨g', hg', rfl⟩, ?_⟩
    rw [C.autHom_apply_proj, h', ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      MulAut.one_apply, C.compat]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni
