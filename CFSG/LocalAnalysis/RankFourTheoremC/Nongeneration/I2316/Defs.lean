module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316

open CFSG.Open

@[expose] def fixedPts {K : Type*} [Group K] (E : Subgroup (MulAut K)) : Set K :=
  {k : K | ∃ e ∈ E, e ≠ 1 ∧ e k = k}

@[expose] def PlanesGenerate (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 2 →
    ¬ E ≤ (MulAut.conj : K →* MulAut K).range → Subgroup.closure (fixedPts E) = ⊤

section Transport

variable {K L : Type*} [Group K] [Group L]

def transportPlane (ε : K ≃* L) (E : Subgroup (MulAut K)) : Subgroup (MulAut L) :=
  E.map (MulAut.congr ε).toMonoidHom

theorem congr_apply_apply (ε : K ≃* L) (e : MulAut K) (l : L) :
    (MulAut.congr ε e) l = ε (e (ε.symm l)) := rfl

theorem congr_congr_symm (ε : K ≃* L) (e : MulAut L) :
    MulAut.congr ε (MulAut.congr ε.symm e) = e := by
  ext x
  simp [congr_apply_apply]

theorem congr_conj_apply (ε : K ≃* L) (g : K) :
    MulAut.congr ε (MulAut.conj g) = MulAut.conj (ε g) := by
  ext x
  simp [congr_apply_apply]

theorem transportPlane_isElemAbelian {p : ℕ} (ε : K ≃* L) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) : IsElemAbelian p (transportPlane ε E) := by
  refine ⟨?_, ?_⟩
  · have := hE.1
    exact Subgroup.map_isMulCommutative E (MulAut.congr ε).toMonoidHom
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_pow, hE.2 x hx, map_one]

theorem transportPlane_card (ε : K ≃* L) (E : Subgroup (MulAut K)) :
    Nat.card (transportPlane ε E) = Nat.card E :=
  Subgroup.card_map_of_injective (f := (MulAut.congr ε).toMonoidHom)
    (MulAut.congr ε).injective

theorem transportPlane_not_le_inner (ε : K ≃* L) {E : Subgroup (MulAut K)}
    (h : ¬ E ≤ (MulAut.conj : K →* MulAut K).range) :
    ¬ transportPlane ε E ≤ (MulAut.conj : L →* MulAut L).range := by
  intro hle
  apply h
  intro e he
  obtain ⟨g, hg⟩ := hle ⟨e, he, rfl⟩
  refine ⟨ε.symm g, ?_⟩
  have h1 : MulAut.conj (ε (ε.symm g)) = MulAut.congr ε e := by
    rw [ε.apply_symm_apply]; exact hg
  rw [← congr_conj_apply] at h1
  exact (MulAut.congr ε).injective h1

theorem transportPlane_fixedPts (ε : K ≃* L) (E : Subgroup (MulAut K)) :
    fixedPts (transportPlane ε E) = ε '' fixedPts E := by
  ext l
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hne, hl⟩
    refine ⟨ε.symm l, ⟨e, he, ?_, ?_⟩, ε.apply_symm_apply l⟩
    · rintro rfl
      exact hne (map_one _)
    · apply ε.injective
      simpa [congr_apply_apply] using hl
  · rintro ⟨k, ⟨e, he, hne, hk⟩, rfl⟩
    refine ⟨MulAut.congr ε e, ⟨e, he, rfl⟩, ?_, ?_⟩
    · intro h
      exact hne ((MulAut.congr ε).injective (by rw [map_one]; exact h))
    · simp [congr_apply_apply, hk]

theorem planesGenerate_of_mulEquiv {p : ℕ} (ε : K ≃* L) (h : PlanesGenerate p K) :
    PlanesGenerate p L := by
  intro E' hE' hcard hnot
  set E : Subgroup (MulAut K) := transportPlane ε.symm E' with hEdef
  have hE : IsElemAbelian p E := transportPlane_isElemAbelian ε.symm hE'
  have hEc : Nat.card E = p ^ 2 := (transportPlane_card ε.symm E').trans hcard
  have hEn : ¬ E ≤ (MulAut.conj : K →* MulAut K).range :=
    transportPlane_not_le_inner ε.symm hnot
  have hgen := h E hE hEc hEn
  have hback : transportPlane ε E = E' := by
    ext e
    simp only [hEdef, transportPlane, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [congr_congr_symm]
      exact hx
    · intro he
      exact ⟨MulAut.congr ε.symm e, ⟨e, he, rfl⟩, congr_congr_symm ε e⟩
  have hfix : fixedPts E' = ε '' fixedPts E := by
    rw [← hback, transportPlane_fixedPts]
  rw [hfix]
  have hmap := MonoidHom.map_closure ε.toMonoidHom (fixedPts E)
  rw [hgen, Subgroup.map_top_of_surjective _ ε.surjective] at hmap
  exact hmap.symm

end Transport

section Conjugation

variable {K : Type*} [Group K]

def conjPlane (α : MulAut K) (E : Subgroup (MulAut K)) : Subgroup (MulAut K) :=
  E.map (MulAut.conj α).toMonoidHom

theorem mem_conjPlane {α : MulAut K} {E : Subgroup (MulAut K)} {e : MulAut K} :
    e ∈ conjPlane α E ↔ α⁻¹ * e * α ∈ E := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show α⁻¹ * (α * x * α⁻¹) * α = x by group]
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem conjPlane_fixedPts (α : MulAut K) (E : Subgroup (MulAut K)) :
    fixedPts (conjPlane α E) = α '' fixedPts E := by
  ext k
  constructor
  · rintro ⟨e, he, hne, hk⟩
    have hmem := mem_conjPlane.1 he
    refine ⟨α⁻¹ k, ⟨α⁻¹ * e * α, hmem, ?_, ?_⟩, α.apply_symm_apply k⟩
    · intro h1
      apply hne
      have : e = α * (α⁻¹ * e * α) * α⁻¹ := by simp [mul_assoc]
      rw [this, h1]
      simp
    · simp only [MulAut.mul_apply]
      have : e (α (α⁻¹ k)) = k := by simpa using hk
      simpa [MulAut.inv_apply] using congrArg α.symm this
  · rintro ⟨x, ⟨e, he, hne, hx⟩, rfl⟩
    refine ⟨α * e * α⁻¹, mem_conjPlane.2
      (by rwa [show α⁻¹ * (α * e * α⁻¹) * α = e by group]), ?_, ?_⟩
    · intro h1
      apply hne
      have : e = α⁻¹ * (α * e * α⁻¹) * α := by simp [mul_assoc]
      rw [this, h1]
      simp
    · simp [MulAut.mul_apply, hx]

theorem closure_fixedPts_eq_top_of_conj (α : MulAut K) {E : Subgroup (MulAut K)}
    (h : Subgroup.closure (fixedPts (conjPlane α E)) = ⊤) :
    Subgroup.closure (fixedPts E) = ⊤ := by
  rw [conjPlane_fixedPts] at h
  have hmap := MonoidHom.map_closure α.toMonoidHom (fixedPts E)
  have h' : Subgroup.closure (α '' fixedPts E) = ((Subgroup.closure (fixedPts E)).map
      α.toMonoidHom) := hmap.symm
  rw [h'] at h
  have hc := Subgroup.comap_map_eq_self_of_injective (f := α.toMonoidHom) α.injective
    (Subgroup.closure (fixedPts E))
  rw [h, Subgroup.comap_top] at hc
  exact hc.symm

end Conjugation

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316
