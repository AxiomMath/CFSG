module

public import CFSG.LinearAlgebra.CoordinateSemilinearMatrixAction
public import CFSG.Quasithin.Background.E2Basic

public section

namespace CFSG.LinearAlgebra.CyclicThreeActionData

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {W : Type*} [CommGroup W]
variable {n : ℕ} {K : Type} [Field K]

@[expose, reducible] def rawH
    (A : Subgroup (MulAut W))
    (ρ : A →* coordinateSemilinearGroup n K)
    (τ : (SemidirectProduct.rightHom.comp ρ).ker →*
      Matrix.GeneralLinearGroup (Fin n) K)
    (Hmat : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) :
    Subgroup (MulAut W) :=
  (Hmat.comap τ).map
    (A.subtype.comp (SemidirectProduct.rightHom.comp ρ).ker.subtype)

theorem rawH_le
    (A : Subgroup (MulAut W))
    (ρ : A →* coordinateSemilinearGroup n K)
    (τ : (SemidirectProduct.rightHom.comp ρ).ker →*
      Matrix.GeneralLinearGroup (Fin n) K)
    (Hmat : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) :
    rawH A ρ τ Hmat ≤ A := by
  rintro g ⟨j, -, rfl⟩
  exact (j : A).2

noncomputable def rawHEquiv
    (A : Subgroup (MulAut W))
    (ρ : A →* coordinateSemilinearGroup n K)
    (τ : (SemidirectProduct.rightHom.comp ρ).ker →*
      Matrix.GeneralLinearGroup (Fin n) K)
    (hτinj : Function.Injective τ)
    (Hmat : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hHrange : Hmat ≤ τ.range) :
    rawH A ρ τ Hmat ≃* Hmat := by
  classical
  let e₁ := Subgroup.equivMapOfInjective (Hmat.comap τ)
    (A.subtype.comp (SemidirectProduct.rightHom.comp ρ).ker.subtype)
    (A.subtype_injective.comp (SemidirectProduct.rightHom.comp ρ).ker.subtype_injective)
  let e₂ := Subgroup.equivMapOfInjective (Hmat.comap τ) τ hτinj
  let e₃ := MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hHrange)
  exact e₁.symm.trans (e₂.trans e₃)

theorem rawH_map_coordinateSemilinearGLAct_eq
    (A : Subgroup (MulAut W))
    (ρ : A →* coordinateSemilinearGroup n K)
    (τ : (SemidirectProduct.rightHom.comp ρ).ker →*
      Matrix.GeneralLinearGroup (Fin n) K)
    (hτ : ∀ j : (SemidirectProduct.rightHom.comp ρ).ker,
      ρ (j : A) = SemidirectProduct.inl (τ j))
    (a : A)
    (Hmat : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) :
    rawH A ρ τ
        (Hmat.map (coordinateSemilinearGLAct n K (ρ a)).toMonoidHom) =
      (rawH A ρ τ Hmat).map (MulAut.conj (a : MulAut W)).toMonoidHom := by
  classical
  let J := (SemidirectProduct.rightHom.comp ρ).ker
  let raw : J →* MulAut W :=
    A.subtype.comp (SemidirectProduct.rightHom.comp ρ).ker.subtype
  have hJn : J.Normal := MonoidHom.normal_ker _
  ext g
  constructor
  · intro hg
    rw [rawH, Subgroup.mem_map] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    rw [Subgroup.mem_comap, Subgroup.mem_map] at hj
    obtain ⟨h, hhH, hhτ⟩ := hj
    let kA : A := a⁻¹ * (j : A) * a
    have hkA : kA ∈ J := by
      have hconj := hJn.conj_mem (j : A) j.property a⁻¹
      simpa [kA, J] using hconj
    let k : J := ⟨kA, hkA⟩
    have hconjA : (j : A) = a * (k : A) * a⁻¹ := by
      change (j : A) = a * (a⁻¹ * (j : A) * a) * a⁻¹
      group
    have hτk : τ j = coordinateSemilinearGLAct n K (ρ a) (τ k) :=
      tau_conj_eq_coordinateSemilinearGLAct n K ρ τ hτ a k j hconjA
    have hhk : h = τ k := by
      apply (coordinateSemilinearGLAct n K (ρ a)).injective
      have hhτ' : (coordinateSemilinearGLAct n K (ρ a)) h = τ j := hhτ
      rw [hhτ', hτk]
    have hkK : τ k ∈ Hmat := by
      rw [← hhk]
      exact hhH
    refine Subgroup.mem_map.mpr ⟨raw k, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨k, Subgroup.mem_comap.mpr hkK, rfl⟩
    · have hconjJ : (⟨a * (k : A) * a⁻¹, by
          have hconj := hJn.conj_mem (k : A) k.property a
          simpa [J] using hconj⟩ : J) = j := Subtype.ext hconjA.symm
      calc (MulAut.conj (a : MulAut W)) (raw k)
          = raw ⟨a * (k : A) * a⁻¹, by
              have hconj := hJn.conj_mem (k : A) k.property a
              simpa [J] using hconj⟩ := by
            simp [raw, MulAut.conj_apply]
        _ = raw j := by rw [hconjJ]
  · intro hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨y, hy, hyg⟩ := hg
    rw [rawH, Subgroup.mem_map] at hy
    obtain ⟨k, hk, hkraw⟩ := hy
    rw [Subgroup.mem_comap] at hk
    let jA : A := a * (k : A) * a⁻¹
    have hjA : jA ∈ J := by
      have hconj := hJn.conj_mem (k : A) k.property a
      simpa [jA, J] using hconj
    let j : J := ⟨jA, hjA⟩
    have hτj : τ j = coordinateSemilinearGLAct n K (ρ a) (τ k) :=
      tau_conj_eq_coordinateSemilinearGLAct n K ρ τ hτ a k j (by
        change jA = a * (k : A) * a⁻¹
        rfl)
    refine Subgroup.mem_map.mpr ⟨j, ?_, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨τ k, hk, ?_⟩
      exact hτj.symm
    · rw [← hyg, ← hkraw]
      simp [j, jA, raw, MulAut.conj_apply]

theorem normal_subgroupOf_rawH
    (A : Subgroup (MulAut W))
    (ρ : A →* coordinateSemilinearGroup n K)
    (τ : (SemidirectProduct.rightHom.comp ρ).ker →*
      Matrix.GeneralLinearGroup (Fin n) K)
    (hτ : ∀ j : (SemidirectProduct.rightHom.comp ρ).ker,
      ρ (j : A) = SemidirectProduct.inl (τ j))
    (Hmat : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hHinv : ∀ a : A,
      Hmat.map (coordinateSemilinearGLAct n K (ρ a)).toMonoidHom = Hmat) :
    ((rawH A ρ τ Hmat).subgroupOf A).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (rawH_le A ρ τ Hmat)).mpr ?_
  intro a ha
  let aA : A := ⟨a, ha⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  calc
    (rawH A ρ τ Hmat).map (MulAut.conj (a : MulAut W)).toMonoidHom
        = rawH A ρ τ (Hmat.map (coordinateSemilinearGLAct n K (ρ aA)).toMonoidHom) :=
          (rawH_map_coordinateSemilinearGLAct_eq A ρ τ hτ aA Hmat).symm
    _ = rawH A ρ τ Hmat := by rw [hHinv aA]

theorem le_rawH_of_map_comap_eq
    (A : Subgroup (MulAut W))
    (ρ : A →* coordinateSemilinearGroup n K)
    (τ : (SemidirectProduct.rightHom.comp ρ).ker →*
      Matrix.GeneralLinearGroup (Fin n) K)
    (Lb : Subgroup (MulAut W))
    (hZraw : (Lb.comap
      (A.subtype.comp (SemidirectProduct.rightHom.comp ρ).ker.subtype)).map
        (A.subtype.comp (SemidirectProduct.rightHom.comp ρ).ker.subtype) = Lb)
    (Hmat : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hZH : ((Lb.comap
      (A.subtype.comp (SemidirectProduct.rightHom.comp ρ).ker.subtype)).map τ) ≤ Hmat) :
    Lb ≤ rawH A ρ τ Hmat := by
  intro l hl
  rw [← hZraw] at hl
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hl
  refine Subgroup.mem_map.mpr ⟨j, Subgroup.mem_comap.mpr ?_, rfl⟩
  exact hZH (Subgroup.mem_map.mpr ⟨j, hj, rfl⟩)

theorem isPOnePlusTwo_of_mulEquiv_rawHEquiv
    (A : Subgroup (MulAut W))
    (ρ : A →* coordinateSemilinearGroup n K)
    (τ : (SemidirectProduct.rightHom.comp ρ).ker →*
      Matrix.GeneralLinearGroup (Fin n) K)
    (hτinj : Function.Injective τ)
    (Hmat : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hHrange : Hmat ≤ τ.range) {p : ℕ}
    (hHshape : CFSG.Quasithin.IsPOnePlusTwo p ↥Hmat) :
    CFSG.Quasithin.IsPOnePlusTwo p ↥(rawH A ρ τ Hmat) :=
  CFSG.Quasithin.isPOnePlusTwo_of_mulEquiv
    (rawHEquiv A ρ τ hτinj Hmat hHrange).symm hHshape

end CFSG.LinearAlgebra.CyclicThreeActionData
