module

public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.LieType.SeitzGeneration.UnitaryNonabNonPthAlgebra

public section

namespace CFSG.LieType.SeitzGeneration.NonPth

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

variable {ℓ f n p : ℕ} {K : Type} [Field K]

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem exists_mixing_of_nonpth (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    {x : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n)) {α : K}
    (hx3 : ((x ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hcx : ¬ ∃ μ : K, μ ^ p = α) {S₁ S₂ : Submodule K (Fin n → K)}
    (hS₁ : ∀ s ∈ S₁, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ s ∈ S₁)
    (hS₂ : ∀ s ∈ S₂, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ s ∈ S₂)
    (hdisj : Disjoint S₁ S₂)
    (horth : ∀ s ∈ S₁, ∀ t ∈ S₂, herm (unitaryInvolution K ℓ f) s t = 0)
    (hnd₁ : ((idForm h n).domRestrict₁₂ S₁ S₁).SeparatingLeft)
    (hnd₂ : ((idForm h n).domRestrict₁₂ S₂ S₂).SeparatingLeft)
    (hKI : ∀ w ∈ S₂, w ≠ 0 → ∃ w₀ ∈ S₂, herm (unitaryInvolution K ℓ f) w₀ w₀ = 0 ∧
      herm (unitaryInvolution K ℓ f) w w₀ ≠ 0)
    {u w : Fin n → K} (hu : u ∈ S₁) (hu0 : u ≠ 0) (hw : w ∈ S₂) (hw0 : w ≠ 0) :
    ∃ g : SUid (unitaryInvolution K ℓ f) n,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
        (x : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      ∃ w₀ ∈ S₂, w₀ ≠ 0 ∧ herm (unitaryInvolution K ℓ f) w₀ w₀ = 0 ∧
        ∃ u'' ∈ S₁, ∃ w'' ∈ S₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧ g • w₀ = u'' + w'' := by
  classical
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσ : IsUnitaryInvolution σ := Nonsplit.isUnitaryInvolution h
  set B := idForm h n with hBdef
  have hBsymm : B.IsSymm := idForm_isSymm h n
  set xl : LinearMap.GeneralLinearGroup K (Fin n → K) := Matrix.GeneralLinearGroup.toLin x
    with hxl
  have hxmem : xl ∈ sesqUnitaryGroup B := (toLin_mem_sesqUnitaryGroup_iff x).mpr hx
  have hxend : (xl : Module.End K (Fin n → K)) = Matrix.toLin' (x : Matrix (Fin n) (Fin n) K) :=
    rfl
  have hxlp : (xl : Module.End K (Fin n → K)) ^ p =
      algebraMap K (Module.End K (Fin n → K)) α := by
    have h1 : ((x : Matrix (Fin n) (Fin n) K)) ^ p = α • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hx3
    have h2 := congrArg Matrix.toLinAlgEquiv' h1
    rw [map_pow, map_smul, map_one] at h2
    rw [hxend, Algebra.algebraMap_eq_smul_one]
    exact h2
  have : Nontrivial (Fin n → K) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hu0 (Subsingleton.elim _ _)
  have hmin : minpoly K (xl : Module.End K (Fin n → K)) = X ^ p - C α :=
    minpoly_eq_X_pow_sub_C hp hxlp hcx
  have hirr : Irreducible (X ^ p - C α : K[X]) := irreducible_X_pow_sub_C hp hcx
  have hsq : Squarefree (minpoly K (xl : Module.End K (Fin n → K))) := by
    rw [hmin]; exact hirr.squarefree
  let a : primaryFactors (xl : Module.End K (Fin n → K)) :=
    ⟨X ^ p - C α, by
      rw [mem_primaryFactors]
      exact ⟨hirr, monic_X_pow_sub_C _ hp.ne_zero, by rw [hmin]⟩⟩
  have hdeg : dualPoly h.bar (a : K[X]) = a → 2 ≤ (a : K[X]).natDegree := fun _ => by
    simpa [a, natDegree_X_pow_sub_C] using hp.two_le
  have hcomp : ∀ v : Fin n → K,
      v ∈ primaryComponent (xl : Module.End K (Fin n → K)) (a : K[X]) := by
    intro v
    rw [mem_primaryComponent]
    have h0 : aeval (xl : Module.End K (Fin n → K)) (X ^ p - C α : K[X]) = 0 := by
      simp [hxlp]
    show aeval (xl : Module.End K (Fin n → K)) (X ^ p - C α : K[X]) v = 0
    rw [h0]; rfl
  have hS₁' : ∀ s ∈ S₁, (xl : Module.End K (Fin n → K)) s ∈ S₁ := fun s hs => by
    rw [hxend, Matrix.toLin'_apply]; exact hS₁ s hs
  have hS₂' : ∀ s ∈ S₂, (xl : Module.End K (Fin n → K)) s ∈ S₂ := fun s hs => by
    rw [hxend, Matrix.toLin'_apply]; exact hS₂ s hs
  have horth' : ∀ s ∈ S₁, ∀ t ∈ S₂, B s t = 0 := fun s hs t ht => by
    rw [hBdef, Nonsplit.idForm_eq_herm h]; exact horth s hs t ht
  have hKI' : ∀ w ∈ S₂, w ≠ 0 → ∃ w₀ ∈ S₂, B w₀ w₀ = 0 ∧ B w w₀ ≠ 0 := by
    intro w hw hw0
    obtain ⟨w₀, hw₀, h1, h2⟩ := hKI w hw hw0
    exact ⟨w₀, hw₀, by rw [hBdef, Nonsplit.idForm_eq_herm h]; exact h1,
      by rw [hBdef, Nonsplit.idForm_eq_herm h]; exact h2⟩
  obtain ⟨g, hg, hgdet, w₀, hw₀, hw₀0, hw₀i, u'', hu'', w'', hw'', hu''0, hw''0, hgw⟩ :=
    Mixing.exists_mixing_element (a := a) hBsymm (idForm_separatingLeft h n) hxmem hsq hdeg
      hS₁' hS₂' hdisj horth' hnd₁ hnd₂ hKI' hu (hcomp u) hu0 hw (hcomp w) hw0
  have hgsesq := (mem_unitaryCentralizer.mp hg).1
  have hgcomm := (mem_unitaryCentralizer.mp hg).2
  obtain ⟨gm, hgm⟩ : ∃ gm : GL (Fin n) K, ∀ v, (gm : Matrix (Fin n) (Fin n) K) *ᵥ v =
      (g : Module.End K (Fin n → K)) v := by
    refine ⟨Matrix.GeneralLinearGroup.toLin.symm g, fun v => ?_⟩
    have h1 : (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm g) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) = g := MulEquiv.apply_symm_apply _ g
    have h2 := congrArg (fun φ : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (φ : Module.End K (Fin n → K)) v) h1
    have h3 : ((Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm g) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) v =
        (Matrix.GeneralLinearGroup.toLin.symm g : Matrix (Fin n) (Fin n) K) *ᵥ v :=
      Matrix.GeneralLinearGroup.toLin_apply _ v
    exact h3.symm.trans h2
  have hgend : (g : Module.End K (Fin n → K)) = Matrix.toLin' (gm : Matrix (Fin n) (Fin n) K) :=
    LinearMap.ext fun v => by rw [Matrix.toLin'_apply, hgm]
  let gS : SUid σ n := ⟨gm, (mem_SUid_iff σ).mpr ⟨by
      rw [← LinearMap.det_toLin', ← hgend]; exact hgdet,
    fun v w => by
      rw [hgm, hgm, ← Nonsplit.idForm_eq_herm h, ← Nonsplit.idForm_eq_herm h]
      exact hgsesq v w⟩⟩
  have hgS : ∀ v, gS • v = (g : Module.End K (Fin n → K)) v := fun v => hgm v
  refine ⟨gS, ?_, w₀, hw₀, hw₀0, ?_, u'', hu'', w'', hw'', hu''0, hw''0, ?_⟩
  ·
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
    have := hgcomm.eq
    rw [hgend, hxend] at this
    exact this
  · rw [← Nonsplit.idForm_eq_herm h]; exact hw₀i
  · rw [hgS]; exact hgw

end CFSG.LieType.SeitzGeneration.NonPth
