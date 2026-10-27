module

public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.LieType.SeitzGeneration.UnitaryNonCubeAlgebra

public section

namespace CFSG.LieType.SeitzGeneration.NonCube

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem isCenter_of_eigen_matrix {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c)
    {H : Subgroup (SUid σ n)} {Y : Matrix (Fin n) (Fin n) K}
    (hH : ∀ g : SUid σ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y =
      Y * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H)
    (hY : ∀ u w, herm σ (Y *ᵥ u) (Y *ᵥ w) = herm σ u w)
    {v : Fin n → K} (hv : herm σ v v = 0) {l : K} (hl : σ l * l = 1) (hYv : Y *ᵥ v = l • v) :
    Centers.IsCenter H v := by
  refine ⟨hv, fun c hc => ⟨tv hσ hv hc, hH _ ?_, tv_smul hσ hv hc⟩⟩
  have hT : ∀ w, ((tv hσ hv hc : SUid σ n) : GL (Fin n) K) *ᵥ w = w + (c * herm σ v w) • v :=
    fun w => tv_smul hσ hv hc w
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  set u : Fin n → K := Pi.single i 1
  have h1 : herm σ v (Y *ᵥ u) = l * herm σ v u := by
    have h := hY v u
    rw [hYv, herm_smul_left] at h
    calc herm σ v (Y *ᵥ u) = l * (σ l * herm σ v (Y *ᵥ u)) := by
          linear_combination (-(herm σ v (Y *ᵥ u))) * hl
      _ = l * herm σ v u := by rw [h]
  rw [hT, hT, Matrix.mulVec_add, Matrix.mulVec_smul, hYv, h1, smul_smul]
  congr 2
  ring


variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem exists_mixing_of_noncube (h : UnitaryFieldData ℓ f K)
    {x : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n)) {α : K}
    (hx3 : ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hcx : ¬ ∃ μ : K, μ ^ 3 = α) {S₁ S₂ : Submodule K (Fin n → K)}
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
  have hxend : (xl : Module.End K (Fin n → K)) = Matrix.toLin' (x : Matrix (Fin n) (Fin n) K) := rfl
  have hxl3 : (xl : Module.End K (Fin n → K)) ^ 3 =
      algebraMap K (Module.End K (Fin n → K)) α := by
    have h1 : ((x : Matrix (Fin n) (Fin n) K)) ^ 3 = α • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hx3
    have h2 := congrArg Matrix.toLinAlgEquiv' h1
    rw [map_pow, map_smul, map_one] at h2
    rw [hxend, Algebra.algebraMap_eq_smul_one]
    exact h2
  have : Nontrivial (Fin n → K) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hu0 (Subsingleton.elim _ _)
  have hmin : minpoly K (xl : Module.End K (Fin n → K)) = X ^ 3 - C α :=
    minpoly_eq_X_pow_three_sub_C hxl3 hcx
  have hirr : Irreducible (X ^ 3 - C α : K[X]) := irreducible_X_pow_three_sub_C hcx
  have hsq : Squarefree (minpoly K (xl : Module.End K (Fin n → K))) := by
    rw [hmin]; exact hirr.squarefree
  let a : primaryFactors (xl : Module.End K (Fin n → K)) :=
    ⟨X ^ 3 - C α, by
      rw [mem_primaryFactors]
      exact ⟨hirr, monic_X_pow_sub_C _ (by norm_num), by rw [hmin]⟩⟩
  have hdeg : dualPoly h.bar (a : K[X]) = a → 2 ≤ (a : K[X]).natDegree := fun _ => by
    simp [a, natDegree_X_pow_sub_C]
  have hcomp : ∀ v : Fin n → K,
      v ∈ primaryComponent (xl : Module.End K (Fin n → K)) (a : K[X]) := by
    intro v
    rw [mem_primaryComponent]
    have h0 : aeval (xl : Module.End K (Fin n → K)) (X ^ 3 - C α : K[X]) = 0 := by
      simp [hxl3]
    show aeval (xl : Module.End K (Fin n → K)) (X ^ 3 - C α : K[X]) v = 0
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


end CFSG.LieType.SeitzGeneration.NonCube
