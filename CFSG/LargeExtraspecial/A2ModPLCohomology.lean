module

public import CFSG.LargeExtraspecial.A2ModCfgSL
public import CFSG.GroupTheory.GLnTwoSplitting.FirstCohomology

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Module Matrix

private noncomputable def contraEquiv {n : ℕ} (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun := contra g
  map_add' := contra_add g
  map_smul' c φ := contra_smul g c φ
  invFun := contra g⁻¹
  left_inv φ := contra_inv_contra g φ
  right_inv φ := contra_contra_inv g φ

private noncomputable def contraHom {n : ℕ} :
    SpecialLinearGroup (Fin n) (ZMod 2) →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) where
  toFun := contraEquiv
  map_one' := LinearEquiv.ext fun φ => contra_one φ
  map_mul' g h := LinearEquiv.ext fun φ => contra_mul g h φ

private theorem contraHom_apply {n : ℕ} (g : SpecialLinearGroup (Fin n) (ZMod 2))
    (φ : Fin n → ZMod 2) : contraHom g φ = contra g φ := rfl

private theorem toLin'_apply' {n : ℕ} (g : SpecialLinearGroup (Fin n) (ZMod 2))
    (x : Fin n → ZMod 2) :
    SpecialLinearGroup.toLin' g x = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x := by
  rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem IsPointMaps.exists_coboundary {Q : QuadraticForm (ZMod 2) V}
    {ρ' : SpecialLinearGroup (Fin 4) (ZMod 2) →* (V ≃ₗ[ZMod 2] V)}
    {P Pd : (Fin 4 → ZMod 2) →ₗ[ZMod 2] V} (hP : IsPointMaps ρ' Q P Pd)
    (htop : LinearMap.range P ⊔ LinearMap.range Pd = ⊤)
    {L : Type*} [Group L] (π : L →* SpecialLinearGroup (Fin 4) (ZMod 2))
    (hπ : Function.Surjective π) (δ : L → V)
    (hδ : ∀ g h, δ (g * h) = δ g + ρ' (π g) (δ h)) (hker : ∀ g, π g = 1 → δ g = 0) :
    ∃ w : V, ∀ g, δ g = ρ' (π g) w + w := by
  classical
  have hinj : Function.Injective (P.coprod Pd) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨n, φ⟩ h
    rw [LinearMap.coprod_apply] at h
    have h1 : P n = Pd φ := by
      have h0 : P n = -Pd φ := eq_neg_of_add_eq_zero_left h
      rw [h0, ZModModule.neg_eq_self]
    have h2 : P n ∈ LinearMap.range P ⊓ LinearMap.range Pd := ⟨⟨n, rfl⟩, ⟨φ, h1.symm⟩⟩
    rw [hP.range_inf_range, Submodule.mem_bot] at h2
    have hn : n = 0 := hP.injective (h2.trans (map_zero P).symm)
    have hφ : φ = 0 := hP.injective_dual (by rw [h1.symm, h2, map_zero])
    simp [hn, hφ]
  have hsurj : Function.Surjective (P.coprod Pd) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_coprod, htop]
  let e : ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) ≃ₗ[ZMod 2] V :=
    LinearEquiv.ofBijective (P.coprod Pd) ⟨hinj, hsurj⟩
  have he : ∀ n φ, e (n, φ) = P n + Pd φ := fun n φ => by
    change (P.coprod Pd) (n, φ) = _
    rw [LinearMap.coprod_apply]
  have hact : ∀ (g : SpecialLinearGroup (Fin 4) (ZMod 2)) (x : (Fin 4 → ZMod 2) ×
      (Fin 4 → ZMod 2)), ρ' g (e x) = e ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x.1,
      contra g x.2) := by
    rintro g ⟨n, φ⟩
    rw [he, he, map_add, hP.map_mulVec, hP.map_contra]
  have hact' : ∀ (g : SpecialLinearGroup (Fin 4) (ZMod 2)) (v : V),
      e.symm (ρ' g v) = ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ (e.symm v).1,
        contra g (e.symm v).2) := by
    intro g v
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, ← hact, LinearEquiv.apply_symm_apply]
  let δ₁ : L → (Fin 4 → ZMod 2) := fun g => (e.symm (δ g)).1
  let δ₂ : L → (Fin 4 → ZMod 2) := fun g => (e.symm (δ g)).2
  let ρ₁ : L →* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
    SpecialLinearGroup.toLin'.comp π
  let ρ₂ : L →* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) := contraHom.comp π
  have hδ₁ : ∀ g h, δ₁ (g * h) = δ₁ g + ρ₁ g (δ₁ h) := by
    intro g h
    have := congrArg (fun x => x.1) (show e.symm (δ (g * h)) = e.symm (δ g) +
      e.symm (ρ' (π g) (δ h)) by rw [hδ, map_add])
    simp only [Prod.fst_add] at this
    rw [hact'] at this
    simpa [δ₁, ρ₁, toLin'_apply'] using this
  have hδ₂ : ∀ g h, δ₂ (g * h) = δ₂ g + ρ₂ g (δ₂ h) := by
    intro g h
    have := congrArg (fun x => x.2) (show e.symm (δ (g * h)) = e.symm (δ g) +
      e.symm (ρ' (π g) (δ h)) by rw [hδ, map_add])
    simp only [Prod.snd_add] at this
    rw [hact'] at this
    simpa [δ₂, ρ₂, contraHom_apply] using this
  have hker₁ : ∀ g, ρ₁ g = 1 → δ₁ g = 0 := by
    intro g hg
    have hπg : π g = 1 := SpecialLinearGroup.toLin'_injective (by simpa [ρ₁] using hg)
    simp [δ₁, hker g hπg]
  have hker₂ : ∀ g, ρ₂ g = 1 → δ₂ g = 0 := by
    intro g hg
    have hπg : π g = 1 := by
      have h1 : ∀ φ : Fin 4 → ZMod 2, contra (π g) φ = φ := fun φ => by
        have := LinearEquiv.congr_fun hg φ
        simpa [ρ₂, contraHom_apply] using this
      have h2 : ((π g)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) = 1 := by
        refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
        have := congrFun (h1 (Pi.single i 1)) j
        rw [contra_def, Matrix.single_vecMul] at this
        change (((π g)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
          i j = (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j
        rw [Matrix.one_apply]
        have h3 : ((π g)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)).1 i j =
            (Pi.single i (1 : ZMod 2) : Fin 4 → ZMod 2) j := by
          simpa [Matrix.row] using this
        rw [h3, Pi.single_apply]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij, Ne.symm hij]
      exact inv_eq_one.mp h2
    simp [δ₂, hker g hπg]
  have hρ₁ : ∀ (f : Dual (ZMod 2) (Fin 4 → ZMod 2)) (d : Fin 4 → ZMod 2) (h : f d = 0),
      ∃ l, ρ₁ l = LinearEquiv.transvection h := by
    intro f d h
    obtain ⟨φ, rfl⟩ := (dotProductEquiv (ZMod 2) (Fin 4)).surjective f
    have hφ : φ ⬝ᵥ d = 0 := by simpa using h
    obtain ⟨l, hl⟩ := hπ (tv d φ)
    refine ⟨l, LinearEquiv.ext fun x => ?_⟩
    simp only [ρ₁, MonoidHom.comp_apply, hl, toLin'_apply', tv_mulVec hφ,
      LinearEquiv.transvection.apply]
    simp
  have hρ₂ : ∀ (f : Dual (ZMod 2) (Fin 4 → ZMod 2)) (d : Fin 4 → ZMod 2) (h : f d = 0),
      ∃ l, ρ₂ l = LinearEquiv.transvection h := by
    intro f d h
    obtain ⟨v, rfl⟩ := (dotProductEquiv (ZMod 2) (Fin 4)).surjective f
    have hv : d ⬝ᵥ v = 0 := by rw [dotProduct_comm]; simpa using h
    obtain ⟨l, hl⟩ := hπ (tv v d)
    refine ⟨l, LinearEquiv.ext fun x => ?_⟩
    simp only [ρ₂, MonoidHom.comp_apply, hl, contraHom_apply, contra_tv hv,
      LinearEquiv.transvection.apply]
    rw [CFSG.GroupTheory.GLnTwoSplitting.two_sub, dotProduct_comm]
    simp
  have h4 : 4 ≤ finrank (ZMod 2) (Fin 4 → ZMod 2) := by rw [Module.finrank_fin_fun]
  obtain ⟨w₁, hw₁⟩ := CFSG.GroupTheory.GLnTwoSplitting.exists_eq_of_isCocycle h4 ρ₁ hρ₁ δ₁
    hδ₁ hker₁
  obtain ⟨w₂, hw₂⟩ := CFSG.GroupTheory.GLnTwoSplitting.exists_eq_of_isCocycle h4 ρ₂ hρ₂ δ₂
    hδ₂ hker₂
  refine ⟨e (w₁, w₂), fun g => ?_⟩
  have h1 : δ g = e (δ₁ g, δ₂ g) := by
    have : e (e.symm (δ g)) = δ g := e.apply_symm_apply _
    exact this.symm
  rw [h1, hact, hw₁ g, hw₂ g]
  have e1 : (δ₁ g, δ₂ g) = (ρ₁ g w₁ + w₁, ρ₂ g w₂ + w₂) := by rw [hw₁ g, hw₂ g]
  rw [← map_add]
  rfl

end CFSG.LargeExtraspecial.A2Mod
