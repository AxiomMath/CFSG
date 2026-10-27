module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.ClassicalInvolution.Models.Transfer.Unitary
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Chart

public section

namespace CFSG.ClassicalInvolution.RouteD.SU4Pattern

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open scoped MatrixGroups

section NatChart

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem trace_blockMat_zero (M : Matrix (Fin 2) (Fin 2) K) :
    (blockMat 4 0 M).trace = M.trace + 2 := by
  simp [Matrix.trace, Fin.sum_univ_four, blockMat_apply, Fin.sum_univ_two]
  ring

theorem exists_natChart (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {F : Type} [Field F]
    (ε : F ≃+* fixedSubfield K p f) :
    ∃ ν : SL(2, F) →* Su K p f 4, Function.Injective ν ∧
      ν.range = rootSU2 K p f (by norm_num : 2 ≤ 4) ∧
      ∀ s : SL(2, F), (suMat (ν s)).trace =
        2 + ((ε ((s : Matrix (Fin 2) (Fin 2) F) 0 0 + (s : Matrix (Fin 2) (Fin 2) F) 1 1) :
          fixedSubfield K p f) : K) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨μ, hμ⟩ := exists_norm_eq_neg_one hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  set Ψ := psiEquiv hζ0 hζ h2 hμ with hΨ
  have hμ0 : μ ≠ 0 := ne_zero_of_norm_neg_one _ hμ
  let E : SL(2, F) →* SL(2, fixedSubfield K p f) :=
    Matrix.SpecialLinearGroup.map (ε : F →+* fixedSubfield K p f)
  have hEinj : Function.Injective E := by
    intro A B h
    ext i j
    have := congrArg (fun M : SL(2, fixedSubfield K p f) =>
      (M : Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)) i j) h
    simpa [E] using this
  have hEsurj : Function.Surjective E := by
    intro B
    refine ⟨Matrix.SpecialLinearGroup.map (ε.symm : fixedSubfield K p f →+* F) B, ?_⟩
    ext i j
    simp [E]
  refine ⟨(blockEmb K p f 4 2 0 (by omega)).comp (Ψ.toMonoidHom.comp E), ?_, ?_, ?_⟩
  · exact (blockEmb_injective (by omega)).comp (Ψ.injective.comp hEinj)
  · have h1 : (Ψ.toMonoidHom.comp E).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (Ψ.surjective.comp hEsurj)
    rw [MonoidHom.range_comp, h1, ← MonoidHom.range_eq_map]
    rfl
  · intro s
    show (blockMat 4 0 (suMat (Ψ (E s)))).trace = _
    rw [trace_blockMat_zero, hΨ, suMat_psiEquiv]
    have e1 : (wittMat μ * hypMat ζ (E s : Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)) *
        wittMatInv μ).trace =
        (hypMat ζ (E s : Matrix (Fin 2) (Fin 2) (fixedSubfield K p f))).trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, wittMatInv_mul h2 hμ0, Matrix.one_mul]
    rw [e1]
    simp [hypMat, Matrix.trace, Fin.sum_univ_two, E, add_comm]

end NatChart

section ChartLift

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem trace_conj {L : Type*} [CommRing L] {n : ℕ} (G Gi M : Matrix (Fin n) (Fin n) L)
    (h : Gi * G = 1) : (G * M * Gi).trace = M.trace := by
  rw [Matrix.trace_mul_cycle, h, Matrix.one_mul]

theorem exists_chart_lift (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {F : Type} [Field F] [Finite F] (ε : F ≃+* fixedSubfield K p f) {X : Type} [Group X]
    (ψ : Su K p f 4 →* X) (hker : ψ.ker ≤ Subgroup.center (Su K p f 4))
    (θ : SL(2, F) →* X) (hθ : θ.range = (rootSU2 K p f (by norm_num : 2 ≤ 4)).map ψ)
    (ρ : X ≃* X) (d : Fˣ) (hθρ : ∀ s, ρ (θ s) = θ (diagConj2 d 1 s))
    (α : Su K p f 4 →* Su K p f 4) (g : GL (Fin 4) K) (φ : K ≃+* K)
    (hα : ∀ x, ψ (α x) = ρ (ψ x))
    (hmat : ∀ x, ((α x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (g : Matrix (Fin 4) (Fin 4) K) *
        φ.mapMatrix ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    ∃ θ' : SL(2, F) →* Su K p f 4, Function.Injective θ' ∧
      θ'.range = rootSU2 K p f (by norm_num : 2 ≤ 4) ∧ (∀ s, ψ (θ' s) = θ s) ∧
      (∀ s, α (θ' s) = θ' (diagConj2 d 1 s)) ∧ ∀ y ∈ fixedSubfield K p f, φ y = y := by
  classical
  have hn : (2 : ℕ) ≤ 4 := by norm_num
  have hcardF : Nat.card F = p ^ f := by
    rw [Nat.card_congr ε.toEquiv, card_fixedSubfield hK]
  have h4F : 4 ≤ Nat.card F := by rw [hcardF]; omega
  have : Group.IsPerfect SL(2, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4F
  obtain ⟨ν, hνinj, hνrange, hνtr⟩ := exists_natChart hK hp2 ε
  set R : Subgroup (Su K p f 4) := rootSU2 K p f hn with hR
  have hRlong : IsLongRootSU2 K p f hn R (rootInvSU K p f hn) := isLongRootSU2_standard hn
  have hker1 : ∀ z ∈ R, z ∈ ψ.ker → z = 1 :=
    Transfer.eq_one_of_mem_ker_of_isLongRootSU2 hK hp2 hq (by norm_num : 3 ≤ 4) hRlong hker
  have hinjR : ∀ a ∈ R, ∀ b ∈ R, ψ a = ψ b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    exact inv_mul_eq_one.mp (hker1 _ (R.mul_mem (R.inv_mem ha) hb) h1)
  have hνR : ∀ s, ν s ∈ R := fun s => hνrange ▸ ⟨s, rfl⟩
  set θ₂ : SL(2, F) →* X := ψ.comp ν with hθ₂
  have hθ₂inj : Function.Injective θ₂ := by
    intro s t hst
    exact hνinj (hinjR _ (hνR s) _ (hνR t) hst)
  have hθ₂range : θ₂.range = θ.range := by
    rw [hθ, hθ₂, MonoidHom.range_comp, hνrange]
  have hex : ∀ s : SL(2, F), ∃ s' : SL(2, F), θ₂ s' = θ s := fun s => by
    have : θ s ∈ θ₂.range := hθ₂range ▸ ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := this
    exact ⟨s', hs'⟩
  choose γf hγf using hex
  let γ0 : SL(2, F) →* SL(2, F) :=
    { toFun := γf
      map_one' := hθ₂inj (by rw [hγf, map_one, map_one])
      map_mul' := fun s t => hθ₂inj (by rw [hγf, map_mul, map_mul, hγf, hγf]) }
  have hγsurj : Function.Surjective γ0 := fun t => by
    have : θ₂ t ∈ θ.range := hθ₂range ▸ ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := this
    exact ⟨s, hθ₂inj (by show θ₂ (γf s) = θ₂ t; rw [hγf]; exact hs)⟩
  have hγinj : Function.Injective γ0 := Finite.injective_iff_surjective.2 hγsurj
  let γ : SL(2, F) ≃* SL(2, F) := MulEquiv.ofBijective γ0 ⟨hγinj, hγsurj⟩
  have hγθ : ∀ s, θ₂ (γ0 s) = θ s := hγf
  set θ' : SL(2, F) →* Su K p f 4 := ν.comp γ0 with hθ'
  have hθ'ψ : ∀ s, ψ (θ' s) = θ s := fun s => hγθ s
  have hθ'inj : Function.Injective θ' := hνinj.comp hγinj
  have hθ'range : θ'.range = R := by
    rw [hθ', MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hγsurj, Subgroup.map_top, hνrange]
  have hequiv : ∀ s, α (θ' s) = θ' (diagConj2 d 1 s) := by
    have key := hom_eq_of_central_ker_perfect (G := SL(2, F)) (θ := ψ) hker
      (α.comp θ') (θ'.comp (diagConj2 d 1).toMonoidHom) (fun s => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [hα, hθ'ψ, hθ'ψ, hθρ])
    exact fun s => DFunLike.congr_fun key s
  refine ⟨θ', hθ'inj, hθ'range, hθ'ψ, hequiv, ?_⟩
  obtain ⟨G, κ, hG⟩ := CFSG.ClassicalInvolution.Phan.exists_toGL_eq_conj_map γ
  have hγtr : ∀ s : SL(2, F), ((γ0 s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 +
      ((γ0 s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      κ ((s : Matrix (Fin 2) (Fin 2) F) 0 0 + (s : Matrix (Fin 2) (Fin 2) F) 1 1) := by
    intro s
    have h1 := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F)) (hG s)
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h1
    have h2 : ((γ s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = (γ0 s : SL(2, F)) := rfl
    rw [h2] at h1
    have h3 := congrArg Matrix.trace h1
    rw [trace_conj _ _ _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])] at h3
    simpa [Matrix.trace, Fin.sum_univ_two] using h3
  have hθ'tr : ∀ s : SL(2, F), (suMat (θ' s)).trace =
      2 + ((ε (κ ((s : Matrix (Fin 2) (Fin 2) F) 0 0 +
        (s : Matrix (Fin 2) (Fin 2) F) 1 1)) : fixedSubfield K p f) : K) := by
    intro s
    show (suMat (ν (γ0 s))).trace = _
    rw [hνtr, hγtr]
  have hcond : ∀ t : F, φ ((ε (κ t) : fixedSubfield K p f) : K) =
      ((ε (κ t) : fixedSubfield K p f) : K) := by
    intro t
    set s : SL(2, F) := ⟨!![t, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩ with hs
    have hdt : (((diagConj2 d 1 s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 0 0 +
        (((diagConj2 d 1 s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 1 1 = t := by
      rw [coe_diagConj2]
      have hd0 : (d : F) ≠ 0 := d.ne_zero
      simp [hs, Matrix.mul_apply, Matrix.diagonal_apply]
      field_simp
    have e1 := hθ'tr (diagConj2 d 1 s)
    rw [hdt] at e1
    have e2 : (suMat (α (θ' s))).trace = φ ((suMat (θ' s)).trace) := by
      show (((α (θ' s) : Su K p f 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = _
      rw [hmat, trace_conj _ _ _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])]
      show (φ.mapMatrix (suMat (θ' s))).trace = _
      simp [Matrix.trace, map_sum]
    have e3 := hθ'tr s
    have hst : ((s : Matrix (Fin 2) (Fin 2) F) 0 0 + (s : Matrix (Fin 2) (Fin 2) F) 1 1) = t := by
      simp [hs]
    rw [hst] at e3
    rw [hequiv s, e1, e3, map_add, map_ofNat] at e2
    linear_combination -e2
  intro y hy
  obtain ⟨t, ht⟩ : ∃ t : F, ε (κ t) = ⟨y, hy⟩ :=
    ⟨κ.symm (ε.symm ⟨y, hy⟩), by simp⟩
  have := hcond t
  rw [ht] at this
  exact this

end ChartLift

end CFSG.ClassicalInvolution.RouteD.SU4Pattern
