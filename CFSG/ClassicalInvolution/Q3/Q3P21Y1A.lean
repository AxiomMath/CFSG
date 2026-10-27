module

public import CFSG.ClassicalInvolution.Q3.Q3P21Y1S
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1M
public import CFSG.ClassicalInvolution.Q3.Q3T6AutConj
public import CFSG.ClassicalInvolution.Q3.Q3URTransfer
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSU

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.RouteD.SU4Pattern
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Generic

theorem exists_aut_of_stab {G X : Type} [Group G] [Finite G] [Group X] (ι : G →* X)
    (hι : Function.Injective ι) (τ : X ≃* X) (h : ∀ g, τ (ι g) ∈ ι.range) :
    ∃ δ : G ≃* G, ∀ g, ι (δ g) = τ (ι g) := by
  classical
  choose δ₀ hδ₀ using h
  let δ : G →* G :=
    { toFun := δ₀
      map_one' := hι (by simp [hδ₀])
      map_mul' := fun a b => hι (by simp [hδ₀]) }
  have hinj : Function.Injective δ := fun a b hab => by
    apply hι
    apply τ.injective
    rw [← hδ₀, ← hδ₀]
    exact congrArg ι hab
  exact ⟨MulEquiv.ofBijective δ ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩,
    fun g => hδ₀ g⟩

theorem exists_inner_of_det_one (g : GL (Fin 2) (ZMod 3))
    (hg : Matrix.GeneralLinearGroup.det g = 1) :
    ∃ s : SL(2, ZMod 3), ∀ b : SL(2, ZMod 3), Q3T6.conjSL g b = s * b * s⁻¹ := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
    have := congrArg Units.val hg
    simpa using this
  obtain ⟨s, rfl⟩ : ∃ s : SL(2, ZMod 3), Matrix.SpecialLinearGroup.toGL s = g :=
    ⟨⟨(g : Matrix (Fin 2) (Fin 2) (ZMod 3)), hdet⟩, Units.ext rfl⟩
  refine ⟨s, fun b => ?_⟩
  apply Subtype.ext
  rw [Q3T6.coe_conjSL, ← map_inv]
  rfl

theorem aut_outer_mul_inner {G : Type} [Group G] (E : G ≃* SL(2, ZMod 3)) (α β : MulAut G)
    (hα : ¬ ∃ h : G, ∀ x, α x = h * x * h⁻¹) (hβ : ¬ ∃ h : G, ∀ x, β x = h * x * h⁻¹) :
    ∃ h : G, ∀ x, α x = h * β x * h⁻¹ := by
  set α' : MulAut SL(2, ZMod 3) := E.symm.trans (α.trans E) with hα'
  set β' : MulAut SL(2, ZMod 3) := E.symm.trans (β.trans E) with hβ'
  obtain ⟨gα, hgα⟩ := Q3T6.sl2Three_aut_eq_conj α'
  obtain ⟨gβ, hgβ⟩ := Q3T6.sl2Three_aut_eq_conj β'
  have hα'eq : ∀ b, α' b = Q3T6.conjSL gα b := fun b => Subtype.ext (hgα b)
  have hβ'eq : ∀ b, β' b = Q3T6.conjSL gβ b := fun b => Subtype.ext (hgβ b)
  have hunits : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1 := by decide
  have hout : ∀ (γ : MulAut G) (g : GL (Fin 2) (ZMod 3)),
      (∀ b, (E.symm.trans (γ.trans E)) b = Q3T6.conjSL g b) →
      (¬ ∃ h : G, ∀ x, γ x = h * x * h⁻¹) → Matrix.GeneralLinearGroup.det g = -1 := by
    intro γ g hg hnot
    rcases hunits (Matrix.GeneralLinearGroup.det g) with h | h
    · exfalso
      obtain ⟨s, hs⟩ := exists_inner_of_det_one g h
      apply hnot
      refine ⟨E.symm s, fun x => ?_⟩
      apply E.injective
      have h1 := hg (E x)
      rw [hs] at h1
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact h1
    · exact h
  have hdα := hout α gα hα'eq hα
  have hdβ := hout β gβ hβ'eq hβ
  have hdet : Matrix.GeneralLinearGroup.det (gα * gβ⁻¹) = 1 := by
    rw [map_mul, map_inv, hdα, hdβ]
    decide
  obtain ⟨s, hs⟩ := exists_inner_of_det_one _ hdet
  refine ⟨E.symm s, fun x => ?_⟩
  apply E.injective
  have e1 := hα'eq (E x)
  have e2 : (Q3T6.conjSL gα) (E x) =
      (Q3T6.conjSL (gα * gβ⁻¹)) ((Q3T6.conjSL gβ) (E x)) := by
    rw [← MonoidHom.comp_apply, ← Q3T6.conjSL_mul, mul_assoc, inv_mul_cancel, mul_one]
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  simp only [hα', MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at e1
  rw [e1, e2, hs]
  simp only [hβ', MulEquiv.trans_apply] at hβ'eq
  rw [← hβ'eq]
  simp

end Generic

section Ad

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem det_conjTr_two (σ : K ≃+* K) (M : Matrix (Fin 2) (Fin 2) K) :
    (conjTr σ M).det = σ M.det := by
  show ((M.map σ)ᵀ).det = σ M.det
  rw [Matrix.det_transpose]
  exact (RingHom.map_det (σ : K →+* K) M).symm

omit [Finite K] in
theorem conjTr_conjTr_of_invol {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) : conjTr σ (conjTr σ M) = M := by
  ext i j
  simp [conjTr, hσ]

@[expose] noncomputable def adHom
    (hσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c)
    (y : Matrix (Fin 2) (Fin 2) K) (hy : conjTr (unitaryInvolution K p f) y * y = 1) :
    Su K p f 2 →* Su K p f 2 :=
  letI σ := unitaryInvolution K p f
  have hy' : y * conjTr σ y = 1 := mul_eq_one_comm.mp hy
  have hdy : σ y.det * y.det = 1 := by
    have := congrArg Matrix.det hy
    rwa [Matrix.det_mul, det_conjTr_two, Matrix.det_one] at this
  have hdet : ∀ b : Su K p f 2, (y * suMat b * conjTr σ y).det = 1 := fun b => by
    have hb : (suMat b).det = 1 := b.2.1
    rw [Matrix.det_mul, Matrix.det_mul, hb, det_conjTr_two, mul_one, mul_comm, hdy]
  have hiso : ∀ b : Su K p f 2,
      conjTr σ (y * suMat b * conjTr σ y) * (y * suMat b * conjTr σ y) = 1 := fun b => by
    have hb : conjTr σ (suMat b) * suMat b = 1 := b.2.2
    rw [conjTr_mul, conjTr_mul, conjTr_conjTr_of_invol hσ]
    calc y * (conjTr σ (suMat b) * conjTr σ y) * (y * suMat b * conjTr σ y)
        = y * conjTr σ (suMat b) * (conjTr σ y * y) * suMat b * conjTr σ y := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hy, Matrix.mul_one, Matrix.mul_assoc y, hb, Matrix.mul_one, hy']
  { toFun := fun b => Models.mkSU K p f (y * suMat b * conjTr σ y) (hdet b) (hiso b)
    map_one' := suMat_injective (by
      rw [suMat_mkSU, suMat_one, Matrix.mul_one, hy'])
    map_mul' := fun b c => suMat_injective (by
      rw [suMat_mkSU, suMat_mul, suMat_mul, suMat_mkSU, suMat_mkSU]
      calc y * (suMat b * suMat c) * conjTr σ y
          = y * suMat b * (conjTr σ y * y) * suMat c * conjTr σ y := by
            rw [hy, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]) }

theorem suMat_adHom (hσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c)
    (y : Matrix (Fin 2) (Fin 2) K) (hy : conjTr (unitaryInvolution K p f) y * y = 1)
    (b : Su K p f 2) :
    suMat (adHom hσ y hy b) = y * suMat b * conjTr (unitaryInvolution K p f) y := rfl

end Ad

section Outer

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem adHom_injective (hσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c)
    (y : Matrix (Fin 2) (Fin 2) K) (hy : conjTr (unitaryInvolution K p f) y * y = 1) :
    Function.Injective (adHom hσ y hy) := by
  intro b c h
  have e := congrArg suMat h
  rw [suMat_adHom, suMat_adHom] at e
  apply suMat_injective
  have hy' : y * conjTr (unitaryInvolution K p f) y = 1 := mul_eq_one_comm.mp hy
  calc suMat b = (conjTr (unitaryInvolution K p f) y * y) * suMat b *
        (conjTr (unitaryInvolution K p f) y * y) := by rw [hy]; simp
    _ = conjTr (unitaryInvolution K p f) y * (y * suMat b * conjTr (unitaryInvolution K p f) y) *
        y := by simp only [Matrix.mul_assoc]
    _ = conjTr (unitaryInvolution K p f) y * (y * suMat c * conjTr (unitaryInvolution K p f) y) *
        y := by rw [e]
    _ = (conjTr (unitaryInvolution K p f) y * y) * suMat c *
        (conjTr (unitaryInvolution K p f) y * y) := by simp only [Matrix.mul_assoc]
    _ = suMat c := by rw [hy]; simp

@[expose] noncomputable def adSU2
    (hσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c)
    (y : Matrix (Fin 2) (Fin 2) K) (hy : conjTr (unitaryInvolution K p f) y * y = 1) :
    MulAut (Su K p f 2) :=
  MulEquiv.ofBijective (adHom hσ y hy)
    ⟨adHom_injective hσ y hy, Finite.injective_iff_surjective.mp (adHom_injective hσ y hy)⟩

theorem suMat_adSU2 (hσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c)
    (y : Matrix (Fin 2) (Fin 2) K) (hy : conjTr (unitaryInvolution K p f) y * y = 1)
    (b : Su K p f 2) :
    suMat (adSU2 hσ y hy b) = y * suMat b * conjTr (unitaryInvolution K p f) y := rfl

theorem y0_unitary {ι : K} (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = -ι) :
    conjTr (unitaryInvolution K p f) (!![1, 0; 0, ι] : Matrix (Fin 2) (Fin 2) K) *
      !![1, 0; 0, ι] = 1 := by
  set σ := unitaryInvolution K p f with hσ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, hσι]
  linear_combination (-1 : K) * hι

theorem adSU2_y0_outer (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hqq : p ^ f = 3)
    (hq3 : p ^ f % 4 = 3) {ι : K} (hι : ι * ι = -1)
    (hσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c)
    (hy0 : conjTr (unitaryInvolution K p f) (!![1, 0; 0, ι] : Matrix (Fin 2) (Fin 2) K) *
      !![1, 0; 0, ι] = 1) :
    ¬ ∃ h : Su K p f 2, ∀ x, adSU2 hσ (!![1, 0; 0, ι]) hy0 x = h * x * h⁻¹ := by
  rintro ⟨h, hh⟩
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  set y0 : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, ι] with hy0def
  have hC : ∀ x : Su K p f 2, (suMat h⁻¹ * y0) * suMat x = suMat x * (suMat h⁻¹ * y0) := by
    intro x
    have e := congrArg suMat (hh x)
    rw [suMat_adSU2, suMat_mul, suMat_mul] at e
    have e2 : y0 * suMat x = suMat h * suMat x * suMat h⁻¹ * y0 := by
      calc y0 * suMat x
          = y0 * suMat x * (conjTr (unitaryInvolution K p f) y0 * y0) := by
            rw [hy0, Matrix.mul_one]
        _ = (y0 * suMat x * conjTr (unitaryInvolution K p f) y0) * y0 := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [e]
    calc suMat h⁻¹ * y0 * suMat x = suMat h⁻¹ * (y0 * suMat x) := by rw [Matrix.mul_assoc]
      _ = suMat h⁻¹ * (suMat h * suMat x * suMat h⁻¹ * y0) := by rw [e2]
      _ = (suMat h⁻¹ * suMat h) * suMat x * (suMat h⁻¹ * y0) := by simp only [Matrix.mul_assoc]
      _ = suMat x * (suMat h⁻¹ * y0) := by rw [suMat_inv_mul_suMat, Matrix.one_mul]
  obtain ⟨c, hc⟩ := su2_commutant_scalar hK hp2 hq3 hC
  have hy0c : y0 = c • suMat h := by
    calc y0 = (suMat h * suMat h⁻¹) * y0 := by rw [suMat_mul_suMat_inv, Matrix.one_mul]
      _ = suMat h * (suMat h⁻¹ * y0) := by rw [Matrix.mul_assoc]
      _ = c • suMat h := by rw [hc, Matrix.mul_smul, Matrix.mul_one]
  have hdet : ι = c * c := by
    have h1 : y0.det = ι := by
      rw [hy0def, det_fin_two_of]
      ring
    have h2' : (c • suMat h).det = c * c := by
      rw [Matrix.det_smul, show (suMat h).det = 1 from h.2.1]
      simp [pow_two]
    rw [← h1, hy0c, h2']
  have hnorm : unitaryInvolution K p f c * c = 1 := by
    have e := congrFun (congrFun hy0 0) 0
    rw [hy0c, conjTr_smul_aux, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at e
    have hh1 : conjTr (unitaryInvolution K p f) (suMat h) * suMat h = 1 := h.2.2
    rw [hh1] at e
    simpa using e
  have hc4 : c ^ 4 = 1 := by
    rw [unitaryInvolution_apply, hqq] at hnorm
    linear_combination hnorm
  apply h2
  have : ι * ι = 1 := by
    rw [hdet]
    linear_combination hc4
  linear_combination hι - this

end Outer

section Block

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem block_y (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hqq : p ^ f = 3)
    (hq3 : p ^ f % 4 = 3) {ι : K} (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = -ι)
    {X : Type} [Group X] (ψ : Su K p f 4 →* X) (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x)
    {i : ℕ} (hi : i + 2 ≤ 4)
    (hinj : ∀ l : Su K p f 2, blockEmb K p f 4 2 i hi l ∈ ψ.ker → l = 1)
    (θ : SL(2, GaloisField 3 1) →* X)
    (hθ : θ.range = (blockEmb K p f 4 2 i hi).range.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) :
    ∃ y₁ : Matrix (Fin 2) (Fin 2) K, conjTr (unitaryInvolution K p f) y₁ * y₁ = 1 ∧
      y₁.det = ι ∧ (∃ z : K, y₁ * y₁ = z • 1 ∧ z ^ 4 = 1) ∧
      ∀ l : Su K p f 2, ∃ l' : Su K p f 2,
        suMat l' = y₁ * suMat l * conjTr (unitaryInvolution K p f) y₁ ∧
          τ (ψ (blockEmb K p f 4 2 i hi l)) = ψ (blockEmb K p f 4 2 i hi l') := by
  classical
  have hσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c :=
    unitaryInvolution_involutive hK
  set σ := unitaryInvolution K p f with hσdef
  set ιi : Su K p f 2 →* X := ψ.comp (blockEmb K p f 4 2 i hi) with hιi
  have hιinj : Function.Injective ιi := by
    rw [injective_iff_map_eq_one]
    intro l hl
    exact hinj l hl
  have hrange : ιi.range = θ.range := by
    rw [hθ, hιi, MonoidHom.range_comp]
  have hstab : ∀ l, τ (ιi l) ∈ ιi.range := by
    intro l
    have h1 : ιi l ∈ θ.range := hrange ▸ ⟨l, rfl⟩
    obtain ⟨s, hs⟩ := h1
    have h2 : τ (ιi l) ∈ θ.range := by
      rw [← hs, hθτ]
      exact ⟨_, rfl⟩
    rwa [← hrange] at h2
  obtain ⟨δ, hδ⟩ := exists_aut_of_stab ιi hιinj τ hstab
  have hδδ : ∀ l, δ (δ l) = l := fun l => hιinj (by rw [hδ, hδ, hτ])
  have hθmem : ∀ s, ∃ l, ιi l = θ s := fun s => by
    have : θ s ∈ ιi.range := hrange ▸ ⟨s, rfl⟩
    exact this
  choose θ₁ hθ₁ using hθmem
  let θ₁h : SL(2, GaloisField 3 1) →* Su K p f 2 :=
    { toFun := θ₁
      map_one' := hιinj (by rw [hθ₁, map_one, map_one])
      map_mul' := fun a b => hιinj (by rw [hθ₁, map_mul, map_mul, hθ₁, hθ₁]) }
  have hθ₁surj : Function.Surjective θ₁h := fun l => by
    have : ιi l ∈ θ.range := hrange ▸ ⟨l, rfl⟩
    obtain ⟨s, hs⟩ := this
    exact ⟨s, hιinj (by show ιi (θ₁ s) = ιi l; rw [hθ₁, hs])⟩
  obtain ⟨E⟩ := exists_su2_equiv_sl2 hK hp2 hqq
  have hcard3 : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  obtain ⟨ε⟩ := Q3W.nonempty_ringEquiv_zmod_three (K := GaloisField 3 1) hcard3
  have hθ₁inj : Function.Injective θ₁h :=
    (Finite.injective_iff_surjective_of_equiv
      ((Q3W.slEquiv ε 2).trans E.symm).toEquiv).mpr hθ₁surj
  have hθ₁δ : ∀ s, θ₁h (diagConj2 (-1) 1 s) = δ (θ₁h s) := fun s =>
    hιinj (by
      show ιi (θ₁ (diagConj2 (-1) 1 s)) = ιi (δ (θ₁ s))
      rw [hθ₁, hδ, hθ₁, hθτ])
  have hF3 : Nat.card (GaloisField 3 1) % 4 = 3 := by rw [hcard3]
  have houter : ¬ ∃ h : Su K p f 2, ∀ x, δ x = h * x * h⁻¹ := by
    rintro ⟨h, hh⟩
    obtain ⟨s₀, hs₀⟩ := hθ₁surj h
    apply not_inner_diagConj2 (F := GaloisField 3 1) hF3
    refine ⟨s₀, fun s => hθ₁inj ?_⟩
    rw [hθ₁δ, hh, map_mul, map_mul, map_inv, hs₀]
  have hy0 := y0_unitary (p := p) (f := f) hι hσι
  obtain ⟨h, hh⟩ := aut_outer_mul_inner E δ (adSU2 hσ (!![1, 0; 0, ι]) hy0) houter
    (adSU2_y0_outer hK hp2 hqq hq3 hι hσ hy0)
  set y0 : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, ι] with hy0def
  set H : Matrix (Fin 2) (Fin 2) K := suMat h with hH
  have hHiso : conjTr σ H * H = 1 := h.2.2
  have hHinv : suMat h⁻¹ = conjTr σ H := (conjTr_suMat_eq_inv h).symm
  have hy0det : y0.det = ι := by
    rw [hy0def, det_fin_two_of]
    ring
  have hY : conjTr σ (H * y0) * (H * y0) = 1 := by
    rw [conjTr_mul]
    calc conjTr σ y0 * conjTr σ H * (H * y0) = conjTr σ y0 * (conjTr σ H * H) * y0 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hHiso, Matrix.mul_one, hy0]
  have hact : ∀ x : Su K p f 2,
      suMat (δ x) = (H * y0) * suMat x * conjTr σ (H * y0) := by
    intro x
    rw [hh x, suMat_mul, suMat_mul, suMat_adSU2, hHinv, conjTr_mul]
    simp only [Matrix.mul_assoc]
    rfl
  have hsq : conjTr σ ((H * y0) * (H * y0)) * ((H * y0) * (H * y0)) = 1 := by
    rw [conjTr_mul]
    calc conjTr σ (H * y0) * conjTr σ (H * y0) * (H * y0 * (H * y0))
        = conjTr σ (H * y0) * (conjTr σ (H * y0) * (H * y0)) * (H * y0) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hY, Matrix.mul_one, hY]
  have hcomm : ∀ x : Su K p f 2,
      ((H * y0) * (H * y0)) * suMat x = suMat x * ((H * y0) * (H * y0)) := by
    intro x
    have e := congrArg suMat (hδδ x)
    rw [hact (δ x), hact x] at e
    calc (H * y0) * (H * y0) * suMat x
        = (H * y0) * (H * y0) * suMat x * (conjTr σ (H * y0) * conjTr σ (H * y0) *
            ((H * y0) * (H * y0))) := by
          rw [show conjTr σ (H * y0) * conjTr σ (H * y0) * ((H * y0) * (H * y0)) = 1 by
            rw [← conjTr_mul]; exact hsq, Matrix.mul_one]
      _ = ((H * y0) * ((H * y0) * suMat x * conjTr σ (H * y0)) * conjTr σ (H * y0)) *
            ((H * y0) * (H * y0)) := by
          simp only [Matrix.mul_assoc]
      _ = suMat x * ((H * y0) * (H * y0)) := by rw [e]
  obtain ⟨z, hz⟩ := su2_commutant_scalar hK hp2 hq3 hcomm
  refine ⟨H * y0, hY, ?_, ⟨z, hz, ?_⟩, fun l => ⟨δ l, hact l, (hδ l).symm⟩⟩
  · rw [Matrix.det_mul, show H.det = 1 from h.2.1, hy0det, one_mul]
  · rw [hz, conjTr_smul_aux, conjTr_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul] at hsq
    have e := congrFun (congrFun hsq 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e
    rw [hσdef, unitaryInvolution_apply, hqq] at e
    linear_combination e

end Block

section Main

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem BD_smul_pow (a b : K) (n : ℕ) :
    (BD (a • (1 : Matrix (Fin 2) (Fin 2) K)) (b • 1)) ^ n =
      BD ((a ^ n) • (1 : Matrix (Fin 2) (Fin 2) K)) ((b ^ n) • 1) := by
  induction n with
  | zero => simp [BD_one]
  | succ n ih =>
    rw [pow_succ, ih, BD_mul]
    congr 1 <;> simp [pow_succ, smul_smul, mul_comm]

theorem block_inj_of_central (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hqq : p ^ f = 3)
    {i : ℕ} (hi : i + 2 ≤ 4) (hi' : i = 0 ∨ i = 2) {l : Su K p f 2}
    (hl : blockEmb K p f 4 2 i hi l ∈ Subgroup.center (Su K p f 4)) : l = 1 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hqq
    · exact h
  obtain ⟨μ, hμ⟩ := ModelFacts.TG3.exists_smul_one_of_mem_center hK hp2 hf (by norm_num : 3 ≤ 4) hl
  rw [suMat_blockEmb] at hμ
  have hμ1 : μ = 1 := by
    rcases hi' with rfl | rfl
    · have e := congrFun (congrFun hμ 3) 3
      simpa [blockMat_apply] using e.symm
    · have e := congrFun (congrFun hμ 0) 0
      simpa [blockMat_apply] using e.symm
  rw [hμ1, one_smul] at hμ
  apply blockEmb_injective hi
  apply suMat_injective
  rw [suMat_blockEmb, hμ, map_one, suMat_one]

end Main

section Final

theorem y1a : Y1aStmt := by
  intro X _ ψ hker τ hτ θ₀ θ₂ hθ₀ hθ₂ hθτ₀ hθτ₂
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := Q3W.card_gf9
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hqq : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hq3 : (3 : ℕ) ^ 1 % 4 = 3 := by norm_num
  have h2 : (2 : GaloisField 3 (2 * 1)) ≠ 0 :=
    CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  obtain ⟨ι, hι, hσι⟩ := exists_sqrt_neg_one_three hK hq3
  set σ := unitaryInvolution (GaloisField 3 (2 * 1)) 3 1 with hσdef
  obtain ⟨y₁, hu₁, hd₁, ⟨z₁, hz₁, hz₁4⟩, hact₁⟩ := block_y hK hp2 hqq hq3 hι hσι ψ τ hτ
    (i := 0) (by norm_num)
    (fun l hl => block_inj_of_central hK hp2 hqq (by norm_num) (Or.inl rfl) (hker hl)) θ₀ hθ₀
    hθτ₀
  obtain ⟨y₂, hu₂, hd₂, ⟨z₂, hz₂, hz₂4⟩, hact₂⟩ := block_y hK hp2 hqq hq3 hι hσι ψ τ hτ
    (i := 2) (by norm_num)
    (fun l hl => block_inj_of_central hK hp2 hqq (by norm_num) (Or.inr rfl) (hker hl)) θ₂ hθ₂
    hθτ₂
  set y₃ : Matrix (Fin 2) (Fin 2) (GaloisField 3 (2 * 1)) := ι • y₂ with hy₃
  have hιι : σ ι * ι = 1 := by rw [hσι]; linear_combination (-1 : GaloisField 3 (2 * 1)) * hι
  have hu₃ : conjTr σ y₃ * y₃ = 1 := by
    rw [hy₃, conjTr_smul_aux, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hu₂, hιι, one_smul]
  have hu₃' : y₃ * conjTr σ y₃ = 1 := mul_eq_one_comm.mp hu₃
  have hu₁' : y₁ * conjTr σ y₁ = 1 := mul_eq_one_comm.mp hu₁
  have hd₃ : y₃.det = -ι := by
    rw [hy₃, Matrix.det_smul, hd₂]
    simp only [Fintype.card_fin]
    linear_combination ι * hι
  have hz₃ : y₃ * y₃ = (-z₂) • 1 := by
    rw [hy₃, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz₂, smul_smul]
    congr 1
    linear_combination z₂ * hι
  have hdetY : (BD y₁ y₃).det = 1 := by
    rw [det_BD, hd₁, hd₃]
    linear_combination (-1 : GaloisField 3 (2 * 1)) * hι
  have hisoY : conjTr σ (BD y₁ y₃) * BD y₁ y₃ = 1 := by
    rw [conjTr_BD, BD_mul, hu₁, hu₃, BD_one]
  set y : Su (GaloisField 3 (2 * 1)) 3 1 4 :=
    Models.mkSU (GaloisField 3 (2 * 1)) 3 1 (BD y₁ y₃) hdetY hisoY with hy
  have hsy : suMat y = BD y₁ y₃ := suMat_mkSU hdetY hisoY
  have hsyi : suMat y⁻¹ = BD (conjTr σ y₁) (conjTr σ y₃) := by
    rw [← conjTr_suMat_eq_inv, hsy, conjTr_BD]
  refine ⟨y₁, y₃, y, hsy, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply suMat_injective
    have hpow : suMat (y ^ 8) = (BD y₁ y₃) ^ 8 := by
      have := map_pow (suMatHom (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) (n := 4)) y 8
      rw [← hsy]
      exact this
    have h8 : (BD y₁ y₃) ^ 8 = 1 := by
      have hY2 : BD y₁ y₃ * BD y₁ y₃ = BD (z₁ • 1) ((-z₂) • 1) := by
        rw [BD_mul, hz₁, hz₃]
      calc (BD y₁ y₃) ^ 8 = (BD y₁ y₃ * BD y₁ y₃) ^ 4 := by rw [← pow_two, ← pow_mul]
        _ = BD ((z₁ ^ 4) • 1) (((-z₂) ^ 4) • 1) := by rw [hY2, BD_smul_pow]
        _ = 1 := by
          rw [hz₁4, show (-z₂) ^ 4 = z₂ ^ 4 by ring, hz₂4, one_smul, BD_one]
    rw [hpow, h8, suMat_one]
  ·
    intro b hb
    obtain ⟨l, rfl⟩ := hb
    obtain ⟨l', hl', hψ⟩ := hact₁ l
    rw [hψ]
    congr 1
    apply suMat_injective
    rw [suMat_mul, suMat_mul, hsy, hsyi, suMat_blockEmb, suMat_blockEmb, blockMat_zero_eq_BD,
      blockMat_zero_eq_BD, BD_mul, BD_mul, hl', Matrix.mul_one, hu₃']
  ·
    intro b hb
    obtain ⟨l, rfl⟩ := hb
    obtain ⟨l', hl', hψ⟩ := hact₂ l
    rw [hψ]
    congr 1
    apply suMat_injective
    have hl3 : y₃ * suMat l * conjTr σ y₃ = suMat l' := by
      rw [hl', hy₃, conjTr_smul_aux, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        hσι, show ι * -ι = 1 by linear_combination (-1 : GaloisField 3 (2 * 1)) * hι, one_smul]
    rw [suMat_mul, suMat_mul, hsy, hsyi, suMat_blockEmb, suMat_blockEmb, blockMat_two_eq_BD,
      blockMat_two_eq_BD, BD_mul, BD_mul, hl3, Matrix.mul_one, hu₁']
  · rw [hd₁]
    intro h
    apply h2
    linear_combination hι - (ι + 1) * h
  · rw [hd₁]
    intro h
    apply h2
    linear_combination hι - (ι - 1) * h

end Final

end CFSG.ClassicalInvolution.Q3.Q3P21
