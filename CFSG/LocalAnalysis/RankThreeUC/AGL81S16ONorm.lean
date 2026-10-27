module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONormB

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal Matrix CFSG.Open
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  coe_quadMinus)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem omega_semilinear (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (α : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) ≃+ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (h2 : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∃ g' ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
        α.symm ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          x) =
          (g' : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
            α.symm x) :
    ∃ θ : F →+* F, ∀ (r : F) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F),
      α (r • x) = θ r • α x := by
  have hβ : ∀ r : F, ∃ μ : F, ∀ x, α (r • α.symm x) = μ • x := by
    intro r
    refine omega_commutant hirr ((α.toAddMonoidHom).comp
      ((AddMonoidHom.mk' (fun x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F => r • x)
        (fun a b => smul_add r a b)).comp α.symm.toAddMonoidHom)) ?_
    intro g hg x
    obtain ⟨g', hg', hg'x⟩ := h2 g hg
    have h3 : ∀ y, α ((g' : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y) =
        (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          α y := by
      intro y
      have := hg'x (α y)
      rw [AddEquiv.symm_apply_apply] at this
      rw [← this, AddEquiv.apply_symm_apply]
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddMonoidHom.mk'_apply]
    rw [hg'x x, ← Matrix.mulVec_smul, h3]
  choose μ hμ using hβ
  have hsm : ∀ r y, α (r • y) = μ r • α y := by
    intro r y
    have := hμ r (α y)
    rwa [AddEquiv.symm_apply_apply] at this
  have key : ∀ a b : F, (∀ y, a • α y = b • α y) → a = b := by
    intro a b h
    have := congrFun (h (α.symm (Pi.single (Sum.inl idx0) 1))) (Sum.inl idx0)
    simpa using this
  refine ⟨{ toFun := μ
            map_one' := key _ _ (fun y => by rw [← hsm, one_smul, one_smul])
            map_zero' := key _ _ (fun y => by rw [← hsm, zero_smul, zero_smul, map_zero])
            map_mul' := fun r s => key _ _ (fun y => by
              rw [← hsm, mul_smul, hsm, hsm, mul_smul])
            map_add' := fun r s => key _ _ (fun y => by
              rw [← hsm, add_smul, map_add, hsm, hsm, add_smul]) }, hsm⟩

theorem commutator_le_orthogonalGroup_self {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) :
    ⁅orthogonalGroup Q, orthogonalGroup Q⁆ ≤ orthogonalGroup Q := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)

theorem quadMinus_mulVec_of_mem_statedOmega
    {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hg : g ∈ StatedOmega (StatedQuadMinus 3 F b c)) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :
    quadMinus 3 F b c
      ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x)
        = quadMinus 3 F b c x := by
  have h := commutator_le_orthogonalGroup_self _ ((mem_statedOmega_iff g).mp hg)
  have := map_of_mem h x
  rwa [toLinEquiv_apply] at this

theorem polar_mulVec_of_mem_statedOmega
    {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hg : g ∈ StatedOmega (StatedQuadMinus 3 F b c))
    (x y : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :
    polar (quadMinus 3 F b c)
      ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x)
      ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y)
        = polar (quadMinus 3 F b c) x y := by
  have h := commutator_le_orthogonalGroup_self _ ((mem_statedOmega_iff g).mp hg)
  have := polar_map_of_mem h x y
  rwa [toLinEquiv_apply, toLinEquiv_apply] at this

theorem omega_similitude_of_normalizes (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)
    (hN : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∃ g' ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
        A *ᵥ ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          F) *ᵥ x) =
          (g' : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
            (A *ᵥ x)) :
    ∃ μ : F, ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      StatedQuadMinus 3 F b c (A *ᵥ x) = μ * StatedQuadMinus 3 F b c x := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hcoe : ⇑(quadMinus 3 F b c) = StatedQuadMinus 3 F b c := coe_quadMinus 3 F b c
  set Q := quadMinus 3 F b c with hQdef
  have hinv : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∀ x y : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      polar Q (A *ᵥ ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x))
        (A *ᵥ ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y)) = polar Q (A *ᵥ x) (A *ᵥ y) := by
    intro g hg x y
    obtain ⟨g', hg', hgx⟩ := hN g hg
    rw [hgx x, hgx y]
    exact polar_mulVec_of_mem_statedOmega hg' _ _
  let AL : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) →ₗ[F] (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :=
    Matrix.mulVecLin A
  let B' : LinearMap.BilinForm F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :=
    (polarBilin Q).compl₁₂ AL AL
  let T := B'.symmCompOfNondegenerate (polarBilin Q) hQ
  have hT : ∀ x y, polar Q (T x) y = polar Q (A *ᵥ x) (A *ᵥ y) := by
    intro x y
    have h := LinearMap.BilinForm.symmCompOfNondegenerate_left_apply B' hQ y x
    rw [polarBilin_apply_apply] at h
    exact h.trans (by simp [B', AL, polarBilin_apply_apply])
  have hTcomm : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      T ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
        (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          T x := by
    intro g hg x
    have key : ∀ z, polar Q (T ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) -
          (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
            T x) z = 0 := by
      intro z
      obtain ⟨y, rfl⟩ : ∃ y, (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y = z :=
        ⟨((g⁻¹ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ z, by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.one_mulVec]⟩
      rw [polar_sub_left, hT, hinv g hg x y, polar_mulVec_of_mem_statedOmega hg, hT, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_polar_eq_zero hQ key)
  obtain ⟨μ, hμ⟩ := omega_commutant hirr T.toAddMonoidHom hTcomm
  have hscal : ∀ x y, polar Q (A *ᵥ x) (A *ᵥ y) = μ * polar Q x y := by
    intro x y
    rw [← hT]
    have := hμ x
    simp only [LinearMap.toAddMonoidHom_coe] at this
    rw [this, polar_smul_left_eq]
  set R : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) → F := fun x => Q (A *ᵥ x) - μ * Q x with hRdef
  have hRadd : ∀ x y, R (x + y) = R x + R y := by
    intro x y
    simp only [hRdef]
    rw [Matrix.mulVec_add, QuadraticMap.map_add Q (A *ᵥ x) (A *ᵥ y), QuadraticMap.map_add Q x y,
      hscal x y]
    ring
  have hR0 : R 0 = 0 := by simp [hRdef]
  have hRinv : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      R ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
        R x := by
    intro g hg x
    obtain ⟨g', hg', hgx⟩ := hN g hg
    simp only [hRdef]
    rw [hgx x, quadMinus_mulVec_of_mem_statedOmega hg', quadMinus_mulVec_of_mem_statedOmega hg]
  have hRe0 : R (Pi.single (Sum.inl idx0) 1) = 0 := by
    obtain ⟨E, hE, hEx⟩ := eichler_mem_statedOmega hirr (Pi.single (Sum.inl idx1) 1)
      (Pi.single (Sum.inl idx0) 1)
    have h1 := hRinv E hE (Pi.single (Sum.inr (Sum.inl idx1)) 1)
    rw [hEx, eichler_e1_e0_f1, hRadd] at h1
    linear_combination h1
  have hRs : ∀ s, Q s = 0 → R s = 0 := by
    intro s hs
    by_cases hs0 : s = 0
    · rw [hs0]
      exact hR0
    obtain ⟨g, hg, hge⟩ := exists_statedOmega_apply_e0 hirr hs hs0
    rw [← hge, hRinv g hg]
    exact hRe0
  let S : AddSubgroup (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :=
    { carrier := {x | R x = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [hRadd, hx, hy, add_zero]
      zero_mem' := hR0
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        have := hRadd x (-x)
        rw [add_neg_cancel, hR0, hx, zero_add] at this
        exact this.symm }
  have hQA : ∀ x, Q (A *ᵥ x) = μ * Q x := fun x => by
    have := mem_of_forall_singular_mem S hRs x
    exact sub_eq_zero.mp this
  refine ⟨μ, fun x => ?_⟩
  rw [← hcoe]
  exact hQA x

theorem omega_isometry_of_normalizes (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)
    (hAA : A * A = 1)
    (hN : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∃ g' ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
        A *ᵥ ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          F) *ᵥ x) =
          (g' : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
            (A *ᵥ x)) :
    ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      StatedQuadMinus 3 F b c (A *ᵥ x) = StatedQuadMinus 3 F b c x := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hcoe : ⇑(quadMinus 3 F b c) = StatedQuadMinus 3 F b c := coe_quadMinus 3 F b c
  obtain ⟨μ, hQA⟩ := omega_similitude_of_normalizes hirr A hN
  obtain ⟨a, ha⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
  have ha' : StatedQuadMinus 3 F b c a ≠ 0 := by rw [← hcoe]; exact ha
  have hAAx : ∀ x, A *ᵥ (A *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hμ2 : μ * μ = 1 := by
    have h1 : StatedQuadMinus 3 F b c a = μ * (μ * StatedQuadMinus 3 F b c a) := by
      calc StatedQuadMinus 3 F b c a = StatedQuadMinus 3 F b c (A *ᵥ (A *ᵥ a)) := by rw [hAAx]
        _ = μ * StatedQuadMinus 3 F b c (A *ᵥ a) := hQA _
        _ = μ * (μ * StatedQuadMinus 3 F b c a) := by rw [hQA]
    have h3 : (μ * μ - 1) * StatedQuadMinus 3 F b c a = 0 := by linear_combination (-1 : F) * h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right ha')
  have hμ1 : μ = 1 := by
    have h3 : (μ - 1) ^ 2 = 0 := by linear_combination hμ2 - (μ - 1) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)
  intro x
  rw [hQA, hμ1, one_mul]

theorem omega_isometry_of_normalizes_pow (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) (k : ℕ)
    (hAk : A ^ (2 ^ k) = 1)
    (hN : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∃ g' ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
        A *ᵥ ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          F) *ᵥ x) =
          (g' : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
            (A *ᵥ x)) :
    ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      StatedQuadMinus 3 F b c (A *ᵥ x) = StatedQuadMinus 3 F b c x := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hcoe : ⇑(quadMinus 3 F b c) = StatedQuadMinus 3 F b c := coe_quadMinus 3 F b c
  obtain ⟨μ, hQA⟩ := omega_similitude_of_normalizes hirr A hN
  obtain ⟨a, ha⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
  have ha' : StatedQuadMinus 3 F b c a ≠ 0 := by rw [← hcoe]; exact ha
  have hpow : ∀ j : ℕ, ∀ x, StatedQuadMinus 3 F b c ((A ^ j) *ᵥ x) = μ ^ j * StatedQuadMinus 3 F b c x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ', ← Matrix.mulVec_mulVec, hQA, ih, pow_succ']
      ring
  have h1 : StatedQuadMinus 3 F b c a = μ ^ (2 ^ k) * StatedQuadMinus 3 F b c a := by
    have := hpow (2 ^ k) a
    rw [hAk, Matrix.one_mulVec] at this
    exact this
  have h3 : (μ ^ (2 ^ k) - 1) * StatedQuadMinus 3 F b c a = 0 := by linear_combination (-1 : F) * h1
  have hμ : μ ^ (2 ^ k) = 1 := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right ha')
  have hμ1 : μ = 1 := by
    have h4 : (μ - 1) ^ (2 ^ k) = 0 := by
      rw [sub_pow_char_pow, hμ, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h4)
  intro x
  rw [hQA, hμ1, one_mul]

end CFSG.LocalAnalysis.RankThreeUC
