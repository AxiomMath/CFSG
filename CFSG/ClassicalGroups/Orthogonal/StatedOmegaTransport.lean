module

public import CFSG.ClassicalGroups.F2Fixed.Descent
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedInf
public import CFSG.ClassicalGroups.F2Swap

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups.F2Fixed CFSG.Open QuadraticMap CFSG.LieType.Universal.Spin
open Matrix

universe uM

structure ElemMatrixIso {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Q : QuadraticForm K (ι → K)) (X : Subgroup (GL ι K)) where
  equiv : X ≃* Gom Q
  app : ∀ (A : X) (v : ι → K), (equiv A).app v = ((A : GL ι K) : Matrix ι ι K) *ᵥ v

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}

@[expose] def ElemMatrixIso.LomGL (E : ElemMatrixIso Q X) (u : ι → K) : Subgroup (GL ι K) :=
  matrixOf X E.equiv (Lom Q u)

@[expose] noncomputable def ElemMatrixIso.ofStated {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) : ElemMatrixIso Q (StatedOmega Q₀) where
  equiv := statedOmegaEquiv hQ hE
  app A v := by
    unfold Gom.app
    rw [coe_statedOmegaEquiv, toLinEquiv_apply]

theorem ElemMatrixIso.LomGL_ofStated {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (u : ι → K) :
    (ElemMatrixIso.ofStated hQ hE).LomGL u =
      CFSG.ClassicalGroups.Orthogonal.LomGL hQ hE u := by
  unfold ElemMatrixIso.LomGL CFSG.ClassicalGroups.Orthogonal.LomGL matrixOf
  exact congrArg (Subgroup.map (StatedOmega Q₀).subtype)
    (Subgroup.comap_equiv_eq_map_symm (statedOmegaEquiv hQ hE) (Lom Q u))

theorem mem_Lom_app_iff {V : Type} [AddCommGroup V] [Module K V] {Q' : QuadraticForm K V}
    (g : Gom Q') (u : V) (h : Gom Q') : h ∈ Lom Q' (g.app u) ↔ g⁻¹ * h * g ∈ Lom Q' u := by
  constructor
  · intro hh
    have := conj_mem_Lom g⁻¹ hh
    rwa [Gom.app_inv_app, inv_inv] at this
  · intro hh
    have := conj_mem_Lom g hh
    have e : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    rwa [e] at this

theorem ElemMatrixIso.mem_LomGL_iff_flag
    (E : ElemMatrixIso Q X) (hQ : (polarBilin Q).Nondegenerate) {u : ι → K} (hu : Q u = 0)
    (hu0 : u ≠ 0) {A : GL ι K} :
    A ∈ E.LomGL u ↔ A ∈ X ∧ (A : Matrix ι ι K) *ᵥ u = u ∧
      (∀ x, polar Q u x = 0 → ∃ c : K, (A : Matrix ι ι K) *ᵥ x - x = c • u) ∧
        ∀ x, polar Q u ((A : Matrix ι ι K) *ᵥ x - x) = 0 := by
  unfold ElemMatrixIso.LomGL
  rw [mem_matrixOf_iff]
  constructor
  · rintro ⟨hA, h⟩
    have := (mem_Lom_iff_flag hQ hu hu0 (E.equiv ⟨A, hA⟩)).mp h
    simp only [E.app] at this
    exact ⟨hA, this⟩
  · rintro ⟨hA, h⟩
    refine ⟨hA, (mem_Lom_iff_flag hQ hu hu0 (E.equiv ⟨A, hA⟩)).mpr ?_⟩
    simpa only [E.app] using h

@[expose] noncomputable def ElemMatrixIso.plus {m : ℕ} (hm : 3 ≤ m) :
    ElemMatrixIso (quadPlus m K) (StatedOmega (StatedQuadPlus m K)) :=
  ElemMatrixIso.ofStated (coe_quadPlus m K) (commutator_orthogonalGroup_quadPlus hm)

@[expose] noncomputable def ElemMatrixIso.minus [Finite K] [CharP K 2] {m : ℕ} {b c : K}
    (hm : 2 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ElemMatrixIso (quadMinus m K b c) (StatedOmega (StatedQuadMinus m K b c)) :=
  ElemMatrixIso.ofStated (coe_quadMinus m K b c)
    (commutator_orthogonalGroup_quadMinus_of_two_le hm hirr)

theorem ElemMatrixIso.LomGL_plus {m : ℕ} (hm : 3 ≤ m) (u : Fin m ⊕ Fin m → K) :
    (ElemMatrixIso.plus hm).LomGL u = LomGLPlus hm u :=
  ElemMatrixIso.LomGL_ofStated _ _ u

theorem ElemMatrixIso.LomGL_minus [Finite K] [CharP K 2] {m : ℕ} {b c : K} (hm : 2 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (u : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    (ElemMatrixIso.minus hm hirr).LomGL u = LomGLMinus hm hirr u :=
  ElemMatrixIso.LomGL_ofStated _ _ u

theorem ElemMatrixIso.exists_mulVec_eq (E : ElemMatrixIso Q X)
    (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q} (h : P.Orth P') {x y : ι → K}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : Q x = Q y) :
    ∃ A ∈ X, ((A : GL ι K) : Matrix ι ι K) *ᵥ x = y := by
  obtain ⟨g, hg, hgx⟩ := exists_mem_elementaryGroup_apply_eq hQ h hx hy hxy
  refine ⟨((E.equiv.symm ⟨g, hg⟩ : X) : GL ι K), (E.equiv.symm ⟨g, hg⟩).2, ?_⟩
  have := E.app (E.equiv.symm ⟨g, hg⟩) x
  rw [MulEquiv.apply_symm_apply] at this
  rw [← this]
  exact hgx

theorem ElemMatrixIso.exists_mulVec_eq_smul [Finite K] [CharP K 2] (E : ElemMatrixIso Q X)
    (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q} (h : P.Orth P') {x y : ι → K}
    (hx : Q x ≠ 0) (hy : Q y ≠ 0) :
    ∃ A ∈ X, ∃ c : K, c ≠ 0 ∧ ((A : GL ι K) : Matrix ι ι K) *ᵥ x = c • y := by
  obtain ⟨c, hc⟩ := isSquare_of_charTwo' (Q x / Q y)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : Q x / Q y = 0 := by rw [hc]; ring
    exact div_ne_zero hx hy this
  have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0, QuadraticMap.map_zero])
  have hy0 : c • y ≠ 0 := fun h0 => hy (by
    have := (smul_eq_zero.mp h0).resolve_left hc0
    rw [this, QuadraticMap.map_zero])
  have hQc : Q x = Q (c • y) := by
    rw [QuadraticMap.map_smul, smul_eq_mul, ← hc]
    field_simp
  obtain ⟨A, hA, hAx⟩ := E.exists_mulVec_eq hQ h hx0 hy0 hQc
  exact ⟨A, hA, c, hc0, hAx⟩

theorem ElemMatrixIso.LomGL_sup_eq (E : ElemMatrixIso Q X) (hQ : (polarBilin Q).Nondegenerate)
    {u u' : ι → K} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0) :
    E.LomGL u ⊔ E.LomGL u' = X := by
  have h := CFSG.ClassicalGroups.F2Swap.sup_subgroupOf_eq_top (rootGroup_le_elementaryGroup Q u)
    (rootGroup_le_elementaryGroup Q u') (rootGroup_sup_eq_elementaryGroup hQ hu hu' huu')
  show matrixOf X E.equiv (Lom Q u) ⊔ matrixOf X E.equiv (Lom Q u') = X
  rw [← matrixOf_sup]
  exact (congrArg _ h).trans matrixOf_top

section Transport

variable (E : ElemMatrixIso Q X) {Y : Type*} [Group Y] (φ : Y →* GL ι K) (hφ : φ.range = X)

theorem viaMatrix_app (y : Y) (v : ι → K) :
    (viaMatrix X E.equiv φ hφ y).app v = (φ y : Matrix ι ι K) *ᵥ v :=
  E.app ⟨φ y, hφ ▸ MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩ v

variable [Finite K] [CharP K 2] {M : Type uM} [AddCommGroup M] [Finite M] [DistribMulAction Y M]

include hφ

theorem fixedSub_descend_Lom (hker : ∀ y ∈ φ.ker, ∀ a : M, y • a = a) {L : Subgroup Y}
    {u : ι → K} (hL : L.map φ = E.LomGL u) :
    @fixedSub (Gom Q) _ M _ (descendAction (viaMatrix X E.equiv φ hφ)
      (viaMatrix_surjective φ hφ) (fun y hy a => by
        rw [ker_viaMatrix] at hy
        exact hker y hy a)) ((Lom Q u : Subgroup (Gom Q)) : Set (Gom Q)) =
      fixedSub M (L : Set Y) :=
  (fixedSub_descend _ _ _ _).trans (fixedSub_viaMatrix_eq φ hφ hker hL)

theorem stroth_2_1_ii_omegaMinus_of_hom {m : ℕ} (hm : 2 ≤ m) (h : IsMinus Q m)
    (h2 : ∀ x : M, x + x = 0) (hker : ∀ y ∈ φ.ker, ∀ a : M, y • a = a)
    {u u' : ι → K} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    {L₁ L₂ : Subgroup Y} (hL₁ : L₁.map φ = E.LomGL u) (hL₂ : L₂.map φ = E.LomGL u')
    (hdec : IsCompl (fixedSub M (L₁ : Set Y)) (fixedSub M (L₂ : Set Y))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (2 ^ m * n) := by
  letI : DistribMulAction (Gom Q) M := descendAction (viaMatrix X E.equiv φ hφ)
    (viaMatrix_surjective φ hφ) (fun y hy a => by
      rw [ker_viaMatrix] at hy
      exact hker y hy a)
  refine stroth_2_1_ii_omegaMinus hm h h2 hu hu' huu' ?_
  rw [fixedSub_descend_Lom E φ hφ hker hL₁, fixedSub_descend_Lom E φ hφ hker hL₂]
  exact hdec

theorem stroth_2_1_ii_omegaPlus_of_hom {m : ℕ} (hm : 3 ≤ m) (h : IsPlus Q m)
    (h2 : ∀ x : M, x + x = 0) (hker : ∀ y ∈ φ.ker, ∀ a : M, y • a = a)
    {u u' : ι → K} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    {L₁ L₂ : Subgroup Y} (hL₁ : L₁.map φ = E.LomGL u) (hL₂ : L₂.map φ = E.LomGL u')
    (hdec : IsCompl (fixedSub M (L₁ : Set Y)) (fixedSub M (L₂ : Set Y))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (2 ^ (m - 1) * n) := by
  letI : DistribMulAction (Gom Q) M := descendAction (viaMatrix X E.equiv φ hφ)
    (viaMatrix_surjective φ hφ) (fun y hy a => by
      rw [ker_viaMatrix] at hy
      exact hker y hy a)
  refine stroth_2_1_ii_omegaPlus hm h h2 hu hu' huu' ?_
  rw [fixedSub_descend_Lom E φ hφ hker hL₁, fixedSub_descend_Lom E φ hφ hker hL₂]
  exact hdec

end Transport

theorem ElemMatrixIso.LomGL_inf_eq_bot_iff [Finite K] [CharP K 2] (E : ElemMatrixIso Q X)
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 2 < Module.finrank K (ι → K)) {u u' : ι → K}
    (hu : Q u = 0) (hu' : Q u' = 0) (hu0 : u ≠ 0) (hu'0 : u' ≠ 0) :
    E.LomGL u ⊓ E.LomGL u' = ⊥ ↔ polar Q u u' ≠ 0 := by
  rw [← Lom_inf_eq_bot_iff hQ h3 hu hu' hu0 hu'0]
  exact matrixOf_inf_eq_bot_iff _ _

section Models

variable [Finite K] [CharP K 2]

theorem statedOmegaPlus_exists_mulVec_eq {m : ℕ} (hm : 3 ≤ m) {x y : Fin m ⊕ Fin m → K}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : quadPlus m K x = quadPlus m K y) :
    ∃ A ∈ StatedOmega (StatedQuadPlus m K),
      ((A : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = y :=
  (ElemMatrixIso.plus hm).exists_mulVec_eq (nondegenerate_polarBilin_quadPlus m K)
    (P := plusPair K ⟨0, by omega⟩) (P' := plusPair K ⟨1, by omega⟩)
    (plusPair_orth (by simp [Fin.ext_iff])) hx hy hxy

theorem statedOmegaPlus_exists_mulVec_eq_smul {m : ℕ} (hm : 3 ≤ m) {x y : Fin m ⊕ Fin m → K}
    (hx : quadPlus m K x ≠ 0) (hy : quadPlus m K y ≠ 0) :
    ∃ A ∈ StatedOmega (StatedQuadPlus m K), ∃ c : K, c ≠ 0 ∧
      ((A : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = c • y :=
  (ElemMatrixIso.plus hm).exists_mulVec_eq_smul (nondegenerate_polarBilin_quadPlus m K)
    (P := plusPair K ⟨0, by omega⟩) (P' := plusPair K ⟨1, by omega⟩)
    (plusPair_orth (by simp [Fin.ext_iff])) hx hy

variable {b c : K}

theorem statedOmegaMinus_exists_mulVec_eq {m : ℕ} (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {x y : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : quadMinus m K b c x = quadMinus m K b c y) :
    ∃ A ∈ StatedOmega (StatedQuadMinus m K b c),
      ((A : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
        Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) *ᵥ x =
          y :=
  (ElemMatrixIso.minus (by omega) hirr).exists_mulVec_eq
    (nondegenerate_polarBilin_quadMinus_of_finite m K hirr)
    (P := minusPair K b c ⟨0, by omega⟩) (P' := minusPair K b c ⟨1, by omega⟩)
    (minusPair_orth (by simp [Fin.ext_iff])) hx hy hxy

end Models

end CFSG.ClassicalGroups.Orthogonal
