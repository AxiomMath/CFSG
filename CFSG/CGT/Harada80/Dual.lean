module

public import CFSG.CGT.Harada80.OmegaReflect
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M2Basic
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19 Matrix
open scoped commutatorElement

theorem exists_polar_eq {m : ℕ} (f : (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) →+ ZMod 2) :
    ∃ w, ∀ y, f y = QuadraticMap.polar (quadQ m) w y := by
  classical
  let B : LinearMap.BilinForm (ZMod 2) (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :=
    QuadraticMap.polarBilin (quadQ m)
  have hB : B.Nondegenerate := nondegenerate_quadQ m
  let F : (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    f.toZModLinearMap 2
  refine ⟨(B.toDual hB).symm F, ?_⟩
  intro y
  have h : B ((B.toDual hB).symm F) y = F y := by
    rw [← LinearMap.BilinForm.toDual_def (b := hB), LinearEquiv.apply_symm_apply]
  exact h.symm

theorem eq_zero_of_polar_eq_zero {m : ℕ} {w : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2}
    (h : ∀ y, QuadraticMap.polar (quadQ m) w y = 0) : w = 0 :=
  (nondegenerate_quadQ m).1 w fun y => by
    simpa [QuadraticMap.polarBilin_apply_apply] using h y

theorem polar_mulVec_of_mem {m : ℕ} {g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)}
    (hg : g ∈ omegaMinusTwo m) (x y : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :
    QuadraticMap.polar (quadQ m) ((g : Matrix _ _ (ZMod 2)) *ᵥ x)
        ((g : Matrix _ _ (ZMod 2)) *ᵥ y) =
      QuadraticMap.polar (quadQ m) x y := by
  let O := TauCeti.QuadraticMap.orthogonalGroup (quadQ m)
  have hg' : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2)
      (ZMod 2) g ∈ ⁅O, O⁆ := by
    rw [omegaMinusTwo_eq_comap, Subgroup.mem_comap] at hg
    exact hg
  have hO : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2)
      (ZMod 2) g ∈ O := by
    have h : ⁅O, O⁆ ≤ O :=
      (Subgroup.le_normalizer_iff_commutator_le_right).mp Subgroup.le_normalizer
    exact h hg'
  have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO x y
  simpa [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply] using h

private theorem polar_eq_of_forall {m : ℕ}
    {x y : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2}
    (h : ∀ v, QuadraticMap.polar (quadQ m) x v = QuadraticMap.polar (quadQ m) y v) :
    x = y := by
  have h0 : x - y = 0 := eq_zero_of_polar_eq_zero fun v => by
    rw [QuadraticMap.polar_sub_left, h v, sub_self]
  exact sub_eq_zero.mp h0

private noncomputable def omegaMat (m : ℕ) (g : ↥(omegaMinusTwo m)) :
    Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) :=
  (g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))

private theorem polar_swap {m : ℕ} (x : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)
    (g : ↥(omegaMinusTwo m)) (v : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :
    QuadraticMap.polar (quadQ m) x (omegaMat m g *ᵥ v) =
      QuadraticMap.polar (quadQ m) (omegaMat m g⁻¹ *ᵥ x) v := by
  have h := polar_mulVec_of_mem (m := m) g.2 (omegaMat m g⁻¹ *ᵥ x) v
  have hx : ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
      (omegaMat m g⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec]
    simp [omegaMat]
  rw [hx] at h
  exact h

namespace Setting

private noncomputable def blockConj {G : Type} [Group G] (J : Subgroup G) :
    ↥J →* MulAut ↥(blockU J) :=
  (Subgroup.normalizerMonoidHom (blockU J)).comp
    (Subgroup.inclusion (by
      have h : J ≤ Subgroup.normalizer ((⁅blockQ J, J⁆ : Subgroup G) : Set G) :=
        Subgroup.normalizer_commutator_ge_right (H₁ := blockQ J) (H₂ := J)
      simpa [blockU] using h))

private theorem blockConj_coe {G : Type} [Group G] (J : Subgroup G)
    (ℓ : ↥J) (u : ↥(blockU J)) :
    ((blockConj J ℓ u : ↥(blockU J)) : G) = (ℓ : G) * (u : G) * (ℓ : G)⁻¹ := by
  simpa [blockConj] using
    Subgroup.normalizerMonoidHom_apply_apply_coe (blockU J)
      (Subgroup.inclusion _ ℓ) u

private noncomputable def blockBeta {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ}
    (S : Setting G M J m) :
    Additive ↥(blockU J) →+ (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :=
  MonoidHom.toAdditiveLeft S.beta

private theorem blockBeta_surjective {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ}
    (S : Setting G M J m) : Function.Surjective (blockBeta S) := by
  intro v
  obtain ⟨u, hu⟩ := S.beta_surjective (Multiplicative.ofAdd v)
  exact ⟨Additive.ofMul u, by simpa [blockBeta] using congrArg Multiplicative.toAdd hu⟩

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} (S : Setting G M J m)
include S

private noncomputable def blockAlphaMat (ℓ : ↥J) :
    Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) :=
  omegaMat m (S.alpha ℓ)

private theorem blockBeta_conj (ℓ : ↥J) (u : Additive ↥(blockU J)) :
    blockBeta S (blockConj J ℓ u) =
      (((S.alpha ℓ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
        blockBeta S u) := by
  have h := S.beta_conj ℓ (Additive.toMul u) (blockConj J ℓ u) (blockConj_coe J ℓ u)
  change Multiplicative.toAdd (S.beta (blockConj J ℓ u)) =
    ((S.alpha ℓ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
      Multiplicative.toAdd (S.beta (Additive.toMul u))
  exact h

private theorem exists_polar_w (φ : Additive ↥(blockU J) →+ ZMod 2) :
    ∃ w : ↥J → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2),
      ∀ (ℓ : ↥J) (u : Additive ↥(blockU J)),
        QuadraticMap.polar (quadQ m) (w ℓ) (blockBeta S u) =
          φ (Additive.ofMul (blockConj J (ℓ⁻¹) (Additive.toMul u))) - φ u := by
  classical
  have hβa := blockBeta_surjective S
  let ψ : ↥J → Additive ↥(blockU J) →+ ZMod 2 := fun ℓ =>
    φ.comp (blockConj J (ℓ⁻¹)).toAdditive - φ
  have hker_le (ℓ : ↥J) : (blockBeta S).ker ≤ (ψ ℓ).ker := by
    intro u hu
    rw [AddMonoidHom.mem_ker] at hu ⊢
    let u' : ↥(blockU J) := Additive.toMul u
    have huβ : u' ∈ S.beta.ker := by
      rw [MonoidHom.mem_ker, ← toAdd_eq_zero]
      simpa [blockBeta, u'] using hu
    have hzZ : (u' : G) ∈ blockZ J := by
      rw [S.ker_beta] at huβ
      exact huβ
    have hconj : blockConj J (ℓ⁻¹) u' = u' := by
      apply Subtype.ext
      rw [blockConj_coe]
      have hcomm := (Subgroup.mem_centralizer_iff.mp hzZ.2) ((ℓ⁻¹ : ↥J) : G)
        (SetLike.coe_mem _)
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    simp only [ψ, AddMonoidHom.comp_apply, AddMonoidHom.sub_apply]
    change φ (Additive.ofMul (blockConj J (ℓ⁻¹) u')) - φ u = 0
    rw [hconj]
    simp [u']
  have hψβ (ℓ : ↥J) {u₁ u₂ : Additive ↥(blockU J)}
      (h : blockBeta S u₁ = blockBeta S u₂) : ψ ℓ u₁ = ψ ℓ u₂ := by
    have hker : u₁ - u₂ ∈ (blockBeta S).ker := by
      rw [AddMonoidHom.mem_ker, map_sub, h, sub_self]
    have h0 : ψ ℓ (u₁ - u₂) = 0 := hker_le ℓ hker
    rwa [map_sub, sub_eq_zero] at h0
  let βinv : (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) → Additive ↥(blockU J) :=
    Function.surjInv hβa
  let lam : ↥J → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) →+ ZMod 2 := fun ℓ =>
    AddMonoidHom.liftOfSurjective (blockBeta S) hβa ⟨ψ ℓ, hker_le ℓ⟩
  have hlam : ∀ (ℓ : ↥J) (v : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2),
      lam ℓ v = ψ ℓ (βinv v) := by
    intro ℓ v
    have h : lam ℓ (blockBeta S (βinv v)) = ψ ℓ (βinv v) := by
      simp [lam]
    rwa [Function.surjInv_eq hβa v] at h
  refine ⟨fun ℓ => Classical.choose (exists_polar_eq (m := m) (lam ℓ)), ?_⟩
  intro ℓ u
  have hw : QuadraticMap.polar (quadQ m)
      (Classical.choose (exists_polar_eq (m := m) (lam ℓ))) (blockBeta S u) =
      lam ℓ (blockBeta S u) :=
    (Classical.choose_spec (exists_polar_eq (m := m) (lam ℓ)) (blockBeta S u)).symm
  rw [hw, hlam ℓ (blockBeta S u), hψβ ℓ (Function.surjInv_eq hβa (blockBeta S u))]
  rfl

private noncomputable def blockPsi (φ : Additive ↥(blockU J) →+ ZMod 2) (ℓ : ↥J) :
    Additive ↥(blockU J) →+ ZMod 2 :=
  φ.comp (blockConj J (ℓ⁻¹)).toAdditive - φ

private theorem blockPsi_mul (φ : Additive ↥(blockU J) →+ ZMod 2)
    (ℓ₁ ℓ₂ : ↥J) (u : Additive ↥(blockU J)) :
    blockPsi φ (ℓ₁ * ℓ₂) u =
      blockPsi φ ℓ₂ (Additive.ofMul (blockConj J (ℓ₁⁻¹) (Additive.toMul u))) +
        blockPsi φ ℓ₁ u := by
  simp only [blockPsi, AddMonoidHom.comp_apply, AddMonoidHom.sub_apply]
  change φ (Additive.ofMul (blockConj J ((ℓ₁ * ℓ₂)⁻¹) (Additive.toMul u))) - φ u =
    (φ (Additive.ofMul (blockConj J (ℓ₂⁻¹)
        (blockConj J (ℓ₁⁻¹) (Additive.toMul u)))) -
      φ (Additive.ofMul (blockConj J (ℓ₁⁻¹) (Additive.toMul u)))) +
      (φ (Additive.ofMul (blockConj J (ℓ₁⁻¹) (Additive.toMul u))) - φ u)
  have hc : blockConj J ((ℓ₁ * ℓ₂)⁻¹) (Additive.toMul u) =
      blockConj J (ℓ₂⁻¹) (blockConj J (ℓ₁⁻¹) (Additive.toMul u)) := by
    rw [_root_.mul_inv_rev, map_mul, MulAut.mul_apply]
  rw [hc]
  abel

private theorem polar_w_cocycle (φ : Additive ↥(blockU J) →+ ZMod 2)
    (w : ↥J → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2))
    (hw : ∀ (ℓ : ↥J) (u : Additive ↥(blockU J)),
      QuadraticMap.polar (quadQ m) (w ℓ) (blockBeta S u) =
        φ (Additive.ofMul (blockConj J (ℓ⁻¹) (Additive.toMul u))) - φ u)
    (ℓ₁ ℓ₂ : ↥J) :
    w (ℓ₁ * ℓ₂) = w ℓ₁ + blockAlphaMat S ℓ₁ *ᵥ w ℓ₂ := by
  let βinv : (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) → Additive ↥(blockU J) :=
    Function.surjInv (blockBeta_surjective S)
  have hβinv : ∀ v, blockBeta S (βinv v) = v := Function.surjInv_eq _
  have hwv (ℓ : ↥J) (v : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :
      QuadraticMap.polar (quadQ m) (w ℓ) v = blockPsi φ ℓ (βinv v) := by
    have h := hw ℓ (βinv v)
    change QuadraticMap.polar (quadQ m) (w ℓ) v =
      φ (Additive.ofMul (blockConj J (ℓ⁻¹) (Additive.toMul (βinv v)))) - φ (βinv v)
    rwa [hβinv v] at h
  have hβconj (ℓ : ↥J) (u : Additive ↥(blockU J)) :
      blockBeta S (blockConj J ℓ u) = blockAlphaMat S ℓ *ᵥ blockBeta S u :=
    blockBeta_conj S ℓ u
  apply polar_eq_of_forall
  intro v
  calc
    QuadraticMap.polar (quadQ m) (w (ℓ₁ * ℓ₂)) v = blockPsi φ (ℓ₁ * ℓ₂) (βinv v) := hwv _ _
    _ = blockPsi φ ℓ₂ (Additive.ofMul
          (blockConj J (ℓ₁⁻¹) (Additive.toMul (βinv v)))) +
        blockPsi φ ℓ₁ (βinv v) := blockPsi_mul S φ _ _ _
    _ = QuadraticMap.polar (quadQ m) (w ℓ₂)
          (blockBeta S (Additive.ofMul
            (blockConj J (ℓ₁⁻¹) (Additive.toMul (βinv v))))) +
        QuadraticMap.polar (quadQ m) (w ℓ₁) (blockBeta S (βinv v)) := by
          rw [show blockPsi φ ℓ₂ (Additive.ofMul
                (blockConj J (ℓ₁⁻¹) (Additive.toMul (βinv v)))) =
              QuadraticMap.polar (quadQ m) (w ℓ₂)
                (blockBeta S (Additive.ofMul
                  (blockConj J (ℓ₁⁻¹) (Additive.toMul (βinv v))))) from
                (hw ℓ₂ (Additive.ofMul
                  (blockConj J (ℓ₁⁻¹) (Additive.toMul (βinv v))))).symm,
            show blockPsi φ ℓ₁ (βinv v) =
              QuadraticMap.polar (quadQ m) (w ℓ₁) (blockBeta S (βinv v)) from
                (hw ℓ₁ (βinv v)).symm]
    _ = QuadraticMap.polar (quadQ m) (w ℓ₂)
          (blockBeta S (Additive.ofMul (blockConj J (ℓ₁⁻¹) (Additive.toMul (βinv v))))) +
        QuadraticMap.polar (quadQ m) (w ℓ₁) v := by rw [hβinv]
    _ = QuadraticMap.polar (quadQ m) (w ℓ₂)
          (blockBeta S (blockConj J (ℓ₁⁻¹) (βinv v))) +
        QuadraticMap.polar (quadQ m) (w ℓ₁) v := rfl
    _ = QuadraticMap.polar (quadQ m) (w ℓ₂) (blockAlphaMat S (ℓ₁⁻¹) *ᵥ v) +
        QuadraticMap.polar (quadQ m) (w ℓ₁) v := by
          rw [hβconj, hβinv]
    _ = QuadraticMap.polar (quadQ m) (blockAlphaMat S ℓ₁ *ᵥ w ℓ₂) v +
        QuadraticMap.polar (quadQ m) (w ℓ₁) v := by
          simpa [blockAlphaMat, map_inv] using
            polar_swap (w ℓ₂) ((S.alpha ℓ₁)⁻¹) v
    _ = QuadraticMap.polar (quadQ m) (w ℓ₁ + blockAlphaMat S ℓ₁ *ᵥ w ℓ₂) v := by
          rw [QuadraticMap.polar_add_left]
          abel

private theorem polar_w_eq_zero_of_alpha_eq_one (φ : Additive ↥(blockU J) →+ ZMod 2)
    (w : ↥J → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2))
    (hw : ∀ (ℓ : ↥J) (u : Additive ↥(blockU J)),
      QuadraticMap.polar (quadQ m) (w ℓ) (blockBeta S u) =
        φ (Additive.ofMul (blockConj J (ℓ⁻¹) (Additive.toMul u))) - φ u)
    {ℓ : ↥J} (hℓ : S.alpha ℓ = 1) : w ℓ = 0 := by
  have hℓQ : (ℓ : G) ∈ blockQ J := by
    exact Subgroup.mem_map.mpr ⟨ℓ, by rwa [← S.ker_alpha, MonoidHom.mem_ker], rfl⟩
  have hw0 : ∀ u : Additive ↥(blockU J),
      QuadraticMap.polar (quadQ m) (w ℓ) (blockBeta S u) = 0 := by
    intro u
    have hconj : blockConj J (ℓ⁻¹) (Additive.toMul u) = Additive.toMul u := by
      apply Subtype.ext
      rw [blockConj_coe]
      have hℓQ' : ((ℓ⁻¹ : ↥J) : G) ∈ blockQ J := by
        simpa using (blockQ J).inv_mem hℓQ
      have hcomm :=
        (Subgroup.mem_centralizer_iff.mp (S.short.blockU_le_center (Additive.toMul u).2).2)
          ((ℓ⁻¹ : ↥J) : G) hℓQ'
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hw ℓ u, hconj]
    simp
  apply eq_zero_of_polar_eq_zero
  intro v
  obtain ⟨u, rfl⟩ := blockBeta_surjective S v
  exact hw0 u

private theorem polar_w_alpha_eq (φ : Additive ↥(blockU J) →+ ZMod 2)
    (w : ↥J → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2))
    (hw : ∀ (ℓ : ↥J) (u : Additive ↥(blockU J)),
      QuadraticMap.polar (quadQ m) (w ℓ) (blockBeta S u) =
        φ (Additive.ofMul (blockConj J (ℓ⁻¹) (Additive.toMul u))) - φ u)
    {ℓ ℓ' : ↥J} (h : S.alpha ℓ = S.alpha ℓ') : w ℓ = w ℓ' := by
  have hk : S.alpha (ℓ⁻¹ * ℓ') = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hk0 : w (ℓ⁻¹ * ℓ') = 0 :=
    polar_w_eq_zero_of_alpha_eq_one S φ w hw hk
  have hc := polar_w_cocycle S φ w hw ℓ (ℓ⁻¹ * ℓ')
  rw [mul_inv_cancel_left] at hc
  rw [hk0, Matrix.mulVec_zero, add_zero] at hc
  exact hc.symm

private theorem exists_a_of_h1 (hH1 : H1Natural m)
    (φ : Additive ↥(blockU J) →+ ZMod 2)
    (w : ↥J → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2))
    (hw : ∀ (ℓ : ↥J) (u : Additive ↥(blockU J)),
      QuadraticMap.polar (quadQ m) (w ℓ) (blockBeta S u) =
        φ (Additive.ofMul (blockConj J (ℓ⁻¹) (Additive.toMul u))) - φ u) :
    ∃ a : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2,
      ∀ ℓ : ↥J, w ℓ = blockAlphaMat S ℓ *ᵥ a - a := by
  have hcocycle := polar_w_cocycle S φ w hw
  have halpha : ∀ {ℓ ℓ' : ↥J}, S.alpha ℓ = S.alpha ℓ' → w ℓ = w ℓ' :=
    fun h => polar_w_alpha_eq S φ w hw h
  let gα : ↥(omegaMinusTwo m) → ↥J := Function.surjInv S.alpha_surjective
  have hgα : ∀ ω, S.alpha (gα ω) = ω := Function.surjInv_eq S.alpha_surjective
  let F : ↥(omegaMinusTwo m) → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) := fun ω => w (gα ω)
  have hF_alpha : ∀ ℓ : ↥J, F (S.alpha ℓ) = w ℓ := by
    intro ℓ
    apply halpha
    rw [hgα]
  have hF : ∀ x y : ↥(omegaMinusTwo m), F (x * y) = F x + omegaMat m x *ᵥ F y := by
    intro x y
    have hα : S.alpha (gα (x * y)) = S.alpha (gα x * gα y) := by
      rw [map_mul, hgα, hgα, hgα]
    calc
      F (x * y) = w (gα (x * y)) := rfl
      _ = w (gα x * gα y) := halpha hα
      _ = w (gα x) + blockAlphaMat S (gα x) *ᵥ w (gα y) := hcocycle _ _
      _ = F x + omegaMat m x *ᵥ F y := by
        simp only [F, blockAlphaMat, hgα]
  obtain ⟨a, ha⟩ := hH1 F hF
  refine ⟨a, fun ℓ => ?_⟩
  have h := ha (S.alpha ℓ)
  rw [hF_alpha] at h
  change w ℓ = (((S.alpha ℓ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
    Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ a - a)
  exact h

private noncomputable def blockFunctional (φ : Additive ↥(blockU J) →+ ZMod 2)
    (a : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :
    Additive ↥(blockU J) →+ ZMod 2 :=
{ toFun := fun u => φ u - QuadraticMap.polar (quadQ m) a (blockBeta S u)
  map_zero' := by
    rw [map_zero, map_zero, QuadraticMap.polar_zero_right, sub_zero]
  map_add' := by
    intro u v
    rw [map_add, map_add]
    rw [QuadraticMap.polar_add_right (Q := quadQ m) a (S.blockBeta u) (S.blockBeta v)]
    abel }

private theorem functional_invariant (φ : Additive ↥(blockU J) →+ ZMod 2)
    (w : ↥J → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2))
    (a : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)
    (hw : ∀ (ℓ : ↥J) (u : Additive ↥(blockU J)),
      QuadraticMap.polar (quadQ m) (w ℓ) (blockBeta S u) =
        φ (Additive.ofMul (blockConj J (ℓ⁻¹) (Additive.toMul u))) - φ u)
    (ha : ∀ ℓ : ↥J, w ℓ = blockAlphaMat S ℓ *ᵥ a - a) :
    ∀ (ℓ : ↥J) (u : Additive ↥(blockU J)),
      blockFunctional S φ a (blockConj J (ℓ⁻¹) u) = blockFunctional S φ a u := by
  intro ℓ u
  have hψu : φ (Additive.ofMul (blockConj J (ℓ⁻¹) (Additive.toMul u))) - φ u =
      QuadraticMap.polar (quadQ m) (w ℓ) (blockBeta S u) := (hw ℓ u).symm
  have hswapA : QuadraticMap.polar (quadQ m) a
      (blockAlphaMat S (ℓ⁻¹) *ᵥ blockBeta S u) =
      QuadraticMap.polar (quadQ m) (blockAlphaMat S ℓ *ᵥ a) (blockBeta S u) := by
    simpa [blockAlphaMat] using polar_swap a ((S.alpha ℓ)⁻¹) (blockBeta S u)
  have hdiff : blockFunctional S φ a (blockConj J (ℓ⁻¹) u) -
      blockFunctional S φ a u = 0 := by
    change (φ (Additive.ofMul (blockConj J (ℓ⁻¹) (Additive.toMul u))) -
        QuadraticMap.polar (quadQ m) a (blockBeta S (blockConj J (ℓ⁻¹) u))) -
      (φ u - QuadraticMap.polar (quadQ m) a (blockBeta S u)) = 0
    rw [blockBeta_conj]
    change (φ (Additive.ofMul (blockConj J (ℓ⁻¹) (Additive.toMul u))) -
          QuadraticMap.polar (quadQ m) a (blockAlphaMat S (ℓ⁻¹) *ᵥ blockBeta S u)) -
        (φ u - QuadraticMap.polar (quadQ m) a (blockBeta S u)) = 0
    have h0 : (φ (Additive.ofMul (blockConj J (ℓ⁻¹) (Additive.toMul u))) -
          QuadraticMap.polar (quadQ m) a (blockAlphaMat S (ℓ⁻¹) *ᵥ blockBeta S u)) -
        (φ u - QuadraticMap.polar (quadQ m) a (blockBeta S u)) =
        (φ (Additive.ofMul (blockConj J (ℓ⁻¹) (Additive.toMul u))) - φ u) -
          (QuadraticMap.polar (quadQ m) a (blockAlphaMat S (ℓ⁻¹) *ᵥ blockBeta S u) -
            QuadraticMap.polar (quadQ m) a (blockBeta S u)) := by abel
    rw [h0, hψu, hswapA, ha ℓ, QuadraticMap.polar_sub_left]
    abel
  exact sub_eq_zero.mp hdiff

theorem commutator_blockU : ⁅blockU J, J⁆ = blockU J :=
  CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual
    S.short.eq_twoResidual
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J)
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J)

private theorem functional_eq_zero (f : Additive ↥(blockU J) →+ ZMod 2)
    (hf_inv : ∀ (ℓ : ↥J) (u : Additive ↥(blockU J)),
      f (blockConj J (ℓ⁻¹) u) = f u)
    (u : Additive ↥(blockU J)) : f u = 0 := by
  let K : Subgroup ↥(blockU J) := AddSubgroup.toSubgroup' f.ker
  let KG : Subgroup G := K.map (Subgroup.subtype (blockU J))
  have hcomm_le : ⁅blockU J, J⁆ ≤ KG := by
    rw [Subgroup.commutator_le]
    intro u hu ℓ hℓ
    let uA : ↥(blockU J) := ⟨u, hu⟩
    let ℓA : ↥J := ⟨ℓ, hℓ⟩
    have hcA : uA * blockConj J ℓA uA⁻¹ ∈ K := by
      rw [show K = AddSubgroup.toSubgroup' f.ker from rfl, AddSubgroup.mem_toSubgroup',
        AddMonoidHom.mem_ker]
      have h1 : f (Additive.ofMul (uA * blockConj J ℓA uA⁻¹)) =
          f (Additive.ofMul uA) + f (Additive.ofMul (blockConj J ℓA uA⁻¹)) := by
        rw [ofMul_mul, map_add]
      have hc : blockConj J ℓA (Additive.ofMul uA⁻¹) =
          Additive.ofMul (blockConj J ℓA uA⁻¹) := rfl
      have hfinv : f (blockConj J ℓA (Additive.ofMul uA⁻¹)) =
          f (Additive.ofMul uA⁻¹) := by
        have := hf_inv (ℓA⁻¹) (Additive.ofMul uA⁻¹)
        rwa [inv_inv] at this
      rw [h1, ← hc, hfinv, ofMul_inv, map_neg]
      abel
    refine Subgroup.mem_map.mpr ⟨uA * blockConj J ℓA uA⁻¹, hcA, ?_⟩
    show ((uA * blockConj J ℓA uA⁻¹ : ↥(blockU J)) : G) = ⁅u, ℓ⁆
    rw [Subgroup.coe_mul, blockConj_coe, Subgroup.coe_inv, commutatorElement_def]
    simp [uA, ℓA]
    group
  have hU_le_KG : blockU J ≤ KG := by
    rw [← commutator_blockU S]
    exact hcomm_le
  have hmem : (u.toMul : G) ∈ KG := hU_le_KG u.toMul.2
  obtain ⟨cA, hcK, hcG⟩ := Subgroup.mem_map.mp hmem
  have hc_eq : cA = u.toMul := Subtype.ext hcG
  have huK : u.toMul ∈ K := by rwa [hc_eq] at hcK
  rw [show K = AddSubgroup.toSubgroup' f.ker from rfl, AddSubgroup.mem_toSubgroup',
    AddMonoidHom.mem_ker] at huK
  exact huK

theorem blockZ_eq_bot (hH1 : H1Natural m) : blockZ J = ⊥ := by
  classical
  letI : CommGroup ↥(blockU J) := CFSG.Quasithin.commGroupOfElemAbelian S.elemU
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  let zA : ↥(blockU J) := ⟨z, hz.1⟩
  have hzA : zA ≠ 1 := by
    intro h
    exact hz1 (by simpa [zA] using congrArg Subtype.val h)
  have h2 : ∀ a : ↥(blockU J), a ^ 2 = 1 := by
    intro a
    apply Subtype.ext
    simpa using S.elemU.2 a a.2
  obtain ⟨φ, -, hφ⟩ := CFSG.CGT.PushingUpLit.CGT6.exists_hom_ne_one h2
    (⊥ : Subgroup ↥(blockU J)) (by simpa using hzA)
  let φa : Additive ↥(blockU J) →+ ZMod 2 := MonoidHom.toAdditiveLeft φ
  have hφa : φa (Additive.ofMul zA) ≠ 0 := by
    intro h
    apply hφ
    have h' : Multiplicative.toAdd (φ zA) = 0 := by simpa [φa] using h
    rwa [toAdd_eq_zero] at h'
  obtain ⟨w, hw⟩ := exists_polar_w S φa
  obtain ⟨a, ha⟩ := exists_a_of_h1 S hH1 φa w hw
  let f : Additive ↥(blockU J) →+ ZMod 2 := blockFunctional S φa a
  have hf_inv : ∀ (ℓ : ↥J) (u : Additive ↥(blockU J)),
      f (blockConj J (ℓ⁻¹) u) = f u := functional_invariant S φa w a hw ha
  have hβz : blockBeta S (Additive.ofMul zA) = 0 := by
    have hzker : zA ∈ S.beta.ker := by
      rw [S.ker_beta, Subgroup.mem_subgroupOf]
      simpa [zA] using hz
    have h1 : S.beta zA = 1 := MonoidHom.mem_ker.mp hzker
    simpa [blockBeta] using congrArg Multiplicative.toAdd h1
  have hfz : f (Additive.ofMul zA) ≠ 0 := by
    intro h
    apply hφa
    simpa [f, blockFunctional, hβz, QuadraticMap.polar_zero_right] using h
  exact hfz (functional_eq_zero S f hf_inv (Additive.ofMul zA))

end Setting

end CFSG.CGT.Harada80
