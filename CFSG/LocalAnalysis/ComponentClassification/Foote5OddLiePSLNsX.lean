module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponentQuadratic
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTransport

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

theorem exists_smul_of_commute_transvection {E : Type*} [Field E] {m : ℕ} (hm : 2 ≤ m)
    (γ : (Fin m → E) →+ (Fin m → E))
    (hγ : ∀ (i j : Fin m) (hij : i ≠ j) (t : E) (w : Fin m → E),
      γ ((SpecialLinearGroup.transvection hij t : Matrix (Fin m) (Fin m) E) *ᵥ w) =
        (SpecialLinearGroup.transvection hij t : Matrix (Fin m) (Fin m) E) *ᵥ γ w) :
    ∃ a : E, ∀ w, γ w = a • w := by
  classical
  have htr : ∀ (i j : Fin m) (hij : i ≠ j) (t : E) (w : Fin m → E),
      (SpecialLinearGroup.transvection hij t : Matrix (Fin m) (Fin m) E) *ᵥ w =
        w + Pi.single i (t * w j) := by
    intro i j hij t w
    rw [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec]
    congr 1
  have h1 : ∀ (i j : Fin m), i ≠ j → ∀ t : E,
      γ (Pi.single i t) = Pi.single i (t * γ (Pi.single j 1) j) := by
    intro i j hij t
    have h := hγ i j hij t (Pi.single j 1)
    rw [htr, htr, map_add] at h
    have h' := add_left_cancel h
    simpa using h'
  set j₀ : Fin m := ⟨0, by omega⟩ with hj₀
  set j₁ : Fin m := ⟨1, by omega⟩ with hj₁
  have h01 : j₁ ≠ j₀ := by simp [hj₀, hj₁, Fin.ext_iff]
  set a := γ (Pi.single j₀ 1) j₀ with ha
  have hsingle : ∀ (i : Fin m) (t : E), γ (Pi.single i t) = Pi.single i (t * a) := by
    intro i t
    by_cases hi : i = j₀
    · rw [hi, h1 j₀ j₁ h01.symm t, h1 j₁ j₀ h01 1]
      simp [ha]
    · exact h1 i j₀ hi t
  refine ⟨a, fun w => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]
  simp only [hsingle]
  ext k
  simp [Finset.sum_apply, Pi.single_apply, mul_comm]

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem exists_nonsplit_component (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) (A : GL (Fin n) K) (c : Kˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin n) c) (hns : ¬ IsSquare (c : K)) :
    ∃ X : Subgroup SL(n, K),
      Open.IsComponentOf X (CFSG.ClassicalInvolution.Balance.fixedGroup (slConjugation n K A)) ∧
      ∀ β₁ β₂ : (Fin n → K) →+ (Fin n → K),
        (∀ x ∈ X, ∀ v, β₁ ((x : Matrix (Fin n) (Fin n) K) *ᵥ v) =
          (x : Matrix (Fin n) (Fin n) K) *ᵥ β₁ v) →
        (∀ x ∈ X, ∀ v, β₂ ((x : Matrix (Fin n) (Fin n) K) *ᵥ v) =
          (x : Matrix (Fin n) (Fin n) K) *ᵥ β₂ v) →
        (∀ (k : K) v, β₁ (k • v) = k • β₁ v) ∧ ∀ v, β₁ (β₂ v) = β₂ (β₁ v) := by
  have : Fact (¬ IsSquare c.val) := ⟨hns⟩
  have : Finite (extension c.val) := Module.finite_of_finite K
  let := matrixModule A c hsq
  set E := extension c.val with hE
  set m := matrixDimension A c hsq with hm
  have hnm : n = 2 * m := by simpa using matrixDimension_twice A c hsq
  have hm2 : 2 ≤ m := by omega
  have hcardE : Nat.card E = Nat.card K ^ 2 := by
    let : Fintype K := Fintype.ofFinite K
    let : Fintype E := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K),
      extension_finrank]
  have hK3 := CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspace.three_le_card_of_two_ne_zero
    h2
  have hE9 : 9 ≤ Nat.card E := by
    rw [hcardE]
    nlinarith
  have h22 : m ≠ 2 ∨ Nat.card E ≠ 2 := Or.inr (by omega)
  have h23 : m ≠ 2 ∨ Nat.card E ≠ 3 := Or.inr (by omega)
  have hperf := CatalogueBGeneralLinear.specialLinear_perfect m E hm2 h22 h23
  have hqs := CatalogueBGeneralLinear.specialLinear_quasisimple m E hm2 h22 h23
  set Φ := matrixCentralizerQuadraticEquiv A c hsq with hΦ
  set g : SL(m, E) →* GL (Fin n) K := (centralizer {A}).subtype.comp
    (Φ.symm.toMonoidHom.comp SpecialLinearGroup.toGL) with hg
  have hgapp : ∀ s, g s = (Φ.symm (SpecialLinearGroup.toGL s) : GL (Fin n) K) := fun s => rfl
  have hdet : ∀ s, ((g s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    intro s
    have h := Abelianization.commutator_subset_ker (GeneralLinearGroup.det.comp g)
      (Group.IsPerfect.mem_commutator (g := s))
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at h
    have := congrArg Units.val h
    simpa using this
  let j : SL(m, E) →* SL(n, K) :=
    { toFun := fun s => ⟨(g s : Matrix (Fin n) (Fin n) K), hdet s⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        change (g (a * b) : Matrix (Fin n) (Fin n) K) = (g a : Matrix (Fin n) (Fin n) K) * g b
        rw [map_mul, Units.val_mul] }
  have hj : ∀ s, ((j s : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      (g s : Matrix (Fin n) (Fin n) K) := fun s => rfl
  have hginj : Function.Injective g := by
    intro a b h
    rw [hgapp, hgapp] at h
    exact SpecialLinearGroup.toGL_injective (Φ.symm.injective (Subtype.ext h))
  have hjinj : Function.Injective j := fun a b h =>
    hginj (Units.ext (by rw [← hj, ← hj, h]))
  set X := j.range with hX
  set F := CFSG.ClassicalInvolution.Balance.fixedGroup (slConjugation n K A) with hF
  have hcent : ∀ s, A * g s = g s * A := fun s =>
    mem_centralizer_iff.mp (Φ.symm (SpecialLinearGroup.toGL s)).2 A (Set.mem_singleton A)
  have hXF : X ≤ F := by
    rintro _ ⟨s, rfl⟩
    rw [hF, CFSG.ClassicalInvolution.Balance.mem_fixedGroup]
    apply Subtype.ext
    rw [slConjugation_matrix, hj]
    have h1 : A * g s * A⁻¹ = g s := by rw [hcent s]; group
    have := congrArg Units.val h1
    simpa using this
  have hXn : ∀ y ∈ F, ∀ x ∈ X, y * x * y⁻¹ ∈ X := by
    rintro y hy _ ⟨s, rfl⟩
    have hyc : SpecialLinearGroup.toGL y ∈ centralizer ({A} : Set (GL (Fin n) K)) := by
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have h1 := congrArg SpecialLinearGroup.toGL
        (CFSG.ClassicalInvolution.Balance.mem_fixedGroup.mp hy)
      rw [toGL_slConjugation] at h1
      calc _ = A * SpecialLinearGroup.toGL y * A⁻¹ * A := by group
        _ = SpecialLinearGroup.toGL y * A := by rw [h1]
    set Y := Φ ⟨_, hyc⟩ with hY
    have hdetY : GeneralLinearGroup.det (Y * SpecialLinearGroup.toGL s * Y⁻¹) = 1 := by
      have hs : GeneralLinearGroup.det (SpecialLinearGroup.toGL s) = 1 :=
        Units.ext (by simp)
      rw [map_mul, map_mul, map_inv, hs, mul_one, mul_inv_cancel]
    let s' : SL(m, E) := ⟨(Y * SpecialLinearGroup.toGL s * Y⁻¹ : GL (Fin m) E),
      by rw [← GeneralLinearGroup.val_det_apply, hdetY, Units.val_one]⟩
    have hs' : SpecialLinearGroup.toGL s' = Y * SpecialLinearGroup.toGL s * Y⁻¹ :=
      Units.ext rfl
    have e1 : ∀ z, SpecialLinearGroup.toGL (j z) = g z := fun z => Units.ext rfl
    refine ⟨s', SpecialLinearGroup.toGL_injective ?_⟩
    rw [e1, hgapp, hs', map_mul, map_mul, map_inv, hY, MulEquiv.symm_apply_apply, map_mul,
      map_mul, map_inv, e1, hgapp]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hXqs : Open.IsQuasisimple X := by
    have e : SL(m, E) ≃* X := MonoidHom.ofInjective hjinj
    have hq' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqs
    exact (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq')
  have hXcomp : Open.IsComponentOf X F := by
    refine ⟨hXF, Open.IsSubnormal.step hXF ?_ (Open.IsSubnormal.refl F), hXqs⟩
    rw [normal_subgroupOf_iff hXF]
    intro x y hx hy
    exact hXn y hy x hx
  set b := matrixBasis A c hsq with hb
  have key : ∀ β : (Fin n → K) →+ (Fin n → K),
      (∀ x ∈ X, ∀ v, β ((x : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        (x : Matrix (Fin n) (Fin n) K) *ᵥ β v) → ∃ a : E, ∀ v, β v = a • v := by
    intro β hβ
    let γ : (Fin m → E) →+ (Fin m → E) :=
      b.equivFun.toLinearMap.toAddMonoidHom.comp
        (β.comp b.equivFun.symm.toLinearMap.toAddMonoidHom)
    have hγapp : ∀ w, γ w = b.equivFun (β (b.equivFun.symm w)) := fun w => rfl
    have hcoord : ∀ (s : SL(m, E)) v, (s : Matrix (Fin m) (Fin m) E) *ᵥ b.equivFun v =
        b.equivFun ((j s : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
      intro s v
      have h := matrixCentralizerQuadraticEquiv_mulVec A c hsq
        (Φ.symm (SpecialLinearGroup.toGL s)) v
      rw [MulEquiv.apply_symm_apply] at h
      exact h
    have hγ : ∀ (i j' : Fin m) (hij : i ≠ j') (t : E) (w : Fin m → E),
        γ ((SpecialLinearGroup.transvection hij t : Matrix (Fin m) (Fin m) E) *ᵥ w) =
          (SpecialLinearGroup.transvection hij t : Matrix (Fin m) (Fin m) E) *ᵥ γ w := by
      intro i j' hij t w
      obtain ⟨v, rfl⟩ := b.equivFun.surjective w
      rw [hγapp, hγapp, hcoord, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
        hβ _ ⟨_, rfl⟩, hcoord]
    obtain ⟨a, ha⟩ := exists_smul_of_commute_transvection hm2 γ hγ
    refine ⟨a, fun v => ?_⟩
    have h := ha (b.equivFun v)
    rw [hγapp, LinearEquiv.symm_apply_apply] at h
    apply b.equivFun.injective
    rw [h, map_smul]
  refine ⟨X, hXcomp, fun β₁ β₂ h₁ h₂ => ?_⟩
  obtain ⟨a₁, ha₁⟩ := key β₁ h₁
  obtain ⟨a₂, ha₂⟩ := key β₂ h₂
  refine ⟨fun k v => ?_, fun v => ?_⟩
  · rw [ha₁, ha₁]
    calc a₁ • (k • v) = a₁ • (algebraMap K E k • v) := by
          rw [matrixModule_algebraMap_smul A c hsq k v]
      _ = algebraMap K E k • (a₁ • v) := by rw [smul_smul, smul_smul, mul_comm]
      _ = k • (a₁ • v) := matrixModule_algebraMap_smul A c hsq k _
  · rw [ha₂, ha₁, ha₁, ha₂, smul_smul, smul_smul, mul_comm]

end CFSG.ComponentClassification.Foote5.OddLieCore
