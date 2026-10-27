module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.RankThree.PartOne.KC.LinearCommutantSemi

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

variable {n : ℕ} {K : Type} [Field K]

theorem l212in_conjAut_toGL (X : SpecialLinearGroup (Fin n) K) :
    conjAut n K (SpecialLinearGroup.toGL X) = MulAut.conj (proj n K X) := by
  ext y
  obtain ⟨Y, rfl⟩ := proj_surjective n K y
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul, map_inv]

theorem l212in_exists_zpow_units [Finite K] (σ : K ≃+* K) :
    ∃ ρ : ℤ, ∀ x : Kˣ, Units.map (σ : K →+* K) x = x ^ ρ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨ρ, hρ⟩ := mem_zpowers_iff.1 (hg (Units.map (σ : K →+* K) g))
  refine ⟨ρ, fun x => ?_⟩
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 (hg x)
  rw [map_zpow, ← hρ, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]

theorem l212in_det_scalar (c : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) c) = c ^ n := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Units.val_pow_eq_pow_val]

theorem l212in_conjAut_eq_one [Finite K] (hn : 3 ≤ n) (B : GL (Fin n) K)
    (h : conjAut n K B = 1) : ∃ c : Kˣ, GeneralLinearGroup.det B = c ^ n := by
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn B).1 h
  exact ⟨c, by rw [← hc, l212in_det_scalar]⟩

theorem l212in_conjAut_mem_inner (B : GL (Fin n) K)
    (h : ∃ c : Kˣ, GeneralLinearGroup.det B = c ^ n) :
    conjAut n K B ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  obtain ⟨c, hc⟩ := h
  have hdet : GeneralLinearGroup.det (B * (GeneralLinearGroup.scalar (Fin n) c)⁻¹) = 1 := by
    rw [map_mul, map_inv, l212in_det_scalar, hc, mul_inv_cancel]
  obtain ⟨g, hg⟩ : B * (GeneralLinearGroup.scalar (Fin n) c)⁻¹ ∈
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  refine ⟨proj n K g, ?_⟩
  rw [← l212in_conjAut_toGL, hg, map_mul, map_inv, conjAut_scalar, inv_one, mul_one]

theorem l212in_ringAut_comm [Finite K] (σ τ : K ≃+* K) : σ * τ = τ * σ := by
  obtain ⟨p, k, hp, hk⟩ : ∃ (p : ℕ) (k : ℕ+), p.Prime ∧ Nat.card K = p ^ (k : ℕ) := by
    have := Fintype.ofFinite K
    obtain ⟨p, -, k, hp, hk⟩ := FiniteField.card' K
    exact ⟨p, k, hp, by rw [Nat.card_eq_fintype_card, hk]⟩
  obtain ⟨φ, -, -, hφ, -⟩ := finite_field_automorphism_fixed_field_cardinality hp k.pos hk
  have hcyc : ∀ σ : K ≃+* K, ∃ m : ℤ, φ ^ m = σ := fun σ =>
    Subgroup.mem_zpowers_iff.mp (hφ ▸ Subgroup.mem_top σ)
  obtain ⟨a, rfl⟩ := hcyc σ
  obtain ⟨b, rfl⟩ := hcyc τ
  exact zpow_mul_comm φ a b

theorem l212in_comm_mem_range_conjAut [Finite K] (hn : 3 ≤ n) (x y : MulAut (projectiveSL n K)) :
    x * y * x⁻¹ * y⁻¹ ∈ (conjAut n K).range := by
  obtain ⟨hgen, hform⟩ := automorphism_generation (K := K) hn
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hδδ : dualAut n K * dualAut n K = 1 := htrans.2.2.2.1
  have hfδ : ∀ σ : K ≃+* K, Commute (fieldAut n K σ) (dualAut n K) := by
    intro σ
    have h := htrans.2.2.2.2.2.1 σ
    show fieldAut n K σ * dualAut n K = dualAut n K * fieldAut n K σ
    calc fieldAut n K σ * dualAut n K
        = (dualAut n K * fieldAut n K σ * dualAut n K) * dualAut n K := by rw [h]
      _ = dualAut n K * fieldAut n K σ * (dualAut n K * dualAut n K) := by group
      _ = dualAut n K * fieldAut n K σ := by rw [hδδ, mul_one]
  have hD : linearAutGroup n K = (conjAut n K).range := by
    unfold linearAutGroup
    rw [← MonoidHom.coe_range, Subgroup.closure_eq]
  obtain ⟨-, -, hDnorm, -⟩ := standard_outer_quotients (n := n) (K := K)
  rw [hgen] at hDnorm
  have hDn : ((conjAut n K).range).Normal := by
    rw [← hD]
    exact ⟨fun d hd x => hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨x, Subgroup.mem_top x⟩⟩
  let m : MulAut (projectiveSL n K) →* MulAut (projectiveSL n K) ⧸ (conjAut n K).range :=
    QuotientGroup.mk' _
  have hmconj : ∀ A, m (conjAut n K A) = 1 := fun A => (QuotientGroup.eq_one_iff _).2 ⟨A, rfl⟩
  have hform' : ∀ x : MulAut (projectiveSL n K), ∃ (σ : K ≃+* K) (ε : ℕ),
      m x = m (fieldAut n K σ) * m (dualAut n K) ^ ε := by
    intro x
    obtain ⟨A, σ, ε, -, rfl⟩ := hform x
    refine ⟨σ, ε, ?_⟩
    rw [map_mul, map_mul, map_pow, hmconj, one_mul]
  have hcommfield : ∀ σ τ : K ≃+* K, Commute (m (fieldAut n K σ)) (m (fieldAut n K τ)) := by
    intro σ τ
    show m (fieldAut n K σ) * m (fieldAut n K τ) = m (fieldAut n K τ) * m (fieldAut n K σ)
    have h1 : m (fieldAut n K σ) * m (fieldAut n K τ) =
        m (fieldAut n K σ * fieldAut n K τ) := (map_mul m _ _).symm
    have h2 : m (fieldAut n K τ) * m (fieldAut n K σ) =
        m (fieldAut n K τ * fieldAut n K σ) := (map_mul m _ _).symm
    rw [h1, h2, htrans.2.1 σ τ, htrans.2.1 τ σ, l212in_ringAut_comm σ τ]
  have hcommxy : Commute (m x) (m y) := by
    obtain ⟨σ, ε, hx⟩ := hform' x
    obtain ⟨τ, ε', hy⟩ := hform' y
    rw [hx, hy]
    have hσd := (hfδ σ).map m
    have hτd := (hfδ τ).map m
    have h1 : Commute (m (fieldAut n K σ)) (m (fieldAut n K τ) * m (dualAut n K) ^ ε') :=
      (hcommfield σ τ).mul_right (hσd.pow_right ε')
    have h2 : Commute (m (dualAut n K) ^ ε) (m (fieldAut n K τ) * m (dualAut n K) ^ ε') :=
      (hτd.symm.pow_left ε).mul_right ((Commute.refl _).pow_pow ε ε')
    exact h1.mul_left h2
  refine (QuotientGroup.eq_one_iff _).1 ?_
  change m (x * y * x⁻¹ * y⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommxy.eq, mul_inv_cancel_right,
    mul_inv_cancel]

theorem l212in_det_inverseTranspose (B : GL (Fin n) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.inverseTranspose B) =
      (GeneralLinearGroup.det B)⁻¹ := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose,
    Matrix.det_transpose, ← GeneralLinearGroup.val_det_apply, map_inv]

theorem l212in_det_map (σ : K ≃+* K) (B : GL (Fin n) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.map (σ : K →+* K) B) =
      Units.map (σ : K →+* K) (GeneralLinearGroup.det B) := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, Units.coe_map, GeneralLinearGroup.val_det_apply]
  exact (RingHom.map_det (σ : K →+* K) (B : Matrix (Fin n) (Fin n) K)).symm

theorem l212in_scalar_comm (A : GL (Fin n) K) (c : Kˣ) :
    A * GeneralLinearGroup.scalar (Fin n) c = GeneralLinearGroup.scalar (Fin n) c * A := by
  have h : GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.center (GL (Fin n) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.1 h A

theorem l212in_inverseTranspose_scalar (c : Kˣ) :
    GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.scalar (Fin n) c⁻¹ := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.coe_inverseTranspose, ← map_inv, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_transpose]

theorem l212in_scalar_action (A : GL (Fin n) K) (σ : K ≃+* K) (ρ : ℤ)
    (hρ : ∀ x : Kˣ, Units.map (σ : K →+* K) x = x ^ ρ) {z : SpecialLinearGroup (Fin n) K}
    (hz : z ∈ scalars n K) :
    CatalogueBHigherLinearAction.slConjugation n K A z = z ∧
      CatalogueBHigherLinearField.slFieldAut (Fin n) K σ z = z ^ ρ ∧
        CatalogueBGraphForm.slGraphAut n K z = z⁻¹ := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hz
  have hzc : SpecialLinearGroup.toGL z = GeneralLinearGroup.scalar (Fin n) c :=
    Units.ext (by rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]; exact hc)
  refine ⟨?_, ?_, ?_⟩
  · apply SpecialLinearGroup.toGL_injective
    rw [CatalogueBHigherLinearAction.toGL_slConjugation, hzc, l212in_scalar_comm A c,
      mul_inv_cancel_right]
  · apply SpecialLinearGroup.toGL_injective
    change SpecialLinearGroup.toGL (CatalogueBHigherLinearField.slFieldEquiv (Fin n) σ z) = _
    rw [CatalogueBHigherLinearField.toGL_slFieldEquiv,
      map_zpow (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K) z ρ, hzc,
      CatalogueBHigherLinearField.glFieldEquiv_scalar,
      show Units.map σ.toMonoidHom c = Units.map (σ : K →+* K) c from rfl, hρ,
      ← map_zpow (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) c ρ]
  · apply SpecialLinearGroup.toGL_injective
    rw [CatalogueBGraphForm.toGL_slGraphAut, map_inv, hzc]
    exact (l212in_inverseTranspose_scalar c).trans
      (map_inv (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) c).symm

theorem l212in_lift_linear [Finite K] (hn : 3 ≤ n) (α : MulAut (projectiveSL n K)) :
    ∃ (κ : ℤ) (Ã : SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K)
      (t : GL (Fin n) K → GL (Fin n) K),
      (∀ s, proj n K (Ã s) = α (proj n K s)) ∧
      (∀ s ∈ (proj n K).ker, Ã s = s ^ κ) ∧
      (∀ B, α * conjAut n K B * α⁻¹ = conjAut n K (t B)) ∧
      (∀ B, GeneralLinearGroup.det (t B) = GeneralLinearGroup.det B ^ κ) := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform α
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hδδ : dualAut n K * dualAut n K = 1 := htrans.2.2.2.1
  have hδinv : (dualAut n K)⁻¹ = dualAut n K := inv_eq_of_mul_eq_one_right hδδ
  obtain ⟨ρ, hρ⟩ := l212in_exists_zpow_units σ
  have hα : conjAut n K A * fieldAut n K σ * dualAut n K ^ ε =
      descendAut n K (CatalogueBHigherLinearAction.slConjugation n K A *
        CatalogueBHigherLinearField.slFieldAut (Fin n) K σ *
          CatalogueBGraphForm.slGraphAut n K ^ ε) := by
    rw [map_mul, map_mul, map_pow]
    rfl
  have hkerz : ∀ z ∈ (proj n K).ker,
      CatalogueBHigherLinearAction.slConjugation n K A z = z ∧
        CatalogueBHigherLinearField.slFieldAut (Fin n) K σ z = z ^ ρ ∧
          CatalogueBGraphForm.slGraphAut n K z = z⁻¹ := by
    intro z hz
    rw [ker_proj] at hz
    exact l212in_scalar_action A σ ρ hρ hz
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · refine ⟨ρ, (CatalogueBHigherLinearAction.slConjugation n K A *
      CatalogueBHigherLinearField.slFieldAut (Fin n) K σ).toMonoidHom,
      fun B => A * GeneralLinearGroup.map (σ : K →+* K) B * A⁻¹, ?_, ?_, ?_, ?_⟩
    · intro s
      rw [hα, descendAut_proj]
      simp
    · intro s hs
      obtain ⟨h1, h2, -⟩ := hkerz s hs
      show CatalogueBHigherLinearAction.slConjugation n K A
        (CatalogueBHigherLinearField.slFieldAut (Fin n) K σ s) = s ^ ρ
      rw [h2, map_zpow, h1]
    · intro B
      rw [pow_zero, mul_one]
      calc conjAut n K A * fieldAut n K σ * conjAut n K B *
            (conjAut n K A * fieldAut n K σ)⁻¹
          = conjAut n K A * (fieldAut n K σ * conjAut n K B * (fieldAut n K σ)⁻¹) *
            (conjAut n K A)⁻¹ := by group
        _ = conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K) B * A⁻¹) := by
          rw [htrans.2.2.1 σ B, map_mul, map_mul, map_inv]
    · intro B
      rw [map_mul, map_mul, map_inv, l212in_det_map, hρ, mul_right_comm, mul_inv_cancel,
        one_mul]
  · refine ⟨-ρ, (CatalogueBHigherLinearAction.slConjugation n K A *
      CatalogueBHigherLinearField.slFieldAut (Fin n) K σ *
        CatalogueBGraphForm.slGraphAut n K).toMonoidHom,
      fun B => A * GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose B) * A⁻¹, ?_, ?_, ?_, ?_⟩
    · intro s
      rw [hα, descendAut_proj]
      simp
    · intro s hs
      obtain ⟨h1, h2, h3⟩ := hkerz s hs
      show CatalogueBHigherLinearAction.slConjugation n K A
        (CatalogueBHigherLinearField.slFieldAut (Fin n) K σ
          (CatalogueBGraphForm.slGraphAut n K s)) = s ^ (-ρ)
      rw [h3, map_inv, h2, map_inv, map_zpow, h1, _root_.zpow_neg]
    · intro B
      rw [pow_one]
      calc conjAut n K A * fieldAut n K σ * dualAut n K * conjAut n K B *
            (conjAut n K A * fieldAut n K σ * dualAut n K)⁻¹
          = conjAut n K A * (fieldAut n K σ * (dualAut n K * conjAut n K B * dualAut n K) *
            (fieldAut n K σ)⁻¹) * (conjAut n K A)⁻¹ := by
            rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hδinv]
            group
        _ = conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K)
            (GeneralLinearGroup.inverseTranspose B) * A⁻¹) := by
          rw [htrans.2.2.2.2.1 B, htrans.2.2.1 σ _, map_mul, map_mul, map_inv]
    · intro B
      rw [map_mul, map_mul, map_inv, l212in_det_map, l212in_det_inverseTranspose, map_inv, hρ,
        mul_right_comm, mul_inv_cancel, one_mul, _root_.zpow_neg]

end CFSG.LocalAnalysis.RankFourTheoremC
