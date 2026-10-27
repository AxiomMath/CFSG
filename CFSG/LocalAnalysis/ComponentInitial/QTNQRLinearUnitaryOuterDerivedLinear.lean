module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.Walter.W67.JR.OutPSL

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OuterDerived

open Matrix LinearFlag CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {K : Type} [Field K] {n : ℕ}

theorem linear_diagonal_outer [Finite K] (hn : 1 ≤ n) :
    IsCyclic ((QuotientGroup.mk' (inner (projectiveSL n K))).comp (conjAut n K)).range ∧
      Nat.card ((QuotientGroup.mk' (inner (projectiveSL n K))).comp (conjAut n K)).range ∣
        Nat.gcd n (Nat.card K - 1) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set φ := (QuotientGroup.mk' (inner (projectiveSL n K))).comp (conjAut n K) with hφ
  have hle : (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker ≤ φ.ker := by
    intro A hA
    obtain ⟨g, rfl⟩ : A ∈ (SpecialLinearGroup.toGL :
        SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
      rw [SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hA
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, conjAut_toGL, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ⟨_, rfl⟩
  have hdet : Function.Surjective (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ) :=
    GeneralLinearGroup.det_surjective
  set ψ : Kˣ →* Outer (projectiveSL n K) := (QuotientGroup.lift _ φ hle).comp
    (QuotientGroup.quotientKerEquivOfSurjective _ hdet).symm.toMonoidHom
  have hψ : ∀ A, ψ (GeneralLinearGroup.det A) = φ A := fun A => by
    have e : (QuotientGroup.quotientKerEquivOfSurjective _ hdet).symm
        (GeneralLinearGroup.det A) =
        (A : GL (Fin n) K ⧸ (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    change QuotientGroup.lift _ φ hle
      ((QuotientGroup.quotientKerEquivOfSurjective _ hdet).symm (GeneralLinearGroup.det A)) = _
    rw [e, QuotientGroup.lift_mk]
  have hrange : φ.range = ψ.range := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨_, hψ A⟩
    · rintro ⟨u, rfl⟩
      obtain ⟨A, rfl⟩ := hdet u
      exact ⟨A, (hψ A).symm⟩
  have hpow : (powMonoidHom n : Kˣ →* Kˣ).range ≤ ψ.ker := by
    rintro _ ⟨u, rfl⟩
    have hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) u) =
        powMonoidHom n u := by
      rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, powMonoidHom_apply]
    rw [MonoidHom.mem_ker, ← hdet, hψ, hφ, MonoidHom.comp_apply, conjAut_scalar, map_one]
  rw [hrange]
  refine ⟨isCyclic_of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective, ?_⟩
  rw [← Subgroup.index_ker]
  exact (Subgroup.index_dvd_of_le hpow).trans (UnitaryHigher.index_powRange_dvd_gcd n)

theorem commutator_mem_linearAutGroup [Finite K] (hn : 3 ≤ n) (α β : MulAut (projectiveSL n K)) :
    α * β * α⁻¹ * β⁻¹ ∈ linearAutGroup n K := by
  obtain ⟨-, -, hDnorm, -⟩ := standard_outer_quotients (n := n) (K := K)
  obtain ⟨hR, hgen⟩ := automorphism_generation (K := K) hn
  rw [hR] at hDnorm
  have : (linearAutGroup n K).Normal := ⟨fun d hd g =>
    hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨g, Subgroup.mem_top g⟩⟩
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have hcommK : ∀ σ τ : K ≃+* K, σ * τ = τ * σ := fun σ τ =>
    (IsCyclic.isMulCommutative (α := K ≃+* K)).is_comm.comm σ τ
  set π := QuotientGroup.mk' (linearAutGroup n K)
  set δ := dualAut n K
  have hform : ∀ α : MulAut (projectiveSL n K), ∃ (σ : K ≃+* K) (ε : ℕ),
      π α = π (fieldAut n K σ) * π δ ^ ε := by
    intro α
    obtain ⟨A, σ, ε, -, rfl⟩ := hgen α
    refine ⟨σ, ε, ?_⟩
    rw [map_mul, map_mul, map_pow, show π (conjAut n K A) = 1 from
      (QuotientGroup.eq_one_iff _).2 (conjAut_mem_linearAutGroup A), one_mul]
  have hff : ∀ σ τ : K ≃+* K, Commute (π (fieldAut n K σ)) (π (fieldAut n K τ)) := by
    intro σ τ
    change π _ * π _ = π _ * π _
    rw [← map_mul π, ← map_mul π, htrans.2.1, htrans.2.1, hcommK]
  have hfδ : ∀ σ : K ≃+* K, Commute (π (fieldAut n K σ)) (π δ) := by
    intro σ
    have h : fieldAut n K σ * δ = δ * fieldAut n K σ := by
      calc fieldAut n K σ * δ = δ * fieldAut n K σ * δ * δ := by rw [htrans.2.2.2.2.2.1]
        _ = δ * fieldAut n K σ := by rw [mul_assoc _ δ δ, htrans.2.2.2.1, mul_one]
    change π _ * π _ = π _ * π _
    rw [← map_mul π, ← map_mul π, h]
  obtain ⟨σ, ε, hα⟩ := hform α
  obtain ⟨τ, η, hβ⟩ := hform β
  have hc : Commute (π α) (π β) := by
    rw [hα, hβ]
    exact ((hff σ τ).mul_right ((hfδ σ).pow_right η)).mul_left
      (((hfδ τ).symm.pow_left ε).mul_right ((Commute.refl (π δ)).pow_pow ε η))
  have h1 : π (α * β * α⁻¹ * β⁻¹) = 1 := by
    rw [map_mul π, map_mul π, map_mul π, map_inv π, map_inv π, hc.eq, mul_inv_cancel_right,
      mul_inv_cancel]
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem exists_linear_outer_diagonal [Finite K] (hn : 3 ≤ n) :
    ∃ N : Subgroup (Outer (projectiveSL n K)), IsCyclic N ∧
      Nat.card N ∣ Nat.gcd n (Nat.card K - 1) ∧
      ∀ a b : Outer (projectiveSL n K), a * b * a⁻¹ * b⁻¹ ∈ N := by
  obtain ⟨hcyc, hcard⟩ := linear_diagonal_outer (K := K) (n := n) (by omega)
  refine ⟨_, hcyc, hcard, fun a b => ?_⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp (commutator_mem_linearAutGroup hn α β)
  exact ⟨A, by rw [MonoidHom.comp_apply, hA]; rfl⟩

theorem semilinearQuotient_mul_comm (K : Type) [Field K] [Finite K]
    (x y : SemilinearQuotient K) : x * y = y * x := by
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have hdvd : Nat.card (quotientFieldProjection K).ker ∣ 2 := by
    rw [quotientFieldProjection_ker, ← Subgroup.index_ker]
    have hle : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range ≤
        (diagonalHom K).ker := by
      rintro _ ⟨y, rfl⟩
      rw [MonoidHom.mem_ker]
      change QuotientGroup.mk' (pGammaL2PSLRange K)
        (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (mem_pGammaL2PSLRange_iff K _).mpr ⟨y, rfl⟩
    refine (Subgroup.index_dvd_of_le hle).trans ?_
    rw [Subgroup.index_eq_card]
    exact (card_pgl_quotient_psl_dvd K).trans (Nat.gcd_dvd_left 2 _)
  exact ((quotientFieldProjection K).isMulCommutative_of_isCyclic_of_ker_le_center
    (Walter.W67.JROut.le_center_of_card_dvd_two hdvd)).is_comm.comm x y

theorem outer_psl2_mul_comm (K : Type) [Field K] [Finite K] (a b : Outer (PSL2 K)) :
    a * b = b * a := by
  set e : SemilinearQuotient K ≃* Outer (PSL2 K) := (semilinearQuotientEquivCoordinateEG K).trans
    ((coordinateOuterQuotientEquiv K).trans (coordinateOuterEquivPSL K))
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  rw [← map_mul, ← map_mul, semilinearQuotient_mul_comm]

end CFSG.LocalAnalysis.ComponentInitial.OuterDerived
