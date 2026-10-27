module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticRepresentation

open Matrix Module Submodule CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)

variable {r : ℕ} {K : Type} [Field K]

theorem coord_single (σ : K ≃+* K) (i : Fin r ⊕ Fin r) :
    (fun j => σ ((Pi.single i (1 : K) : Fin r ⊕ Fin r → K) j)) = Pi.single i 1 := by
  classical
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem eq_one_and_scalar_of_forall_line (hr : 1 ≤ r) (A : GL (Fin r ⊕ Fin r) K)
    (σ : K ≃+* K)
    (h : ∀ v : Fin r ⊕ Fin r → K, v ≠ 0 →
      ∃ μ : K, (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (fun i => σ (v i)) = μ • v) :
    σ = 1 ∧ ∃ c : Kˣ, A = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
  classical
  set M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := A.val with hMdef
  have hsingle : ∀ i : Fin r ⊕ Fin r, (Pi.single i (1 : K) : Fin r ⊕ Fin r → K) ≠ 0 :=
    fun i h0 => (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h0 i)
  have hcol : ∀ i, ∃ μ : K, M *ᵥ Pi.single i 1 = μ • Pi.single i 1 := by
    intro i
    obtain ⟨μ, hμ⟩ := h (Pi.single i 1) (hsingle i)
    rw [coord_single] at hμ
    exact ⟨μ, hμ⟩
  choose μ hμ using hcol
  let i₀ : Fin r ⊕ Fin r := Sum.inl ⟨0, hr⟩
  let j₀ : Fin r ⊕ Fin r := Sum.inr ⟨0, hr⟩
  have hij : i₀ ≠ j₀ := Sum.inl_ne_inr
  have hconst : ∀ i, μ i = μ i₀ := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
    have hne : (Pi.single i (1 : K) + Pi.single i₀ 1 : Fin r ⊕ Fin r → K) ≠ 0 := by
      intro h0
      have := congrFun h0 i
      simp [Pi.single_eq_of_ne hi] at this
    obtain ⟨ν, hν⟩ := h _ hne
    have hσ : (fun j => σ ((Pi.single i (1 : K) + Pi.single i₀ 1 : Fin r ⊕ Fin r → K) j)) =
        Pi.single i 1 + Pi.single i₀ 1 := by
      ext j
      simp only [Pi.add_apply, map_add]
      rw [congrFun (coord_single σ i) j, congrFun (coord_single σ i₀) j]
    rw [hσ, mulVec_add, hμ, hμ] at hν
    have h1 := congrFun hν i
    have h2 := congrFun hν i₀
    simp [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne (Ne.symm hi)] at h1 h2
    rw [h1, h2]
  have hM : M = Matrix.scalar (Fin r ⊕ Fin r) (μ i₀) := by
    ext k i
    have hk := congrFun (hμ i) k
    rw [mulVec_single_one, hconst i] at hk
    rw [show M k i = M.col i k from rfl, hk]
    by_cases hki : k = i
    · subst hki
      simp
    · simp [hki]
  have hμ0 : μ i₀ ≠ 0 := by
    intro h0
    have hone : ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * M =
        1 := by
      rw [hMdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hM, h0, Matrix.scalar_apply, diagonal_zero, Matrix.mul_zero] at hone
    have := congrFun (congrFun hone i₀) i₀
    simp at this
  have hσ : σ = 1 := by
    ext c
    have hne : (Pi.single i₀ (1 : K) + c • Pi.single j₀ 1 : Fin r ⊕ Fin r → K) ≠ 0 := by
      intro h0
      have := congrFun h0 i₀
      simp at this
    obtain ⟨ν, hν⟩ := h _ hne
    rw [hM] at hν
    have h1 := congrFun hν i₀
    have h2 := congrFun hν j₀
    simp [Matrix.scalar_apply, mulVec_diagonal] at h1 h2
    rw [← h1] at h2
    exact mul_left_cancel₀ hμ0 h2
  refine ⟨hσ, Units.mk0 (μ i₀) hμ0, ?_⟩
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar]
  exact hM

theorem conjAut_mul_fieldAut_eq_one_iff [Finite K] (hr : 1 ≤ r) (A : gsp r K) (σ : K ≃+* K) :
    conjAut r K A * fieldAut r K σ = 1 ↔
      σ = 1 ∧ ∃ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
  classical
  constructor
  · intro h
    obtain ⟨p, hchar⟩ := CharP.exists K
    have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
    obtain ⟨-, -, hinj⟩ := maximal_parabolics (K := K) p hr
    apply eq_one_and_scalar_of_forall_line hr
    intro v hv
    have hL := map_projStabilizer_conjAut_mul_fieldAut A σ (span K {v})
    rw [h, spCoordImage_span_singleton, Submodule.map_span, Set.image_singleton,
      mulVecLin_apply] at hL
    have h1 : (projStabilizer r K (span K {v})).map
        (1 : MulAut (StatedProj (StatedSp r K))).toMonoidHom = projStabilizer r K (span K {v}) :=
      Subgroup.map_id _
    rw [h1] at hL
    have hw : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (fun i => σ (v i)) ≠ 0 :=
      mulVec_ne_zero_of_ne_zero (A : GL (Fin r ⊕ Fin r) K) (coord_ne_zero σ hv)
    have hiso : ∀ u : Fin r ⊕ Fin r → K, u ≠ 0 →
        IsTotallyIsotropic (pairedSympForm K r) (span K {u}) :=
      fun u hu => isTotallyIsotropic_line (SpPoint.ofVec u hu)
    have heq := hinj (span K {v}) (span K {_}) (by simpa using hv) (hiso v hv)
      (by simpa using hw) (hiso _ hw) hL
    have hmem : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (fun i => σ (v i)) ∈ span K {v} := heq ▸ mem_span_singleton_self _
    obtain ⟨μ, hμ⟩ := mem_span_singleton.mp hmem
    exact ⟨μ, hμ.symm⟩
  · rintro ⟨rfl, c, hc⟩
    rw [map_one, mul_one]
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective x
    rw [conjAut_proj]
    change proj r K (conjSp r K A g) = proj r K g
    congr 1
    apply Subtype.ext
    rw [coe_conjSp, hc]
    have hcomm : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c * (g : GL (Fin r ⊕ Fin r) K) =
        (g : GL (Fin r ⊕ Fin r) K) * GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
      exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq
    rw [hcomm, mul_inv_cancel_right]

theorem conjAut_mul_fieldAut_mul_self (A : gsp r K) (σ : K ≃+* K) :
    conjAut r K A * fieldAut r K σ * (conjAut r K A * fieldAut r K σ) =
      conjAut r K (A * gspFieldMap σ A) * fieldAut r K (σ * σ) := by
  rw [map_mul, map_mul, ← fieldAut_mul_conjAut_mul_inv σ A]
  group

theorem involution_facts [Finite K] (hr : 1 ≤ r) (A : gsp r K) (σ : K ≃+* K)
    (h2 : conjAut r K A * fieldAut r K σ * (conjAut r K A * fieldAut r K σ) = 1)
    (h1 : conjAut r K A * fieldAut r K σ ≠ 1) :
    σ ^ 2 = 1 ∧
      (∃ d : Kˣ, (A : GL (Fin r ⊕ Fin r) K) * glFieldEquiv (Fin r ⊕ Fin r) σ A =
        GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d) ∧
      (σ = 1 → ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c) ∧
      (σ ≠ 1 → Nat.card K = Nat.card {c : K // σ c = c} ^ 2 ∧
        ∀ τ : K ≃+* K, τ ^ 2 = 1 → τ ≠ 1 → τ = σ) := by
  rw [conjAut_mul_fieldAut_mul_self] at h2
  obtain ⟨hσσ, d, hd⟩ := (conjAut_mul_fieldAut_eq_one_iff hr _ _).mp h2
  have hsq : σ ^ 2 = 1 := by rw [sq]; exact hσσ
  refine ⟨hsq, ⟨d, ?_⟩, fun hσ c hc => h1 ((conjAut_mul_fieldAut_eq_one_iff hr _ _).mpr
    ⟨hσ, c, hc⟩), fun hσ => ?_⟩
  · rw [← hd]
    rfl
  · let := Fintype.ofFinite K
    obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
    exact CatalogueBOrthogonalInvolutionRepresentation.field_involution_facts hp n.pos
      (by rw [Nat.card_eq_fintype_card, hcard]) hsq hσ

theorem involution_representative [Finite K] (hr : 1 ≤ r)
    (hgen : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ (A : gsp r K) (σ : K ≃+* K),
      α = conjAut r K A * fieldAut r K σ)
    (α : MulAut (StatedProj (StatedSp r K))) (h2 : α * α = 1) (h1 : α ≠ 1) :
    ∃ (A : gsp r K) (σ : K ≃+* K), α = conjAut r K A * fieldAut r K σ ∧ σ ^ 2 = 1 ∧
      (∃ d : Kˣ, (A : GL (Fin r ⊕ Fin r) K) * glFieldEquiv (Fin r ⊕ Fin r) σ A =
        GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d) ∧
      (σ = 1 → ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c) ∧
      (σ ≠ 1 → Nat.card K = Nat.card {c : K // σ c = c} ^ 2 ∧
        ∀ τ : K ≃+* K, τ ^ 2 = 1 → τ ≠ 1 → τ = σ) := by
  obtain ⟨A, σ, rfl⟩ := hgen α
  exact ⟨A, σ, rfl, involution_facts hr A σ h2 h1⟩

end CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
