module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzUE

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.LinkPSUAux

open CFSG.Open CFSG.SectionRank.EvenCover
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz

section Cover

theorem exists_cover
    {K : Type} [Field K] [Finite K] {f d : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hd : 3 ≤ d) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {Lb : Type} [Group Lb] [Finite Lb] [Group.IsPerfect Lb]
    (π₀ : Lb →* StatedProj (StatedSU d (2 ^ f) K)) (hπ₀ : Function.Surjective π₀)
    (hc : π₀.ker ≤ Subgroup.center Lb) (hk : IsPGroup r π₀.ker) :
    ∃ φ : StatedSU d (2 ^ f) K →* Lb, Function.Surjective φ ∧
      ∀ g, π₀ (φ g) = QuotientGroup.mk g := by
  classical
  set θ : StatedSU d (2 ^ f) K →* StatedProj (StatedSU d (2 ^ f) K) :=
    QuotientGroup.mk' _ with hθ
  have hθs : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hP : IsPGroup r (pullbackFst π₀ θ).ker := by
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.1 hk)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hr).1 (hn ▸ card_pullbackFst_ker_dvd π₀ θ)
    exact IsPGroup.of_card hm
  obtain ⟨σ, hσ⟩ := CFSG.StandardType.ggPSections_su hK hf hd hr hr2 (pullback π₀ θ)
    (pullbackFst π₀ θ) (pullbackFst_surjective hπ₀ θ) (pullbackFst_ker_le_center hc θ) hP
  set φ : StatedSU d (2 ^ f) K →* Lb :=
    (MonoidHom.snd _ _).comp ((pullback π₀ θ).subtype.comp σ) with hφ
  have hφθ : ∀ g, π₀ (φ g) = θ g := fun g => congrArg (· g) (comp_snd_section σ hσ)
  refine ⟨φ, ?_, hφθ⟩
  rw [← MonoidHom.range_eq_top]
  refine eq_top_of_forall_mul_center fun x => ?_
  obtain ⟨g, hg⟩ := hθs (π₀ x)
  refine ⟨φ g, ⟨g, rfl⟩, hc ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hφθ, hg, inv_mul_cancel]

end Cover

section Alpha

variable {p f : ℕ} {K : Type} [Field K]

theorem conj_field_mem (h : UnitaryFieldData p f K) {n : ℕ} {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (ψ : K ≃+* K)
    {x : GL (Fin n) K} (hx : x ∈ StatedSU n (p ^ f) K) :
    A * glAut ψ x * A⁻¹ ∈ StatedSU n (p ^ f) K :=
  mem_statedSU_of_mem_gramSU h (conj_mem_gramSU h _ hA
    (glAut_mem_gramSU h isPrimeFormGram_one ψ (mem_gramSU_one_of_mem h hx)))

theorem conjField_mul {n : ℕ} (A : GL (Fin n) K) (ψ : K ≃+* K) (x y : GL (Fin n) K) :
    A * glAut ψ (x * y) * A⁻¹ = (A * glAut ψ x * A⁻¹) * (A * glAut ψ y * A⁻¹) := by
  rw [map_mul]
  group

@[expose] def alphaSU (h : UnitaryFieldData p f K) {n : ℕ} (A : GL (Fin n) K)
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (ψ : K ≃+* K) :
    StatedSU n (p ^ f) K →* StatedSU n (p ^ f) K where
  toFun x := ⟨A * glAut ψ (x : GL (Fin n) K) * A⁻¹, conj_field_mem h hA ψ x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (conjField_mul A ψ (x : GL (Fin n) K) (y : GL (Fin n) K))

theorem coe_alphaSU (h : UnitaryFieldData p f K) {n : ℕ} (A : GL (Fin n) K)
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (ψ : K ≃+* K)
    (x : StatedSU n (p ^ f) K) :
    ((alphaSU h A hA ψ x : StatedSU n (p ^ f) K) : GL (Fin n) K) =
      A * glAut ψ (x : GL (Fin n) K) * A⁻¹ := rfl

theorem sigma_mk (h : UnitaryFieldData p f K) {n : ℕ} (hn : 1 ≤ n)
    (σ : MulAut (StatedProj (StatedSU n (p ^ f) K)))
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (ψ : K ≃+* K)
    (hσ : MulAut.congr (statedProjEquivPrimeFormOne h hn) σ =
      primeFormConjHom h _ A * primeFormFieldHom h isPrimeFormGram_one ψ)
    (x : StatedSU n (p ^ f) K) :
    σ (QuotientGroup.mk x) = QuotientGroup.mk (alphaSU h A.1 A.2 ψ x) := by
  apply (statedProjEquivPrimeFormOne h hn).injective
  have h1 : statedProjEquivPrimeFormOne h hn (σ (QuotientGroup.mk x)) =
      (MulAut.congr (statedProjEquivPrimeFormOne h hn) σ)
        (statedProjEquivPrimeFormOne h hn (QuotientGroup.mk x)) := by
    simp [MulAut.congr_apply]
  rw [h1, hσ, statedProjEquivPrimeFormOne_mk, statedProjEquivPrimeFormOne_mk, MulAut.mul_apply,
    show primeFormFieldHom h isPrimeFormGram_one ψ = primeFormFieldAut h isPrimeFormGram_one ψ from
      rfl, primeFormFieldAut_mk, primeFormConjHom_mk]
  rfl

theorem alphaSU_pow_of_scalar (h : UnitaryFieldData p f K) {n : ℕ} (A : GL (Fin n) K)
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (ψ : K ≃+* K)
    (u : ℕ) (hu : ∀ x : K, ψ x = x ^ u) (g : StatedSU n (p ^ f) K)
    (hg : g ∈ (QuotientGroup.mk'
      ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K))).ker) :
    alphaSU h A hA ψ g = g ^ u := by
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hg
  obtain ⟨ζ, hζ⟩ := hg
  apply Subtype.ext
  rw [coe_alphaSU, Subgroup.coe_pow, ← hζ]
  have e1 : glAut ψ (Matrix.GeneralLinearGroup.scalar (Fin n) ζ) =
      Matrix.GeneralLinearGroup.scalar (Fin n) (ζ ^ u) := by
    apply Units.ext
    rw [coe_glAut, Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero ψ),
      Units.val_pow_eq_pow_val, ← hu]
  rw [e1, ← map_pow, (commute_scalar (ζ ^ u) A).eq, mul_inv_cancel_right]

end Alpha

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.LinkPSUAux
