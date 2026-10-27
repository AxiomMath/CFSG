module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open scoped MatrixGroups commutatorElement

theorem matrix_two_eq_one_of_mulVec_eq_self {K : Type*} [Field K] {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) {v : Fin 2 → K} (hv : v ≠ 0) (hMv : M.mulVec v = v) {p : ℕ}
    (hpK : (p : K) ≠ 0) (hMp : M ^ p = 1) : M = 1 := by
  have hdet0 : (M - 1).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, hMv, Matrix.one_mulVec, sub_self]
  have hN2 : (M - 1) * (M - 1) = 0 := by
    rw [Matrix.det_fin_two] at hdet hdet0
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at hdet0
    have htr : M 0 0 + M 1 1 - 2 = 0 := by linear_combination hdet - hdet0
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (M 0 0) * htr - hdet
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (M 0 1) * htr
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (M 1 0) * htr
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (M 1 1) * htr - hdet
  have hpow : ∀ k : ℕ, M ^ k = 1 + (k : K) • (M - 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc M ^ (k + 1) = M ^ k * M := pow_succ _ _
        _ = (1 + (k : K) • (M - 1)) * (1 + (M - 1)) := by rw [ih]; congr 1; abel
        _ = 1 + ((k + 1 : ℕ) : K) • (M - 1) := by
          simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, hN2, smul_zero,
            add_zero, Nat.cast_succ]
          rw [add_smul, one_smul, add_assoc]
  have h1 : (p : K) • (M - 1) = 0 := by
    have := hpow p
    rw [hMp] at this
    exact add_eq_left.mp this.symm
  have h2 : M - 1 = 0 := (smul_eq_zero.mp h1).resolve_left hpK
  exact sub_eq_zero.mp h2

theorem exists_common_eigenvector_of_pow_eq_one {K V ι : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V] {p : ℕ}
    (hpK : (p : K) ≠ 0) (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j => Commute (f i) (f j)) (hf : ∀ i, f i ^ p = 1) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ μ : K, f i v = μ • v := by
  have hsq : Squarefree (Polynomial.X ^ p - 1 : Polynomial K) := by
    have := (Polynomial.separable_X_pow_sub_C (1 : K) hpK one_ne_zero).squarefree
    simpa using this
  have hss : ∀ i, (f i).IsSemisimple := fun i => by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq ?_
    simp [hf i]
  have htop : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤ := fun i =>
    Module.End.iSup_maxGenEigenspace_eq_top _
  have h := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f hcomm htop
  have hne : ∃ χ : ι → K, (⨅ i, (f i).maxGenEigenspace (χ i)) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have : ⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊥ := iSup_eq_bot.mpr hcon
    rw [h] at this
    exact top_ne_bot this
  obtain ⟨χ, hχ⟩ := hne
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hχ
  refine ⟨v, hv0, fun i => ⟨χ i, ?_⟩⟩
  have hvi : v ∈ (f i).maxGenEigenspace (χ i) := (Submodule.mem_iInf _).mp hv i
  rw [(hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hvi
  exact Module.End.mem_eigenspace_iff.mp hvi

theorem natCast_ne_zero_algebraicClosure_of_ringChar_ne {F : Type*} [Field F] {p : ℕ}
    (hp : p.Prime) (hpℓ : ringChar F ≠ p) : ((p : ℕ) : AlgebraicClosure F) ≠ 0 := by
  intro h0
  have h1 : ((p : ℕ) : F) = 0 := by
    apply (algebraMap F (AlgebraicClosure F)).injective
    rw [map_natCast, map_zero]
    exact h0
  have h2 : ringChar F ∣ p := (ringChar.spec F _).mp h1
  rcases (Nat.dvd_prime hp).mp h2 with h3 | h3
  · exact CharP.ringChar_ne_one h3
  · exact hpℓ h3

theorem sl2_elemAb_card_le {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hpF : ringChar F ≠ p) (A : Subgroup SL(2, F))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ p = 1) :
    Nat.card ↥A ≤ p := by
  classical
  have _ := hodd
  have _ := hp2
  have hp : p.Prime := Fact.out
  have hpK : ((p : ℕ) : AlgebraicClosure F) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ringChar_ne hp hpF
  set K := AlgebraicClosure F with hK
  let ρ : SL(2, F) →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun a => (a : Matrix (Fin 2) (Fin 2) F).map (algebraMap F K)
      map_one' := by simp
      map_mul' := fun a b => by simp [Matrix.map_mul] }
  have hρ : ∀ a : SL(2, F), ρ a = (a : Matrix (Fin 2) (Fin 2) F).map (algebraMap F K) :=
    fun a => rfl
  have hρinj : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    rw [hρ, hρ] at hab
    exact Matrix.map_injective (algebraMap F K).injective hab
  have hρdet : ∀ a : SL(2, F), (ρ a).det = 1 := by
    intro a
    rw [hρ, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe,
      map_one]
  let f : A → Module.End K (Fin 2 → K) := fun a => Matrix.toLinAlgEquiv' (ρ a)
  have hfv : ∀ (a : A) (v : Fin 2 → K), f a v = (ρ a).mulVec v := fun a v => rfl
  have hcommf : Pairwise fun a b : A => Commute (f a) (f b) := by
    intro a b _
    show f a * f b = f b * f a
    simp only [f, ← map_mul, ← map_mul ρ]
    congr 2
    exact hcomm a a.2 b b.2
  have hfp : ∀ a : A, f a ^ p = 1 := by
    intro a
    simp only [f, ← map_pow, ← map_pow ρ]
    rw [show (a : SL(2, F)) ^ p = 1 from hexp a a.2]
    simp
  obtain ⟨v, hv0, hveig⟩ := exists_common_eigenvector_of_pow_eq_one hpK f hcommf hfp
  choose χ hχ using hveig
  have hχ' : ∀ a : A, (ρ a).mulVec v = χ a • v := fun a => by rw [← hfv]; exact hχ a
  have hχ1 : χ 1 = 1 := by
    have h1 := hχ' 1
    rw [Subgroup.coe_one, map_one, Matrix.one_mulVec] at h1
    exact smul_left_injective K hv0 (by simpa using h1.symm : χ 1 • v = (1 : K) • v)
  have hχmul : ∀ a b : A, χ (a * b) = χ a * χ b := by
    intro a b
    have h1 := hχ' (a * b)
    rw [Subgroup.coe_mul, map_mul, ← Matrix.mulVec_mulVec, hχ' b, Matrix.mulVec_smul, hχ' a,
      smul_smul] at h1
    exact smul_left_injective K hv0 (by simpa [mul_comm] using h1.symm)
  let χh : A →* K := { toFun := χ, map_one' := hχ1, map_mul' := hχmul }
  have hχp : ∀ a : A, χ a ^ p = 1 := by
    intro a
    have h1 := Module.End.HasEigenvector.pow_apply (f := f a) (μ := χ a) (v := v)
      ⟨Module.End.mem_eigenspace_iff.mpr (hχ a), hv0⟩ p
    rw [hfp a] at h1
    exact (smul_left_injective K hv0 (by simpa using h1 : (1 : K) • v = χ a ^ p • v)).symm
  have hinj : Function.Injective χh := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha1 : χ a = 1 := ha
    have h1 : (ρ a).mulVec v = v := by rw [hχ' a, ha1, one_smul]
    have h2 : ρ a ^ p = 1 := by
      rw [← map_pow, show (a : SL(2, F)) ^ p = 1 from hexp a a.2]
      simp
    have h3 := matrix_two_eq_one_of_mulVec_eq_self (hρdet a) hv0 h1 hpK h2
    apply Subtype.ext
    apply hρinj
    show ρ (a : SL(2, F)) = ρ 1
    rw [h3, map_one]
  have hmem : ∀ a : A, χ a ∈ Polynomial.nthRootsFinset p (1 : K) := fun a =>
    (Polynomial.mem_nthRootsFinset hp.pos 1).mpr (hχp a)
  let g : A → ↥(Polynomial.nthRootsFinset p (1 : K)) := fun a => ⟨χ a, hmem a⟩
  have hg : Function.Injective g := fun a b h => hinj (congrArg Subtype.val h)
  calc Nat.card A ≤ Nat.card ↥(Polynomial.nthRootsFinset p (1 : K)) :=
        Nat.card_le_card_of_injective g hg
    _ = (Polynomial.nthRootsFinset p (1 : K)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ p := by
        rw [Polynomial.nthRootsFinset_def]
        exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

theorem exists_ne_zero_sq_ne_one_of_four_le {F : Type*} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  have := Fintype.ofFinite F
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1, -1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have hs : a = 1 ∨ a = -1 := sq_eq_one_iff.mp (hcon a ha)
      rcases hs with rfl | rfl <;> simp
  have hle : (Finset.univ : Finset F).card ≤ ({0, 1, -1} : Finset F).card :=
    Finset.card_le_card hsub
  have h3 : ({0, 1, -1} : Finset F).card ≤ 3 :=
    (Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
  omega

theorem sl2_normal_neg_one_mem {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (N : Subgroup SL(2, F)) [N.Normal] (hN : N ≠ ⊥) :
    (-1 : SL(2, F)) ∈ N := by
  classical
  have _ := hodd
  have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let π : SL(2, F) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.mk' (Subgroup.center SL(2, F))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have : (N.map π).Normal := Subgroup.Normal.map ‹N.Normal› π hπ
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · obtain ⟨⟨n, hn⟩, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN
    have hnc : n ∈ Subgroup.center SL(2, F) := by
      have : π n ∈ N.map π := Subgroup.mem_map_of_mem π hn
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff n).mp this
    rcases CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.eq_one_or_neg_one_of_mem_center hnc with h1 | h1
    · exact absurd (Subtype.ext h1) hn1
    · rw [← h1]; exact hn
  · obtain ⟨a, ha0, hasq⟩ := exists_ne_zero_sq_ne_one_of_four_le (F := F) (by omega)
    have hperf : commutator SL(2, F) = ⊤ := Matrix.SL2.commutator_eq_top ha0 hasq
    have key : ∀ g₁ g₂ : SL(2, F), ⁅g₁, g₂⁆ ∈ N := by
      intro g₁ g₂
      have hmem : π g₁ ∈ N.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n₁, hn₁, hπn⟩ := hmem
      have hc0 : n₁⁻¹ * g₁ ∈ Subgroup.center SL(2, F) := QuotientGroup.eq.mp hπn
      obtain ⟨c, hcz, rfl⟩ : ∃ c ∈ Subgroup.center SL(2, F), g₁ = n₁ * c :=
        ⟨n₁⁻¹ * g₁, hc0, by group⟩
      have hcg : c * g₂ = g₂ * c := (Subgroup.mem_center_iff.mp hcz g₂).symm
      have h1 : ⁅n₁ * c, g₂⁆ = n₁ * (g₂ * n₁⁻¹ * g₂⁻¹) := by
        rw [commutatorElement_def]
        calc n₁ * c * g₂ * (n₁ * c)⁻¹ * g₂⁻¹ = n₁ * (c * g₂) * c⁻¹ * n₁⁻¹ * g₂⁻¹ := by group
          _ = n₁ * (g₂ * c) * c⁻¹ * n₁⁻¹ * g₂⁻¹ := by rw [hcg]
          _ = n₁ * (g₂ * n₁⁻¹ * g₂⁻¹) := by group
      rw [h1]
      exact N.mul_mem hn₁ (Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem hn₁) g₂)
    have hle : commutator SL(2, F) ≤ N := by
      rw [commutator_def]
      exact Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => key g₁ g₂
    rw [hperf] at hle
    exact hle (Subgroup.mem_top _)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
