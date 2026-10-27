module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolution
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

section RootSL2

variable {τ : Tag} {K : Type} [Field K]

theorem rootSL2_neg_one_eq_rootDiagUnit {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {b : Fin τ.rank → Kˣ} (hb : ∀ i, (-1 : Kˣ) ^ corootPair γ (Pi.single i 1) = b i) :
    rootSL2 τ K γ (HSL (-1)) = rootDiagUnit τ b := by
  obtain ⟨a, ha, -⟩ := exists_rootTorusSL2_eq_rootDiagUnit (K := K) hγ (-1)
  have hab : a = b := by
    funext i
    have h1 := ((exceptional_Lang_root_rank_one_torus_transport τ K hγ).2.2.2.2.1 (-1)).2
      (Pi.single i 1) (isRoot_single τ i)
    rw [ha] at h1
    change rootDiag a (rootVec τ K (Pi.single i 1)) = _ at h1
    rw [rootDiag_rootVec a (isRoot_single τ i)] at h1
    have hne : rootVec τ K (Pi.single i 1) ≠ 0 := by
      rw [rootVec_eq_single_of_isRoot (isRoot_single τ i)]
      exact Finsupp.single_ne_zero.2 one_ne_zero
    have h3 := smul_left_injective K hne h1
    have h4 : rootChar a (Pi.single i 1) = (-1 : Kˣ) ^ corootPair γ (Pi.single i 1) :=
      Units.ext h3
    rw [← hb i, ← h4]
    have := rootChar_nsmul_single a i 1
    simpa using this.symm
  subst hab
  exact ha

end RootSL2

section Mask4

theorem d4_corootPair_parity {γ : Fin Tag.D4.rank → ℤ}
    (hγ : γ ∈ kernelRoots (signMaskChar Tag.D4 4)) (i : Fin Tag.D4.rank) :
    corootPair γ (Pi.single i 1) % 2 = if (i : ℕ) = 2 then 1 else 0 := by
  obtain ⟨j, hj, rfl, hker⟩ := (mem_kernelRoots_iff d4Certificate_check).1 hγ
  have h : ∀ j < d4Certificate.roots.length, inKernel d4Certificate 4 j = true →
      ∀ i : Fin Tag.D4.rank, corootPair (d4Certificate.root j) (Pi.single i 1) % 2 =
        if (i : ℕ) = 2 then 1 else 0 := by
    decide +kernel
  exact h j hj hker i

variable {K : Type} [Field K]

theorem d4_neg_one_zpow_eq {γ : Fin Tag.D4.rank → ℤ}
    (hγ : γ ∈ kernelRoots (signMaskChar Tag.D4 4)) (i : Fin Tag.D4.rank) :
    (-1 : Kˣ) ^ corootPair γ (Pi.single i 1) = signMaskTuple Tag.D4 K 4 i := by
  have h := d4_corootPair_parity hγ i
  by_cases hi : (i : ℕ) = 2
  · have h' : corootPair γ (Pi.single i 1) % 2 = 1 := by simpa [hi] using h
    have hodd : Odd (corootPair γ (Pi.single i 1)) := Int.odd_iff.2 h'
    rw [hodd.neg_one_zpow]
    simp [signMaskTuple, hi]
  · have h' : corootPair γ (Pi.single i 1) % 2 = 0 := by simpa [hi] using h
    have heven : Even (corootPair γ (Pi.single i 1)) := Int.even_iff.2 h'
    rw [heven.neg_one_zpow]
    have : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 3 := by
      have hlt := i.2
      change (i : ℕ) < 4 at hlt
      omega
    rcases this with h0 | h0 | h0 <;> simp [signMaskTuple, h0]

end Mask4

section OrbitMap

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

theorem map_neg_one_sl2 {R S : Type*} [Field R] [Field S] (f : R →+* S) :
    Matrix.SpecialLinearGroup.map f (-1 : SL(2, R)) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem HSL_neg_one_eq {R : Type*} [Field R] : (HSL (-1 : Rˣ) : SL(2, R)) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem orbitMap_neg_one_d4 (D : OrthogonalSemilinearFixedRootDatum Tag.D4 p k)
    (hχ : D.χ = signMaskChar Tag.D4 4)
    (hodd : ∀ {O : Set (Fin Tag.D4.rank → ℤ)}, O ∈ D.orbits → Odd (orbitCard O))
    {O : Set (Fin Tag.D4.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.orbitMap O (-1) = rootDiagUnit Tag.D4 (signMaskTuple Tag.D4 k 4) := by
  set x : ModGL Tag.D4 k := rootDiagUnit Tag.D4 (signMaskTuple Tag.D4 k 4) with hx
  have hx2 : x * x = 1 := by
    rw [hx, ← rootDiagUnit_mul]
    have : (signMaskTuple Tag.D4 k 4 * signMaskTuple Tag.D4 k 4) = 1 := by
      funext i
      simp only [Pi.mul_apply, Pi.one_apply, signMaskTuple, ← pow_add]
      rcases Nat.mod_two_eq_zero_or_one (4 / 2 ^ (i : ℕ)) with h | h <;> rw [h]
      · simp
      · rw [← two_mul, pow_mul]
        simp
    rw [this, rootDiagUnit_one]
  have hf : ∀ j, D.orbitFactor O j (-1) = x := by
    intro j
    rw [D.orbitFactor_apply, map_neg_one_sl2, map_neg_one_sl2, ← HSL_neg_one_eq]
    have hmem : D.orbitVec O j ∈ kernelRoots (signMaskChar Tag.D4 4) := by
      rw [← hχ]
      exact D.thetaOrbit_subset_kernelRoots (D.orbitRoot_mem_kernelRoots hO)
        (by rw [← D.eq_thetaOrbit_orbitRoot hO]; exact D.orbitVec_mem hO j)
    exact rootSL2_neg_one_eq_rootDiagUnit hmem.1 fun i => d4_neg_one_zpow_eq (hχ ▸ hmem) i
  rw [D.orbitMap_eq_prod]
  simp only [hf, List.map_const', List.length_range, List.prod_replicate]
  obtain ⟨m, hm⟩ := hodd hO
  rw [hm, pow_succ, pow_mul, sq, hx2, one_pow, one_mul]

end OrbitMap

end CFSG.ClassicalInvolution.ModelFacts
