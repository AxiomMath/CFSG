module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootAdj
public import CFSG.LieType.Chevalley.E6PinnedAdjoint

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

open Psi

variable {K : Type} [Field K]

theorem Psi.e6_highest_sub_aux : ∀ j : Fin TwistTag.E6.tag.rank,
    -e6HighestRoot - Pi.single j 1 ∉ rootFinset TwistTag.E6.tag := by
  decide +kernel

theorem Psi.e6_highest_add_aux : ∀ j : Fin TwistTag.E6.tag.rank, j ≠ e6Idx 1 →
    -e6HighestRoot + Pi.single j 1 ∉ rootFinset TwistTag.E6.tag := by
  decide +kernel

theorem Psi.single_apply_one {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ e6Idx 1) :
    (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) (e6Idx 1) = 0 :=
  Pi.single_eq_of_ne hi.symm _

theorem Psi.xop_apply (j : Fin TwistTag.E6.tag.rank) (c : K) (v : Rv K) (γ : Dr) :
    xop K j c v γ = v γ + c * (if h : γ.1 - Pi.single j 1 ∈ degOneRoots then
      v ⟨γ.1 - Pi.single j 1, h⟩ else 0) := by
  simp [xop, eop]

theorem Psi.yop_apply (j : Fin TwistTag.E6.tag.rank) (c : K) (v : Rv K) (γ : Dr) :
    yop K j c v γ = v γ + c * (if h : γ.1 + Pi.single j 1 ∈ degOneRoots then
      v ⟨γ.1 + Pi.single j 1, h⟩ else 0) := by
  simp [yop, fop]

theorem Psi.piD_rootVec_eq_zero {ν : Fin TwistTag.E6.tag.rank → ℤ}
    (h : ν (e6Idx 1) ≠ -1) : piD K (rootVec TwistTag.E6.tag K ν) = 0 := by
  ext γ
  rw [piD_rootVec, if_neg]
  · rfl
  · intro e
    apply h
    rw [e]
    exact sub_highest_apply_one γ

theorem Psi.neg_highest_ne_single {i : Fin TwistTag.E6.tag.rank}
    (hi : i ≠ e6Idx 1) :
    (-e6HighestRoot : Fin TwistTag.E6.tag.rank → ℤ) ≠ Pi.single i 1 ∧
      (-e6HighestRoot : Fin TwistTag.E6.tag.rank → ℤ) ≠ -Pi.single i 1 := by
  constructor <;> intro e <;> have := congrFun e (e6Idx 1) <;>
    simp only [Pi.neg_apply, single_apply_one hi, e6HighestRoot_idx_one] at this <;> omega

theorem Psi.xOp_v0
    {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ e6Idx 1) (c : K) :
    xOp TwistTag.E6.tag K i c (v0 K) = v0 K := by
  obtain ⟨h1, h2⟩ := neg_highest_ne_single hi
  unfold v0
  rw [E6PinnedAdjoint.xOp_rootVec_E6 i c isRoot_neg_highest h1 h2]
  have h0 : rootVec TwistTag.E6.tag K (-e6HighestRoot + Pi.single i 1) = 0 :=
    dif_neg fun h => e6_highest_add_aux i hi (mem_rootFinset.2 h)
  rw [h0, smul_zero, add_zero]

theorem Psi.yOp_v0
    {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ e6Idx 1) (c : K) :
    yOp TwistTag.E6.tag K i c (v0 K) = v0 K := by
  obtain ⟨h1, h2⟩ := neg_highest_ne_single hi
  unfold v0
  rw [E6PinnedAdjoint.yOp_rootVec_E6 i c isRoot_neg_highest h1 h2]
  have h0 : rootVec TwistTag.E6.tag K (-e6HighestRoot - Pi.single i 1) = 0 :=
    dif_neg fun h => e6_highest_sub_aux i (mem_rootFinset.2 h)
  rw [h0, smul_zero, add_zero]

theorem Psi.sub_single_mem_degOne {j : Fin TwistTag.E6.tag.rank}
    (hj : j ≠ e6Idx 1) {μ : Fin TwistTag.E6.tag.rank → ℤ} (hμ : IsRoot TwistTag.E6.tag μ)
    (γ : Dr) (h : μ + Pi.single j 1 = γ.1 - e6HighestRoot) : γ.1 - Pi.single j 1 ∈ degOneRoots := by
  have hdeg : μ (e6Idx 1) = -1 := by
    have := congrFun h (e6Idx 1)
    simp only [Pi.add_apply, single_apply_one hj, Pi.sub_apply, degOne_apply γ.2,
      e6HighestRoot_idx_one] at this
    omega
  have := add_highest_mem_degOne hμ hdeg
  have e : μ + e6HighestRoot = γ.1 - Pi.single j 1 := by
    have : μ = γ.1 - e6HighestRoot - Pi.single j 1 := by rw [← h]; abel
    rw [this]
    abel
  rwa [e] at this

theorem Psi.add_single_mem_degOne {j : Fin TwistTag.E6.tag.rank}
    (hj : j ≠ e6Idx 1) {μ : Fin TwistTag.E6.tag.rank → ℤ} (hμ : IsRoot TwistTag.E6.tag μ)
    (γ : Dr) (h : μ - Pi.single j 1 = γ.1 - e6HighestRoot) : γ.1 + Pi.single j 1 ∈ degOneRoots := by
  have hdeg : μ (e6Idx 1) = -1 := by
    have := congrFun h (e6Idx 1)
    simp only [Pi.sub_apply, single_apply_one hj, degOne_apply γ.2, e6HighestRoot_idx_one] at this
    omega
  have := add_highest_mem_degOne hμ hdeg
  have e : μ + e6HighestRoot = γ.1 + Pi.single j 1 := by
    have : μ = γ.1 - e6HighestRoot + Pi.single j 1 := by rw [← h]; abel
    rw [this]
    abel
  rwa [e] at this

theorem Psi.piD_xOp
    {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ e6Idx 1) (c : K)
    (y : RootModule TwistTag.E6.tag K) :
    piD K (xOp TwistTag.E6.tag K i c y) = xop K i c (piD K y) := by
  have hz₁ : piD K (rootVec TwistTag.E6.tag K (Pi.single i 1)) = 0 :=
    piD_rootVec_eq_zero (by simp [single_apply_one hi])
  have hz₂ : piD K (rootVec TwistTag.E6.tag K (-Pi.single i 1)) = 0 :=
    piD_rootVec_eq_zero (by simp [single_apply_one hi])
  have key : (piD K).comp (xOp TwistTag.E6.tag K i c) = (xop K i c).comp (piD K) := by
    refine Finsupp.basisSingleOne.ext fun b => ?_
    rcases b with l | ⟨μ, hμ⟩
    · show piD K (xOp TwistTag.E6.tag K i c (hVec TwistTag.E6.tag K l)) =
        xop K i c (piD K (hVec TwistTag.E6.tag K l))
      rw [xOp_apply_hVec, map_add, map_smul, piD_hVec, hz₁]
      simp
    · have hb : (Finsupp.single (Sum.inr ⟨μ, hμ⟩) 1 : RootModule TwistTag.E6.tag K) =
          rootVec TwistTag.E6.tag K μ := (rootVec_eq_single_of_isRoot hμ).symm
      show piD K (xOp TwistTag.E6.tag K i c (Finsupp.single (Sum.inr ⟨μ, hμ⟩) 1)) =
        xop K i c (piD K (Finsupp.single (Sum.inr ⟨μ, hμ⟩) 1))
      rw [hb]
      by_cases h1 : μ = Pi.single i 1
      · subst h1
        rw [CFSG.Blueprint.Chevalley.xOp_apply_rootVec_single, hz₁]
        simp
      by_cases h2 : μ = -Pi.single i 1
      · subst h2
        rw [CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single, map_add, map_add, map_smul,
          map_smul, hz₁, hz₂, piD_hVec]
        simp
      · rw [E6PinnedAdjoint.xOp_rootVec_E6 i c hμ h1 h2]
        ext γ
        rw [map_add, map_smul, xop_apply]
        simp only [Pi.add_apply, Pi.smul_apply, piD_rootVec, smul_eq_mul]
        by_cases hγ : γ.1 - Pi.single i 1 ∈ degOneRoots
        · rw [dif_pos hγ]
          have e : (μ + Pi.single i 1 = γ.1 - e6HighestRoot) ↔
              (μ = (⟨γ.1 - Pi.single i 1, hγ⟩ : Dr).1 - e6HighestRoot) := by
            constructor <;> intro e
            · show μ = γ.1 - Pi.single i 1 - e6HighestRoot
              calc μ = (μ + Pi.single i 1) - Pi.single i 1 := by abel
                _ = γ.1 - e6HighestRoot - Pi.single i 1 := by rw [e]
                _ = γ.1 - Pi.single i 1 - e6HighestRoot := by abel
            · have e' : μ = γ.1 - Pi.single i 1 - e6HighestRoot := e
              rw [e']
              abel
          simp only [e]
        · rw [dif_neg hγ, if_neg (fun e => hγ (sub_single_mem_degOne hi hμ γ e)), mul_zero]
  exact LinearMap.congr_fun key y

theorem Psi.piD_yOp
    {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ e6Idx 1) (c : K)
    (y : RootModule TwistTag.E6.tag K) :
    piD K (yOp TwistTag.E6.tag K i c y) = yop K i c (piD K y) := by
  have hz₁ : piD K (rootVec TwistTag.E6.tag K (Pi.single i 1)) = 0 :=
    piD_rootVec_eq_zero (by simp [single_apply_one hi])
  have hz₂ : piD K (rootVec TwistTag.E6.tag K (-Pi.single i 1)) = 0 :=
    piD_rootVec_eq_zero (by simp [single_apply_one hi])
  have key : (piD K).comp (yOp TwistTag.E6.tag K i c) = (yop K i c).comp (piD K) := by
    refine Finsupp.basisSingleOne.ext fun b => ?_
    rcases b with l | ⟨μ, hμ⟩
    · show piD K (yOp TwistTag.E6.tag K i c (hVec TwistTag.E6.tag K l)) =
        yop K i c (piD K (hVec TwistTag.E6.tag K l))
      rw [yOp_apply_hVec, map_add, map_smul, piD_hVec, hz₂]
      simp
    · have hb : (Finsupp.single (Sum.inr ⟨μ, hμ⟩) 1 : RootModule TwistTag.E6.tag K) =
          rootVec TwistTag.E6.tag K μ := (rootVec_eq_single_of_isRoot hμ).symm
      show piD K (yOp TwistTag.E6.tag K i c (Finsupp.single (Sum.inr ⟨μ, hμ⟩) 1)) =
        yop K i c (piD K (Finsupp.single (Sum.inr ⟨μ, hμ⟩) 1))
      rw [hb]
      by_cases h1 : μ = Pi.single i 1
      · subst h1
        rw [CFSG.Blueprint.Chevalley.yOp_apply_rootVec_single, map_add, map_add, map_smul,
          map_smul, hz₁, hz₂, piD_hVec]
        simp
      by_cases h2 : μ = -Pi.single i 1
      · subst h2
        rw [CFSG.Blueprint.Chevalley.yOp_apply_rootVec_neg_single, hz₂]
        simp
      · rw [E6PinnedAdjoint.yOp_rootVec_E6 i c hμ h1 h2]
        ext γ
        rw [map_add, map_smul, yop_apply]
        simp only [Pi.add_apply, Pi.smul_apply, piD_rootVec, smul_eq_mul]
        by_cases hγ : γ.1 + Pi.single i 1 ∈ degOneRoots
        · rw [dif_pos hγ]
          have e : (μ - Pi.single i 1 = γ.1 - e6HighestRoot) ↔
              (μ = (⟨γ.1 + Pi.single i 1, hγ⟩ : Dr).1 - e6HighestRoot) := by
            constructor <;> intro e
            · show μ = γ.1 + Pi.single i 1 - e6HighestRoot
              calc μ = (μ - Pi.single i 1) + Pi.single i 1 := by abel
                _ = γ.1 - e6HighestRoot + Pi.single i 1 := by rw [e]
                _ = γ.1 + Pi.single i 1 - e6HighestRoot := by abel
            · have e' : μ = γ.1 + Pi.single i 1 - e6HighestRoot := e
              rw [e']
              abel
          simp only [e]
        · rw [dif_neg hγ, if_neg (fun e => hγ (add_single_mem_degOne hi hμ γ e)), mul_zero]
  exact LinearMap.congr_fun key y

theorem psi_conj_xUnit
    {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ e6Idx 1) (c : K) (z : ModGL TwistTag.E6.tag K) :
    psi K (xUnit TwistTag.E6.tag K i c * z * (xUnit TwistTag.E6.tag K i c)⁻¹) =
      xop K i c (psi K z) := by
  have h := psi_conj (xUnit TwistTag.E6.tag K i c) z 1 (xop K i c) (by
    rw [one_smul]
    exact xOp_v0 hi (-c)) fun y => piD_xOp hi c y
  rw [one_smul] at h
  exact h

theorem psi_conj_yUnit
    {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ e6Idx 1) (c : K) (z : ModGL TwistTag.E6.tag K) :
    psi K (yUnit TwistTag.E6.tag K i c * z * (yUnit TwistTag.E6.tag K i c)⁻¹) =
      yop K i c (psi K z) := by
  have h := psi_conj (yUnit TwistTag.E6.tag K i c) z 1 (yop K i c) (by
    rw [one_smul]
    exact yOp_v0 hi (-c)) fun y => piD_yOp hi c y
  rw [one_smul] at h
  exact h

theorem Psi.orbit_card_zero : (TwistTag.E6.orbit 0).card = 2 := by decide +kernel

theorem Psi.orbit_card_one : (TwistTag.E6.orbit 1).card = 2 := by decide +kernel

theorem Psi.orbit_card_two : (TwistTag.E6.orbit 2).card = 1 := by decide +kernel

theorem Psi.orbitMin_zero : TwistTag.E6.orbitMin 0 = 0 := by decide +kernel

theorem Psi.orbitMin_one : TwistTag.E6.orbitMin 1 = 2 := by decide +kernel

theorem Psi.orbitMin_two : TwistTag.E6.orbitMin 2 = 3 := by decide +kernel

theorem Psi.perm_zero : TwistTag.E6.perm 0 = 5 := by decide +kernel

theorem Psi.perm_two : TwistTag.E6.perm 2 = 4 := by decide +kernel

section Orbit

variable (σ : K ≃+* K)

theorem Psi.coe_orbitX_zero (c : orbitField TwistTag.E6 K σ.toRingHom 0) :
    ((orbitX TwistTag.E6 K σ.toRingHom 0 c : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K 0 (c : K) * xUnit TwistTag.E6.tag K 5 (σ c) := by
  rw [coe_orbitX, orbit_card_zero, orbitMin_zero]
  simp [List.range_succ, perm_zero]

theorem Psi.coe_orbitX_one (c : orbitField TwistTag.E6 K σ.toRingHom 1) :
    ((orbitX TwistTag.E6 K σ.toRingHom 1 c : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K 2 (c : K) * xUnit TwistTag.E6.tag K 4 (σ c) := by
  rw [coe_orbitX, orbit_card_one, orbitMin_one]
  simp [List.range_succ, perm_two]

theorem Psi.coe_orbitX_two (c : orbitField TwistTag.E6 K σ.toRingHom 2) :
    ((orbitX TwistTag.E6 K σ.toRingHom 2 c : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) = xUnit TwistTag.E6.tag K 3 (c : K) := by
  rw [coe_orbitX, orbit_card_two, orbitMin_two]
  simp [List.range_succ]

theorem Psi.coe_orbitY_zero (c : orbitField TwistTag.E6 K σ.toRingHom 0) :
    ((orbitY TwistTag.E6 K σ.toRingHom 0 c : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) =
      yUnit TwistTag.E6.tag K 0 (c : K) * yUnit TwistTag.E6.tag K 5 (σ c) := by
  rw [coe_orbitY, orbit_card_zero, orbitMin_zero]
  simp [List.range_succ, perm_zero]

theorem Psi.coe_orbitY_one (c : orbitField TwistTag.E6 K σ.toRingHom 1) :
    ((orbitY TwistTag.E6 K σ.toRingHom 1 c : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) =
      yUnit TwistTag.E6.tag K 2 (c : K) * yUnit TwistTag.E6.tag K 4 (σ c) := by
  rw [coe_orbitY, orbit_card_one, orbitMin_one]
  simp [List.range_succ, perm_two]

theorem Psi.coe_orbitY_two (c : orbitField TwistTag.E6 K σ.toRingHom 2) :
    ((orbitY TwistTag.E6 K σ.toRingHom 2 c : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) = yUnit TwistTag.E6.tag K 3 (c : K) := by
  rw [coe_orbitY, orbit_card_two, orbitMin_two]
  simp [List.range_succ]

theorem psi_conj_orbitX {a : Fin TwistTag.E6.foldedTag.rank} (ha : a ≠ 3)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) (z : ModGL TwistTag.E6.tag K) :
    psi K ((orbitX TwistTag.E6 K σ.toRingHom a c : adjointGroup TwistTag.E6.tag K) * z *
        ((orbitX TwistTag.E6 K σ.toRingHom a c : adjointGroup TwistTag.E6.tag K) :
          ModGL TwistTag.E6.tag K)⁻¹) = xorb K σ a (c : K) (psi K z) := by
  have hcases : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → a = 0 ∨ a = 1 ∨ a = 2 := by
    decide
  rcases hcases a ha with rfl | rfl | rfl
  · rw [coe_orbitX_zero, mul_inv_rev,
      show xUnit TwistTag.E6.tag K 0 (c : K) * xUnit TwistTag.E6.tag K 5 (σ c) * z *
          ((xUnit TwistTag.E6.tag K 5 (σ c))⁻¹ * (xUnit TwistTag.E6.tag K 0 (c : K))⁻¹) =
        xUnit TwistTag.E6.tag K 0 (c : K) * (xUnit TwistTag.E6.tag K 5 (σ c) * z *
          (xUnit TwistTag.E6.tag K 5 (σ c))⁻¹) * (xUnit TwistTag.E6.tag K 0 (c : K))⁻¹ by group,
      psi_conj_xUnit (i := 0) (by decide) (c : K), psi_conj_xUnit (i := 5) (by decide)]
    rfl
  · rw [coe_orbitX_one, mul_inv_rev,
      show xUnit TwistTag.E6.tag K 2 (c : K) * xUnit TwistTag.E6.tag K 4 (σ c) * z *
          ((xUnit TwistTag.E6.tag K 4 (σ c))⁻¹ * (xUnit TwistTag.E6.tag K 2 (c : K))⁻¹) =
        xUnit TwistTag.E6.tag K 2 (c : K) * (xUnit TwistTag.E6.tag K 4 (σ c) * z *
          (xUnit TwistTag.E6.tag K 4 (σ c))⁻¹) * (xUnit TwistTag.E6.tag K 2 (c : K))⁻¹ by group,
      psi_conj_xUnit (i := 2) (by decide) (c : K), psi_conj_xUnit (i := 4) (by decide)]
    rfl
  · rw [coe_orbitX_two, psi_conj_xUnit (i := 3) (by decide)]
    rfl

theorem psi_conj_orbitY {a : Fin TwistTag.E6.foldedTag.rank} (ha : a ≠ 3)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) (z : ModGL TwistTag.E6.tag K) :
    psi K ((orbitY TwistTag.E6 K σ.toRingHom a c : adjointGroup TwistTag.E6.tag K) * z *
        ((orbitY TwistTag.E6 K σ.toRingHom a c : adjointGroup TwistTag.E6.tag K) :
          ModGL TwistTag.E6.tag K)⁻¹) = yorb K σ a (c : K) (psi K z) := by
  have hcases : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → a = 0 ∨ a = 1 ∨ a = 2 := by
    decide
  rcases hcases a ha with rfl | rfl | rfl
  · rw [coe_orbitY_zero, mul_inv_rev,
      show yUnit TwistTag.E6.tag K 0 (c : K) * yUnit TwistTag.E6.tag K 5 (σ c) * z *
          ((yUnit TwistTag.E6.tag K 5 (σ c))⁻¹ * (yUnit TwistTag.E6.tag K 0 (c : K))⁻¹) =
        yUnit TwistTag.E6.tag K 0 (c : K) * (yUnit TwistTag.E6.tag K 5 (σ c) * z *
          (yUnit TwistTag.E6.tag K 5 (σ c))⁻¹) * (yUnit TwistTag.E6.tag K 0 (c : K))⁻¹ by group,
      psi_conj_yUnit (i := 0) (by decide) (c : K), psi_conj_yUnit (i := 5) (by decide)]
    rfl
  · rw [coe_orbitY_one, mul_inv_rev,
      show yUnit TwistTag.E6.tag K 2 (c : K) * yUnit TwistTag.E6.tag K 4 (σ c) * z *
          ((yUnit TwistTag.E6.tag K 4 (σ c))⁻¹ * (yUnit TwistTag.E6.tag K 2 (c : K))⁻¹) =
        yUnit TwistTag.E6.tag K 2 (c : K) * (yUnit TwistTag.E6.tag K 4 (σ c) * z *
          (yUnit TwistTag.E6.tag K 4 (σ c))⁻¹) * (yUnit TwistTag.E6.tag K 2 (c : K))⁻¹ by group,
      psi_conj_yUnit (i := 2) (by decide) (c : K), psi_conj_yUnit (i := 4) (by decide)]
    rfl
  · rw [coe_orbitY_two, psi_conj_yUnit (i := 3) (by decide)]
    rfl

end Orbit

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
