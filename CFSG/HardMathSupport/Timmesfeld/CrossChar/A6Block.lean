module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.A6FrameTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralFive
public import CFSG.HardMathSupport.Timmesfeld.Torality.A4Block

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chainRoot)
open CFSG.RankThree.PartOne.KE
open CFSG.ClassicalInvolution.WeakCT
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Cycle

variable {L : Type*} [Field L]

@[expose] def cycMat7 (a : Fin 7 → L) : Matrix (Fin 7) (Fin 7) L :=
  !![0, 0, 0, 0, 0, 0, a 6;
    a 0, 0, 0, 0, 0, 0, 0;
    0, a 1, 0, 0, 0, 0, 0;
    0, 0, a 2, 0, 0, 0, 0;
    0, 0, 0, a 3, 0, 0, 0;
    0, 0, 0, 0, a 4, 0, 0;
    0, 0, 0, 0, 0, a 5, 0]

theorem cycMat7_mul_diagonal (a d : Fin 7 → L) :
    cycMat7 a * Matrix.diagonal d = cycMat7 (fun j => a j * d j) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat7, Matrix.mul_apply, Matrix.diagonal_apply]

@[expose] def cycEigen7 (ω : L) (a : Fin 7 → L) : Matrix (Fin 7) (Fin 7) L :=
  Matrix.diagonal ![1, a 0, a 0 * a 1, a 0 * a 1 * a 2, a 0 * a 1 * a 2 * a 3,
      a 0 * a 1 * a 2 * a 3 * a 4, a 0 * a 1 * a 2 * a 3 * a 4 * a 5] *
    (Matrix.vandermonde fun k : Fin 7 => ω ^ (k : ℕ))ᵀ

theorem cycMat7_mul_cycEigen7 {ω : L} (hω : ω ^ 7 = 1) {a : Fin 7 → L}
    (ha : a 0 * a 1 * a 2 * a 3 * a 4 * a 5 * a 6 = 1) :
    cycMat7 a * cycEigen7 ω a =
      cycEigen7 ω a * Matrix.diagonal fun k : Fin 7 => (ω ^ (k : ℕ)) ^ 6 := by
  ext i k
  have hy : (ω ^ (k : ℕ)) ^ 7 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]
  rw [Matrix.mul_diagonal]
  simp only [cycEigen7, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.transpose_apply,
    Matrix.vandermonde_apply]
  generalize ω ^ (k : ℕ) = y at hy ⊢
  have h8 : y ^ 8 = y := by rw [pow_succ, hy, one_mul]
  have h9 : y ^ 9 = y ^ 2 := by rw [show 9 = 7 + 2 from rfl, pow_add, hy, one_mul]
  have h10 : y ^ 10 = y ^ 3 := by rw [show 10 = 7 + 3 from rfl, pow_add, hy, one_mul]
  have h11 : y ^ 11 = y ^ 4 := by rw [show 11 = 7 + 4 from rfl, pow_add, hy, one_mul]
  have h12 : y ^ 12 = y ^ 5 := by rw [show 12 = 7 + 5 from rfl, pow_add, hy, one_mul]
  fin_cases i <;> simp [cycMat7]
  · linear_combination y ^ 6 * ha
  all_goals (ring_nf; simp only [hy, h8, h9, h10, h11, h12, mul_one])

theorem exists_sl7_conj_diagonal_cyc {ω : L} (hω : IsPrimitiveRoot ω 7) {a : Fin 7 → L}
    (ha : a 0 * a 1 * a 2 * a 3 * a 4 * a 5 * a 6 = 1) (m : SL(7, L))
    (hm : (m : Matrix (Fin 7) (Fin 7) L) = cycMat7 a) :
    ∃ g : SL(7, L), ∃ d : Fin 7 → L, ((g⁻¹ * m * g : SL(7, L)) : Matrix (Fin 7) (Fin 7) L) =
      Matrix.diagonal d := by
  have hω7 : ω ^ 7 = 1 := hω.pow_eq_one
  have ha0 : a 0 ≠ 0 := fun h => by simp [h] at ha
  have ha1 : a 1 ≠ 0 := fun h => by simp [h] at ha
  have ha2 : a 2 ≠ 0 := fun h => by simp [h] at ha
  have ha3 : a 3 ≠ 0 := fun h => by simp [h] at ha
  have ha4 : a 4 ≠ 0 := fun h => by simp [h] at ha
  have ha5 : a 5 ≠ 0 := fun h => by simp [h] at ha
  have hVdet : (Matrix.vandermonde fun k : Fin 7 => ω ^ (k : ℕ)).det ≠ 0 := by
    refine Matrix.det_vandermonde_ne_zero_iff.2 fun i j hij => ?_
    exact Fin.ext (hω.pow_inj i.2 j.2 hij)
  have hQ : (cycEigen7 ω a).det ≠ 0 := by
    rw [cycEigen7, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
    refine mul_ne_zero ?_ hVdet
    simp [Fin.prod_univ_seven, ha0, ha1, ha2, ha3, ha4, ha5]
  have hΔ : ∏ k : Fin 7, (ω ^ (k : ℕ)) ^ 6 = 1 := by
    simp only [Fin.prod_univ_seven]
    have e : ∀ k : Fin 7, (ω ^ (k : ℕ)) ^ 6 = (ω ^ 6) ^ (k : ℕ) := fun k => by
      rw [← pow_mul, ← pow_mul, mul_comm]
    simp only [e]
    have h3 : ((3 : Fin 7) : ℕ) = 3 := rfl
    have h4 : ((4 : Fin 7) : ℕ) = 4 := rfl
    have h5 : ((5 : Fin 7) : ℕ) = 5 := rfl
    have h6 : ((6 : Fin 7) : ℕ) = 6 := rfl
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, h3, h4, h5, h6]
    have : (ω ^ 6) ^ 0 * (ω ^ 6) ^ 1 * (ω ^ 6) ^ 2 * (ω ^ 6) ^ 3 * (ω ^ 6) ^ 4 * (ω ^ 6) ^ 5 *
        (ω ^ 6) ^ 6 = (ω ^ 7) ^ 18 := by ring
    rw [this, hω7, one_pow]
  exact ⟨(Torality.exists_sln_conj_of_eigen hQ hΔ (cycMat7_mul_cycEigen7 hω7 ha) m hm).choose,
    _, (Torality.exists_sln_conj_of_eigen hQ hΔ (cycMat7_mul_cycEigen7 hω7 ha) m hm).choose_spec⟩

end Cycle

section Coxeter

variable {L : Type} [Field L]

abbrev xSL7 (c : Fin 6) (s : L) : SL(7, L) :=
  Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := c)).ne s

abbrev ySL7 (c : Fin 6) (s : L) : SL(7, L) :=
  Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := c)).ne' s

@[expose] def wSL7 (c : Fin 6) : SL(7, L) := xSL7 c 1 * ySL7 c (-1) * xSL7 c 1

@[expose] def coxSL7 : SL(7, L) := wSL7 0 * wSL7 1 * wSL7 2 * wSL7 3 * wSL7 4 * wSL7 5

private theorem uSL_vSL_uSL_a6 : uSL (1 : L) * vSL (-1) * uSL 1 = WSL := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_WSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wSL7_eq_blockSL2 (c : Fin 6) : wSL7 c = blockSL2 L 6 c WSL := by
  rw [wSL7, xSL7, ySL7, ← blockSL2_uSL_a6, ← blockSL2_vSL_a6, ← map_mul, ← map_mul,
    uSL_vSL_uSL_a6]

private def wMatZ (t : Fin 6) : Matrix (Fin 7) (Fin 7) ℤ :=
  Matrix.of fun i j => if i = t.castSucc ∧ j = t.succ then 1 else
    if i = t.succ ∧ j = t.castSucc then -1 else if i = j ∧ i ≠ t.castSucc ∧ i ≠ t.succ then 1 else 0

private def coxMatZ : Matrix (Fin 7) (Fin 7) ℤ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) + 1 then -1 else if i = 0 ∧ j = 6 then 1 else 0

private theorem coxMatZ_eq :
    wMatZ 0 * wMatZ 1 * wMatZ 2 * wMatZ 3 * wMatZ 4 * wMatZ 5 = coxMatZ := by
  decide +kernel

open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply) in
private theorem coe_blockSL2_WSL_a6 (t : Fin 6) :
    ((blockSL2 L 6 t WSL : SL(7, L)) : Matrix (Fin 7) (Fin 7) L) =
      (Int.castRingHom L).mapMatrix (wMatZ t) := by
  rw [blockSL2, coe_blockSL]
  ext a b
  fin_cases t <;> fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, WSL, wMatZ]

theorem coe_coxSL7 :
    ((coxSL7 : SL(7, L)) : Matrix (Fin 7) (Fin 7) L) =
      cycMat7 ![-1, -1, -1, -1, -1, -1, 1] := by
  have h : ((coxSL7 : SL(7, L)) : Matrix (Fin 7) (Fin 7) L) =
      (Int.castRingHom L).mapMatrix coxMatZ := by
    simp only [coxSL7, wSL7_eq_blockSL2, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL2_WSL_a6]
    rw [← coxMatZ_eq]
    simp only [map_mul]
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coxMatZ, cycMat7]

end Coxeter

variable {τ : Tag}


variable {nd : Fin 6 → Fin τ.rank} (hD : A6ChainData τ nd) (hF : A6ChainFrames τ nd)
  {L : Type} [Field L]

private theorem kappa_SL2_a6 (l m : L) (hl : l ≠ 0)
    (h : (uSL l * vSL (-m) * uSL l) * uSL l = vSL (-m) * (uSL l * vSL (-m) * uSL l)) :
    l * m = 1 := by
  have h0 := congrArg Subtype.val h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h0
  have h1 := congrFun (congrFun h0 0) 1
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at h1
  rcases h1 with h1 | h1
  · linear_combination -h1
  · exact absurd h1 hl

private theorem kappa_SL7_a6 (c : Fin 6) (l m : L) (hl : l ≠ 0)
    (h : (xSL7 c l * ySL7 c (-m) * xSL7 c l) * xSL7 c l =
      ySL7 c (-m) * (xSL7 c l * ySL7 c (-m) * xSL7 c l)) : l * m = 1 := by
  refine kappa_SL2_a6 l m hl (blockSL2_injective (K := L) 6 c ?_)
  simp only [map_mul, blockSL2_uSL_a6, blockSL2_vSL_a6]
  exact h

theorem rhoA6_wSL7 (v : WeylGroup τ) (hinj : Function.Injective (a6Frame hD hF L)) (c : Fin 6) :
    ∃ hm : rhoA6 hD hF L v (wSL7 c) ∈ monomialSubgroup τ L,
      weylQuotientHom τ L ⟨rhoA6 hD hF L v (wSL7 c), hm⟩ =
        rootReflection (sigmaA6 nd v c.castSucc c.succ) := by
  have hab : c.castSucc ≠ c.succ := (Fin.castSucc_lt_succ (i := c)).ne
  obtain ⟨a, ha⟩ := rhoA6_transvection hD hF (L := L) v c.castSucc c.succ hab
  obtain ⟨b, hb⟩ := rhoA6_transvection hD hF (L := L) v c.succ c.castSucc hab.symm
  rw [sigmaA6_neg] at hb
  exact Torality.mono_of_transv (rhoA6 hD hF L v) (rhoA6_injective hD hF v hinj)
    (isRoot_sigmaA6 hD v hab) (xSL7 c) (ySL7 c) ha hb fun l m hl h => kappa_SL7_a6 c l m hl h

theorem a6Block_rhoA6 [IsAlgClosed L] (hL : ringChar L ≠ 7)
    (hinj : Function.Injective (a6Frame hD hF L)) (v : WeylGroup τ) :
    ∃ m ∈ rootSpan τ L (a6SigmaRoots nd v), ∃ hm : m ∈ monomialSubgroup τ L,
      weylQuotientHom τ L ⟨m, hm⟩ = rootReflection (sigmaA6 nd v 0 1) *
        rootReflection (sigmaA6 nd v 1 2) * rootReflection (sigmaA6 nd v 2 3) *
        rootReflection (sigmaA6 nd v 3 4) * rootReflection (sigmaA6 nd v 4 5) *
        rootReflection (sigmaA6 nd v 5 6) ∧
      ∀ t ∈ torusGroup τ L, ∃ y ∈ rootSpan τ L (a6SigmaRoots nd v),
        y * (m * t) * y⁻¹ ∈ torusGroup τ L := by
  set ρ := rhoA6 hD hF L v with hρ
  obtain ⟨hm0, hq0⟩ := rhoA6_wSL7 hD hF v hinj 0
  obtain ⟨hm1, hq1⟩ := rhoA6_wSL7 hD hF v hinj 1
  obtain ⟨hm2, hq2⟩ := rhoA6_wSL7 hD hF v hinj 2
  obtain ⟨hm3, hq3⟩ := rhoA6_wSL7 hD hF v hinj 3
  obtain ⟨hm4, hq4⟩ := rhoA6_wSL7 hD hF v hinj 4
  obtain ⟨hm5, hq5⟩ := rhoA6_wSL7 hD hF v hinj 5
  have hmono : ρ coxSL7 ∈ monomialSubgroup τ L := by
    simp only [coxSL7, map_mul]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hm0 hm1) hm2) hm3) hm4) hm5
  refine ⟨ρ coxSL7, ?_, hmono, ?_, ?_⟩
  · rw [← rhoA6_range hD hF v]
    exact ⟨coxSL7, rfl⟩
  · have e : (⟨ρ coxSL7, hmono⟩ : monomialSubgroup τ L) =
        ⟨_, hm0⟩ * ⟨_, hm1⟩ * ⟨_, hm2⟩ * ⟨_, hm3⟩ * ⟨_, hm4⟩ * ⟨_, hm5⟩ := by
      apply Subtype.ext
      simp only [coxSL7, map_mul, Subgroup.coe_mul, hρ]
    rw [e, map_mul, map_mul, map_mul, map_mul, map_mul, hq0, hq1, hq2, hq3, hq4, hq5]
    rfl
  · intro t ht
    have : NeZero ((7 : ℕ) : L) :=
      ⟨by exact_mod_cast Torality.natCast_ne_zero_of_ringChar_ne (by norm_num) hL⟩
    obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 7
    have hconj : ∀ (d' : Fin 7 → Lˣ) (hd' : ∏ i, (d' i : L) = 1), ∃ g : SL(7, L), ∀ i j, i ≠ j →
        ((g⁻¹ * (coxSL7 * Torality.diagSLn d' hd') * g : SL(7, L)) :
          Matrix (Fin 7) (Fin 7) L) i j = 0 := by
      intro d' hd'
      have hm : ((coxSL7 * Torality.diagSLn d' hd' : SL(7, L)) : Matrix (Fin 7) (Fin 7) L) =
          cycMat7 (fun j => (![-1, -1, -1, -1, -1, -1, 1] : Fin 7 → L) j * (d' j : L)) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, coe_coxSL7, Torality.coe_diagSLn,
          cycMat7_mul_diagonal]
      have hprod : (![-1, -1, -1, -1, -1, -1, 1] : Fin 7 → L) 0 * (d' 0 : L) *
          ((![-1, -1, -1, -1, -1, -1, 1] : Fin 7 → L) 1 * (d' 1 : L)) *
          ((![-1, -1, -1, -1, -1, -1, 1] : Fin 7 → L) 2 * (d' 2 : L)) *
          ((![-1, -1, -1, -1, -1, -1, 1] : Fin 7 → L) 3 * (d' 3 : L)) *
          ((![-1, -1, -1, -1, -1, -1, 1] : Fin 7 → L) 4 * (d' 4 : L)) *
          ((![-1, -1, -1, -1, -1, -1, 1] : Fin 7 → L) 5 * (d' 5 : L)) *
          ((![-1, -1, -1, -1, -1, -1, 1] : Fin 7 → L) 6 * (d' 6 : L)) = 1 := by
        simp only [Fin.prod_univ_seven] at hd'
        simp
        linear_combination hd'
      obtain ⟨g, d, hg⟩ := exists_sl7_conj_diagonal_cyc hω hprod _ hm
      refine ⟨g, fun i j hij => ?_⟩
      rw [hg]
      simp [hij]
    obtain ⟨g, h, hh, t₁, ht₁, -, he⟩ := Torality.peel_block_gen (by norm_num) ρ
      (rhoA6_torus hD hF v) (rhoA6_diagonal hD hF v) coxSL7 hconj ht (u := 1)
      (fun A => by simp)
    refine ⟨ρ g, ?_, ?_⟩
    · rw [← rhoA6_range hD hF v]
      exact ⟨g, rfl⟩
    · rw [mul_one] at he
      rw [he]
      simpa using mul_mem hh ht₁

theorem chainRoot_eq_sum_a6 (nd : Fin 6 → Fin τ.rank) (a b : Fin 7) :
    chainRoot nd a b = ∑ k : Fin 6, ((if (a : ℕ) ≤ k ∧ (k : ℕ) < b then 1 else 0) -
      (if (b : ℕ) ≤ k ∧ (k : ℕ) < a then 1 else 0) : ℤ) •
        (Pi.single (nd k) 1 : Fin τ.rank → ℤ) := by
  funext l
  simp only [chainRoot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.single_apply]
  simp [eq_comm]

theorem a6SigmaRoots_subset_aChainRoots (nd : Fin 6 → Fin τ.rank) {v : WeylGroup τ}
    {β : Fin 6 → Fin τ.rank → ℤ} (hv : ∀ k, v • (Pi.single (nd k) 1 : Fin τ.rank → ℤ) = β k) :
    a6SigmaRoots nd v ⊆ aChainRoots β := by
  classical
  rintro r ⟨i, j, hij, rfl⟩
  have key : ∀ (c : Fin 6 → ℤ) (s : Finset (Fin 6)), (∀ k, c k = if k ∈ s then 1 else 0) →
      ∑ k : Fin 6, c k • β k = ∑ k ∈ s, β k := by
    intro c s hc
    rw [← Finset.univ_inter s, ← Finset.sum_ite_mem]
    exact Finset.sum_congr rfl fun k _ => by rw [hc k]; split_ifs <;> simp
  have hsum : sigmaA6 nd v i j = ∑ k : Fin 6, ((if (i : ℕ) ≤ k ∧ (k : ℕ) < j then 1 else 0) -
      (if (j : ℕ) ≤ k ∧ (k : ℕ) < i then 1 else 0) : ℤ) • β k := by
    rw [sigmaA6, chainRoot_eq_sum_a6, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm, hv k]
  rcases lt_or_gt_of_ne hij with h | h
  · have h' : (i : ℕ) < j := h
    refine ⟨⟨i, by omega⟩, ⟨j - 1, by omega⟩, Fin.mk_le_mk.2 (by omega), Or.inl ?_⟩
    rw [hsum]
    refine key _ _ fun k => ?_
    simp only [Finset.mem_Icc, Fin.le_iff_val_le_val]
    split_ifs <;> omega
  · have h' : (j : ℕ) < i := h
    refine ⟨⟨j, by omega⟩, ⟨i - 1, by omega⟩, Fin.mk_le_mk.2 (by omega), Or.inr ?_⟩
    have hs := key (fun k => if (j : ℕ) ≤ k ∧ (k : ℕ) < i then 1 else 0)
      (Finset.Icc ⟨j, by omega⟩ ⟨i - 1, by omega⟩) (fun k => by
        simp only [Finset.mem_Icc, Fin.le_iff_val_le_val]
        split_ifs <;> omega)
    rw [← hs, ← Finset.sum_neg_distrib, hsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← neg_smul]
    congr 1
    split_ifs <;> omega

theorem chainRefl_six {τ : Tag} (β : Fin 6 → Fin τ.rank → ℤ) :
    chainRefl β = rootReflection (β 0) * rootReflection (β 1) * rootReflection (β 2) *
      rootReflection (β 3) * rootReflection (β 4) * rootReflection (β 5) := by
  simp [chainRefl, List.ofFn_succ, mul_assoc]

theorem chainBlockToral_six_of_transitive
    (hinj : ∀ (L : Type) [Field L], Function.Injective (a6Frame hD hF L))
    (htr : ∀ β : Fin 6 → Fin τ.rank → ℤ, IsAChain β →
      ∃ v : WeylGroup τ, ∀ k, v • (Pi.single (nd k) 1 : Fin τ.rank → ℤ) = β k) :
    ChainBlockToral τ 6 := by
  intro L _ _ hL β hβ
  obtain ⟨v, hv⟩ := htr β hβ
  obtain ⟨m, hmS, hmN, hmρ, hmt⟩ := a6Block_rhoA6 hD hF (L := L) hL (hinj L) v
  have hsub : rootSpan τ L (a6SigmaRoots nd v) ≤ rootSpan τ L (aChainRoots β) :=
    biSup_mono (a6SigmaRoots_subset_aChainRoots nd hv)
  have hσ : ∀ c : Fin 6, sigmaA6 nd v c.castSucc c.succ = β c := fun c => by
    rw [sigmaA6, hD.succ, hv]
  refine ⟨m, hsub hmS, hmN, ?_, fun t ht => ?_⟩
  · rw [hmρ, chainRefl_six]
    simp only [← hσ]
    rfl
  · obtain ⟨y, hy, hyt⟩ := hmt t ht
    exact ⟨y, hsub hy, hyt⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
