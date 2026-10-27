module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneCases
public import CFSG.HardMathSupport.Timmesfeld.Torality.E8A4Block

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.E6 Matrix
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Timmesfeld.Torality
open scoped MatrixGroups commutatorElement
open Fin.NatCast

set_option linter.unusedSectionVars false


section WeylData

theorem wordProd_pow_smul (ω : List (Fin Tag.E8.rank)) (n : ℕ) (u : Fin Tag.E8.rank → ℤ) :
    ((coxeterSystem Tag.E8).wordProd ω ^ n) • u = (wordMat Tag.E8 ω ^ n) *ᵥ u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, wordProd_smul_eq_wordMat_mulVec, ih, pow_succ, Matrix.mulVec_mulVec]

theorem g1_pow4_smul_wbA (i : Fin 5) :
    e8FiveG1 ^ 4 • wbE8A4 e8VA i = wbE8A4 e8VA (i + 1) := by
  rw [wbE8A4, wbE8A4, e8VA_smul, e8VA_smul, g1_eq, wordProd_pow_smul]
  revert i
  decide +kernel

theorem g2_smul_sigmaA (i j : Fin 5) :
    e8FiveG2 • sigmaRootE8A4 e8VA i j = sigmaRootE8A4 e8VA i j := by
  rw [sigmaRootE8A4, wbE8A4, wbE8A4, smul_sub, e8VA_smul, e8VA_smul, ← Matrix.mulVec_sub,
    g2_eq, wordProd_smul_eq_wordMat_mulVec]
  revert i j
  decide +kernel

theorem g1_pow4_smul_sigmaA (i j : Fin 5) :
    e8FiveG1 ^ 4 • sigmaRootE8A4 e8VA i j = sigmaRootE8A4 e8VA (i + 1) (j + 1) := by
  rw [sigmaRootE8A4, sigmaRootE8A4, smul_sub, g1_pow4_smul_wbA, g1_pow4_smul_wbA]

end WeylData

section Frame

variable (K : Type) [Field K] [Finite K]

@[expose] def rhoA : SL(5, K) →* ModGL Tag.E8 K := rhoSigmaE8A4 K e8VA

variable {K}

theorem rhoA_injective : Function.Injective (rhoA K) := rhoSigmaE8A4_injective e8VA

theorem rhoA_mem_adjoint (X : SL(5, K)) : rhoA K X ∈ adjointGroup Tag.E8 K := by
  have h1 : rhoA K X ∈ (rhoA K).range := ⟨X, rfl⟩
  rw [rhoA, rhoSigmaE8A4_range] at h1
  exact (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α :
    rootSpan Tag.E8 K (sigmaSetE8A4 e8VA) ≤ adjointGroup Tag.E8 K) h1

theorem rootDiagUnit_mul_rhoA (b : Fin Tag.E8.rank → Kˣ) (X : SL(5, K)) :
    rootDiagUnit Tag.E8 b * rhoA K X * (rootDiagUnit Tag.E8 b)⁻¹ =
      rhoA K (conjDiagn (fun i => rootChar b (wbE8A4 e8VA i)) X) :=
  rhoSigmaE8A4_torus e8VA b X

theorem rhoA_diagonal (X : SL(5, K))
    (hX : ∀ i j : Fin 5, i ≠ j → (X : Matrix (Fin 5) (Fin 5) K) i j = 0) :
    rhoA K X ∈ torusGroup Tag.E8 K :=
  rhoSigmaE8A4_diagonal e8VA X hX

theorem exists_mA : ∃ hm : rhoA K coxSL5 ∈ monomialSubgroup Tag.E8 K,
    weylQuotientHom Tag.E8 K ⟨rhoA K coxSL5, hm⟩ = e8FiveG1 ^ 4 := by
  have hfr := e8A4_frame (L := K) e8VA
  obtain ⟨hm01, hq01⟩ := frame_wSL5 hfr 0 1 (by decide)
  obtain ⟨hm12, hq12⟩ := frame_wSL5 hfr 1 2 (by decide)
  obtain ⟨hm23, hq23⟩ := frame_wSL5 hfr 2 3 (by decide)
  obtain ⟨hm34, hq34⟩ := frame_wSL5 hfr 3 4 (by decide)
  have M01 : MapsRootLines (rhoA K (wSL5 0 1 (by decide)))
      (rootReflection (sigmaRootE8A4 e8VA 0 1)) := by
    have := mapsRootLines_weylQuotientHom (τ := Tag.E8) (R := K) ⟨_, hm01⟩
    rwa [hq01] at this
  have M12 : MapsRootLines (rhoA K (wSL5 1 2 (by decide)))
      (rootReflection (sigmaRootE8A4 e8VA 1 2)) := by
    have := mapsRootLines_weylQuotientHom (τ := Tag.E8) (R := K) ⟨_, hm12⟩
    rwa [hq12] at this
  have M23 : MapsRootLines (rhoA K (wSL5 2 3 (by decide)))
      (rootReflection (sigmaRootE8A4 e8VA 2 3)) := by
    have := mapsRootLines_weylQuotientHom (τ := Tag.E8) (R := K) ⟨_, hm23⟩
    rwa [hq23] at this
  have M34 : MapsRootLines (rhoA K (wSL5 3 4 (by decide)))
      (rootReflection (sigmaRootE8A4 e8VA 3 4)) := by
    have := mapsRootLines_weylQuotientHom (τ := Tag.E8) (R := K) ⟨_, hm34⟩
    rwa [hq34] at this
  have hcox : rhoA K coxSL5 = rhoA K (wSL5 0 1 (by decide)) * rhoA K (wSL5 1 2 (by decide)) *
      rhoA K (wSL5 2 3 (by decide)) * rhoA K (wSL5 3 4 (by decide)) := by
    simp only [coxSL5, map_mul]
  have hmono : rhoA K coxSL5 ∈ monomialSubgroup Tag.E8 K := by
    rw [hcox]
    exact mul_mem (mul_mem (mul_mem hm01 hm12) hm23) hm34
  refine ⟨hmono, ?_⟩
  refine (weylQuotientHom_eq (g := ⟨rhoA K coxSL5, hmono⟩) ?_).trans coxA_eq
  have := ((M01.mul M12).mul M23).mul M34
  simpa only [hcox] using this

end Frame

section Torus

variable {K : Type} [Field K] [Finite K]

theorem pow_rootDiagUnit_mul {y : ModGL Tag.E8 K} (hy : y ∈ monomialSubgroup Tag.E8 K)
    {w : WeylGroup Tag.E8} (hyw : weylQuotientHom Tag.E8 K ⟨y, hy⟩ = w)
    (a : Fin Tag.E8.rank → Kˣ) : ∀ n : ℕ,
    (rootDiagUnit Tag.E8 a * y) ^ n = rootDiagUnit Tag.E8
      (∏ k ∈ Finset.range n, CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct (w ^ k) a) *
        y ^ n
  | 0 => by simp [rootDiagUnit_one]
  | n + 1 => by
    have hyn : y ^ n ∈ monomialSubgroup Tag.E8 K := pow_mem hy n
    have hrho : weylQuotientHom Tag.E8 K ⟨y ^ n, hyn⟩ = w ^ n := by
      have : (⟨y ^ n, hyn⟩ : monomialSubgroup Tag.E8 K) = ⟨y, hy⟩ ^ n := rfl
      rw [this, map_pow, hyw]
    have hc := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.monomial_conj_rootDiagUnit
      (⟨y ^ n, hyn⟩ : monomialSubgroup Tag.E8 K) a
    rw [hrho] at hc
    rw [pow_succ, pow_rootDiagUnit_mul hy hyw a n, Finset.prod_range_succ, rootDiagUnit_mul,
      pow_succ]
    calc rootDiagUnit Tag.E8 (∏ k ∈ Finset.range n,
          CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct (w ^ k) a) * y ^ n *
          (rootDiagUnit Tag.E8 a * y) =
        rootDiagUnit Tag.E8 (∏ k ∈ Finset.range n,
          CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct (w ^ k) a) *
          (y ^ n * rootDiagUnit Tag.E8 a * (y ^ n)⁻¹) * (y ^ n * y) := by
          simp only [mul_assoc, inv_mul_cancel_left]
      _ = _ := by rw [hc]

end Torus

section DiagConj

variable {K : Type} [Field K]

theorem exists_diag_conj (ρ : SL(5, K) →* ModGL Tag.E8 K) (hρi : Function.Injective ρ)
    (r : Fin 5 → Fin 5 → Fin Tag.E8.rank → ℤ)
    (hρ : ∀ i j (hij : i ≠ j), ∃ ε : Kˣ, ∀ t : K,
      ρ (SpecialLinearGroup.transvection hij t) = pinnedX Tag.E8 K (r i j) ((ε : K) * t))
    {y : ModGL Tag.E8 K}
    (hy : ∀ i j, i ≠ j → ∃ μ : Kˣ, ∀ c : K,
      y * pinnedX Tag.E8 K (r i j) c * y⁻¹ = pinnedX Tag.E8 K (r i j) ((μ : K) * c)) :
    ∃ du : Fin 5 → Kˣ, ∀ A : SL(5, K), y * ρ A * y⁻¹ = ρ (conjDiagn du A) := by
  classical
  choose! ε hε using hρ
  choose! μ hμ using hy
  set lam : Fin 5 → Fin 5 → K := fun i j => (μ i j : K) with hlam
  have hlamne : ∀ i j, i ≠ j → lam i j ≠ 0 := fun i j _ => (μ i j).ne_zero
  have key : ∀ i j (hij : i ≠ j) (t : K),
      y * ρ (SpecialLinearGroup.transvection hij t) * y⁻¹ =
        ρ (SpecialLinearGroup.transvection hij (lam i j * t)) := by
    intro i j hij t
    rw [hε i j hij t, hμ i j hij, hε i j hij (lam i j * t)]
    congr 1
    simp only [hlam]
    ring
  have hlam3 : ∀ i a j, i ≠ a → a ≠ j → i ≠ j → lam i j = lam i a * lam a j := by
    intro i a j hia haj hij
    have h1 := tv_commutator hia haj hij (1 : K) 1
    have h2 : y * ρ (SpecialLinearGroup.transvection hij (1 * 1)) * y⁻¹ =
        ⁅y * ρ (SpecialLinearGroup.transvection hia 1) * y⁻¹,
          y * ρ (SpecialLinearGroup.transvection haj 1) * y⁻¹⁆ := by
      rw [← h1, map_commutatorElement]
      simp only [commutatorElement_def]
      group
    rw [key, key, key, ← map_commutatorElement, tv_commutator hia haj hij] at h2
    have h3 := tv_inj hij (hρi h2)
    simp only [mul_one] at h3
    exact h3
  set d : Fin 5 → K := fun i => if i = 0 then 1 else lam i 0 with hd
  have hdlam := exact_cocycle lam hlamne hlam3
  have hdne : ∀ i, d i ≠ 0 := fun i => by
    simp only [hd]
    split_ifs with h
    · exact one_ne_zero
    · exact hlamne i 0 h
  set du : Fin 5 → Kˣ := fun i => Units.mk0 (d i) (hdne i) with hdu
  refine ⟨du, fun A => ?_⟩
  have h : (MulAut.conj y).toMonoidHom.comp ρ = ρ.comp (conjDiagnHom du) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 5) (K := K)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      conjDiagnHom_apply]
    rw [key i j hij t, conjDiagn_transvection]
    congr 2
    have h1 : lam i j * d j = d i := by
      simp only [hd]
      exact hdlam i j hij
    simp only [hdu, Units.val_mk0, Units.val_inv_eq_inv_val]
    have hdj : d j ≠ 0 := hdne j
    have h2 : lam i j = d i * (d j)⁻¹ := by
      rw [← h1]
      field_simp
    rw [h2]
    ring
  have := DFunLike.congr_fun h A
  simpa [MulAut.conj_apply, conjDiagnHom_apply] using this

end DiagConj

section Reduce

variable {K : Type} [Field K] [Finite K]

theorem cj_le_of_swap {E : Subgroup (adjointGroup Tag.E8 K)} (hEN : E ≤ monomialN K)
    (hW : wImg K E = sylowW) {yA yB : adjointGroup Tag.E8 K} (hyAE : yA ∈ E) (hyBE : yB ∈ E)
    (hyA : rhoN K ⟨yA, hEN hyAE⟩ = e8FiveG1 ^ 4) (hyB : rhoN K ⟨yB, hEN hyBE⟩ = e8FiveG2)
    {Φ : adjointGroup Tag.E8 K} {w₂ : WeylGroup Tag.E8}
    (hA : ∃ h : Φ * yA * Φ⁻¹ ∈ monomialN K, rhoN K ⟨Φ * yA * Φ⁻¹, h⟩ = 1)
    (hB : ∃ h : Φ * yB * Φ⁻¹ ∈ monomialN K, rhoN K ⟨Φ * yB * Φ⁻¹, h⟩ = w₂)
    (hT : ∀ (e : adjointGroup Tag.E8 K) (he : e ∈ E), rhoN K ⟨e, hEN he⟩ = 1 → Φ * e * Φ⁻¹ = e) :
    ∃ h : cj Φ E ≤ monomialN K, wImg K (cj Φ E) ≤ Subgroup.zpowers w₂ := by
  obtain ⟨hAN, hAρ⟩ := hA
  obtain ⟨hBN, hBρ⟩ := hB
  have key : ∀ (e : adjointGroup Tag.E8 K) (he : e ∈ E), ∃ (hN : Φ * e * Φ⁻¹ ∈ monomialN K) (j : ℕ),
      rhoN K ⟨Φ * e * Φ⁻¹, hN⟩ = w₂ ^ j := by
    intro e he
    have hρe : rhoN K ⟨e, hEN he⟩ ∈ sylowW := by
      rw [← hW]
      exact mem_wImg.2 ⟨e, he, hEN he, rfl⟩
    obtain ⟨i', j', hij⟩ := exists_exp_of_mem_sylowW hρe
    set i : ℕ := 4 * (i' : ℕ) with hi
    set j : ℕ := (j' : ℕ) with hj
    obtain ⟨e', he'⟩ : ∃ e' : adjointGroup Tag.E8 K, e' = e * (yA ^ i * yB ^ j)⁻¹ := ⟨_, rfl⟩
    have hyAN : yA ∈ monomialN K := hEN hyAE
    have hyBN : yB ∈ monomialN K := hEN hyBE
    have he'E : e' ∈ E := by
      rw [he']
      exact mul_mem he (inv_mem (mul_mem (pow_mem hyAE i) (pow_mem hyBE j)))
    have he'N : e' ∈ monomialN K := hEN he'E
    have hρe' : rhoN K ⟨e', he'N⟩ = 1 := by
      have : (⟨e', he'N⟩ : monomialN K) = ⟨e, hEN he⟩ * (⟨yA, hyAN⟩ ^ i * ⟨yB, hyBN⟩ ^ j)⁻¹ :=
        Subtype.ext he'
      rw [this, map_mul, map_inv, map_mul, map_pow, map_pow, hyA, hyB, ← hij, hi, hj]
      have h1 : (e8FiveG1 ^ 4) ^ (4 * (i' : ℕ)) = e8FiveG1 ^ (i' : ℕ) := by
        rw [← pow_mul, show 4 * (4 * (i' : ℕ)) = 5 * (3 * (i' : ℕ)) + (i' : ℕ) by ring, pow_add,
          pow_mul, e8FiveG1_pow, one_pow, one_mul]
      rw [h1]
      group
    have hfix := hT e' he'E hρe'
    have hdec : Φ * e * Φ⁻¹ = e' * (Φ * yA * Φ⁻¹) ^ i * (Φ * yB * Φ⁻¹) ^ j := by
      have : e = e' * (yA ^ i * yB ^ j) := by rw [he']; group
      have h1 : (MulAut.conj Φ).toMonoidHom e =
          (MulAut.conj Φ).toMonoidHom (e' * (yA ^ i * yB ^ j)) := by rw [← this]
      simp only [map_mul, map_pow, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      rw [h1, hfix]
      exact (mul_assoc _ _ _).symm
    have hN : Φ * e * Φ⁻¹ ∈ monomialN K := by
      rw [hdec]
      exact mul_mem (mul_mem he'N (pow_mem hAN i)) (pow_mem hBN j)
    refine ⟨hN, j, ?_⟩
    have : (⟨Φ * e * Φ⁻¹, hN⟩ : monomialN K) = ⟨e', he'N⟩ * ⟨Φ * yA * Φ⁻¹, hAN⟩ ^ i *
        ⟨Φ * yB * Φ⁻¹, hBN⟩ ^ j := Subtype.ext hdec
    rw [this, map_mul, map_mul, map_pow, map_pow, hρe', hAρ, hBρ]
    simp
  have hle : cj Φ E ≤ monomialN K := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨hN, -, -⟩ := key e he
    exact hN
  refine ⟨hle, ?_⟩
  intro w hw
  obtain ⟨x, hx, hxN, rfl⟩ := mem_wImg.1 hw
  obtain ⟨e, he, rfl⟩ := hx
  obtain ⟨hN, j, hj⟩ := key e he
  have : rhoN K ⟨(MulAut.conj Φ).toMonoidHom e, hxN⟩ = w₂ ^ j := hj
  rw [this]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers w₂) j

end Reduce

section Weights

variable {K : Type} [Field K] [Finite K]

theorem g1_pow4_pow_smul_wbA (k : ℕ) (j : Fin 5) :
    (e8FiveG1 ^ 4) ^ k • wbE8A4 e8VA j = wbE8A4 e8VA (j + (k : Fin 5)) := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_smul, g1_pow4_smul_wbA, ih, Nat.cast_succ, add_assoc, add_comm 1,
      ← add_assoc]

theorem rootChar_wbA_const {y : ModGL Tag.E8 K} (hy : y ∈ monomialSubgroup Tag.E8 K)
    (hyw : weylQuotientHom Tag.E8 K ⟨y, hy⟩ = e8FiveG1 ^ 4) {b : Fin Tag.E8.rank → Kˣ}
    (hcomm : y * rootDiagUnit Tag.E8 b = rootDiagUnit Tag.E8 b * y) (i : Fin 5) :
    rootChar b (wbE8A4 e8VA i) = rootChar b (wbE8A4 e8VA 0) := by
  have hconj : y * rootDiagUnit Tag.E8 b * y⁻¹ = rootDiagUnit Tag.E8 b := by
    rw [hcomm]
    group
  have hact := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.monomial_conj_rootDiagUnit
    (⟨y, hy⟩ : monomialSubgroup Tag.E8 K) b
  rw [hyw] at hact
  have heq : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct (e8FiveG1 ^ 4) b = b :=
    rootDiagUnit_injective (hact.symm.trans hconj)
  have hstep : ∀ i : Fin 5, rootChar b (wbE8A4 e8VA (i + 1)) = rootChar b (wbE8A4 e8VA i) := by
    intro i
    have h1 := congrArg (fun b' => rootChar b' (wbE8A4 e8VA (i + 1))) heq
    simp only [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_weylAct] at h1
    have h2 : (e8FiveG1 ^ 4)⁻¹ • wbE8A4 e8VA (i + 1) = wbE8A4 e8VA i := by
      rw [inv_smul_eq_iff, g1_pow4_smul_wbA]
    rw [h2] at h1
    exact h1.symm
  have hall : ∀ n : ℕ, rootChar b (wbE8A4 e8VA (n : Fin 5)) = rootChar b (wbE8A4 e8VA 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, hstep, ih]
  have := hall (i : ℕ)
  rwa [Fin.cast_val_eq_self] at this

theorem rootDiagUnit_comm_rhoA {y : ModGL Tag.E8 K} (hy : y ∈ monomialSubgroup Tag.E8 K)
    (hyw : weylQuotientHom Tag.E8 K ⟨y, hy⟩ = e8FiveG1 ^ 4) {b : Fin Tag.E8.rank → Kˣ}
    (hcomm : y * rootDiagUnit Tag.E8 b = rootDiagUnit Tag.E8 b * y) (X : SL(5, K)) :
    rootDiagUnit Tag.E8 b * rhoA K X = rhoA K X * rootDiagUnit Tag.E8 b := by
  have h := rootDiagUnit_mul_rhoA b X
  have hconst : (fun i => rootChar b (wbE8A4 e8VA i)) = fun _ => rootChar b (wbE8A4 e8VA 0) :=
    funext (rootChar_wbA_const hy hyw hcomm)
  rw [hconst, conjDiagn_const _ (fun _ _ => rfl)] at h
  calc rootDiagUnit Tag.E8 b * rhoA K X = rootDiagUnit Tag.E8 b * rhoA K X *
        (rootDiagUnit Tag.E8 b)⁻¹ * rootDiagUnit Tag.E8 b := by group
    _ = rhoA K X * rootDiagUnit Tag.E8 b := by rw [h]

theorem prod_rootChar_wbA_eq_one {y : ModGL Tag.E8 K} (hy : y ∈ monomialSubgroup Tag.E8 K)
    (hyw : weylQuotientHom Tag.E8 K ⟨y, hy⟩ = e8FiveG1 ^ 4) (hy5 : y ^ 5 = 1)
    {a : Fin Tag.E8.rank → Kˣ} (h5 : (rootDiagUnit Tag.E8 a * y) ^ 5 = 1) :
    ∏ i : Fin 5, rootChar a (wbE8A4 e8VA i) = 1 := by
  rw [pow_rootDiagUnit_mul hy hyw a 5, hy5, mul_one] at h5
  have hP : (∏ k ∈ Finset.range 5, CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
      ((e8FiveG1 ^ 4) ^ k) a) = 1 :=
    rootDiagUnit_injective (h5.trans rootDiagUnit_one.symm)
  have hc : rootChar (∏ k ∈ Finset.range 5, CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
      ((e8FiveG1 ^ 4) ^ k) a) (wbE8A4 e8VA 0) = rootChar (1 : Fin Tag.E8.rank → Kˣ)
        (wbE8A4 e8VA 0) := by rw [hP]
  have hhom : ∀ b : Fin Tag.E8.rank → Kˣ, rootChar b (wbE8A4 e8VA 0) =
      CFSG.LieType.SeitzGeneration.ExcHighThree.rootCharHom (wbE8A4 e8VA 0) b := fun _ => rfl
  rw [hhom, map_prod] at hc
  simp only [← hhom, CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_weylAct] at hc
  have hk : ∀ k : ℕ, ((e8FiveG1 ^ 4) ^ k)⁻¹ • wbE8A4 e8VA 0 = wbE8A4 e8VA (-(k : Fin 5)) := by
    intro k
    rw [inv_smul_eq_iff, g1_pow4_pow_smul_wbA]
    congr 1
    simp
  simp only [hk] at hc
  have : ∏ k ∈ Finset.range 5, rootChar a (wbE8A4 e8VA (-(k : Fin 5))) =
      ∏ i : Fin 5, rootChar a (wbE8A4 e8VA i) := by
    rw [Finset.prod_range]
    simp only [Fin.cast_val_eq_self]
    exact Fintype.prod_equiv (Equiv.neg (Fin 5)) _ _ (fun i => rfl)
  rw [this] at hc
  simpa [rootChar] using hc

end Weights

section Scalars

variable {K : Type} [Field K] [Finite K]

theorem exists_shift_scalar {y : ModGL Tag.E8 K} (hy : y ∈ monomialSubgroup Tag.E8 K)
    (hyw : weylQuotientHom Tag.E8 K ⟨y, hy⟩ = e8FiveG1 ^ 4) (i j : Fin 5) (hij : i ≠ j) :
    ∃ κ : Kˣ, ∀ t : K, y * rhoA K (SpecialLinearGroup.transvection hij t) * y⁻¹ =
      rhoA K (SpecialLinearGroup.transvection ((add_left_injective (1 : Fin 5)).ne hij)
        ((κ : K) * t)) := by
  obtain ⟨ε, hε⟩ := rhoSigmaE8A4_transvection (L := K) e8VA i j hij
  obtain ⟨ε', hε'⟩ := rhoSigmaE8A4_transvection (L := K) e8VA (i + 1) (j + 1)
    ((add_left_injective (1 : Fin 5)).ne hij)
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hy (isRoot_sigmaRootE8A4 e8VA hij)
  rw [hyw, g1_pow4_smul_sigmaA] at hμ
  refine ⟨μ * ε * ε'⁻¹, fun t => ?_⟩
  show y * rhoSigmaE8A4 K e8VA _ * y⁻¹ = rhoSigmaE8A4 K e8VA _
  rw [hε, hμ, hε']
  congr 1
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem exists_fix_scalar {y : ModGL Tag.E8 K} (hy : y ∈ monomialSubgroup Tag.E8 K)
    (hyw : weylQuotientHom Tag.E8 K ⟨y, hy⟩ = e8FiveG2) :
    ∃ du : Fin 5 → Kˣ, ∀ A : SL(5, K), y * rhoA K A * y⁻¹ = rhoA K (conjDiagn du A) := by
  refine exists_diag_conj (rhoA K) rhoA_injective (sigmaRootE8A4 e8VA)
    (fun i j hij => rhoSigmaE8A4_transvection e8VA i j hij) fun i j hij => ?_
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hy (isRoot_sigmaRootE8A4 e8VA hij)
  rw [hyw, g2_smul_sigmaA] at hμ
  exact ⟨μ, hμ⟩

theorem conjDiagn_eq_diagSLn (d : Fin 5 → Kˣ) (hd : ∏ i, (d i : K) = 1) (X : SL(5, K)) :
    conjDiagn d X = diagSLn d hd * X * (diagSLn d hd)⁻¹ := by
  have hd' : ∏ i, ((((1 : Kˣ) * d i)⁻¹ : Kˣ) : K) = 1 := by
    simp only [one_mul, Units.val_inv_eq_inv_val]
    rw [Finset.prod_inv_distrib, hd, inv_one]
  have h := diagSLn_conj d 1 (by simpa using hd) hd' X
  simpa using h.symm

end Scalars

end One

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
