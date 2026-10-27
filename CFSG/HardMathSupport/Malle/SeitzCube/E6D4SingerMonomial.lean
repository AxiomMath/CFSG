module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6D4LineTransport
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3Torus
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3Sign
public import CFSG.RankThree.PartOne.KE.A1E8Frame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi3D4Case
public import CFSG.RankThree.PartOne.KE6.Phi3Frame
public import CFSG.RankThree.PartOne.KE6.Phi3Torsion
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KE6.Phi6Torsion
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.ClassicalInvolution.WeakCT
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

open scoped MatrixGroups

section Block

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K]

theorem conjSL_diagUnitOne_WSL (s : Kˣ) :
    CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) WSL = nSL s := by
  apply Subtype.ext
  rw [CFSG.RankThree.Classical.coe_conjSL, CFSG.RankThree.Classical.coe_diagUnitOne,
    CFSG.RankThree.Classical.coe_diagUnitOne_inv]
  change !![(s : K), 0; 0, 1] * !![(0 : K), 1; -1, 0] * !![((s⁻¹ : Kˣ) : K), 0; 0, 1] =
    !![(0 : K), (s : K); -((s⁻¹ : Kˣ) : K), 0]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem psi_block_WSL (i : Fin 3) (ψ : SL(3, K) →* ModGL Tag.E6 K) (c : Fin 2)
    (γp γn : Fin 2 → ℤ) (β : Fin Tag.E6.rank → ℤ) (hβ : IsRoot Tag.E6 β)
    (hp : γp ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2)))
    (hn : γn ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2)))
    (hFp : e6A2Frame i γp = β) (hFn : e6A2Frame i γn = -β)
    (hxp : ∀ t : K, CFSG.LieType.Steinberg.SL.x 2 K γp t =
      Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := c)).ne t)
    (hxn : ∀ t : K, CFSG.LieType.Steinberg.SL.x 2 K γn t =
      Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := c)).ne' t)
    (hψ : ∀ γ ∈ CFSG.LieType.RootSystem.roots
        (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2)), ∃ ε : Kˣ,
        ∀ c : K, ψ (CFSG.LieType.Steinberg.SL.x 2 K γ c) =
          pinnedX Tag.E6 K (e6A2Frame i γ) ((ε : K) * c)) :
    ∃ h : ψ (blockSL2 K 2 c WSL) ∈ monomialSubgroup Tag.E6 K,
      weylQuotientHom Tag.E6 K ⟨_, h⟩ = rootReflection β := by
  obtain ⟨a, ha⟩ := hψ γp hp
  obtain ⟨b, hb⟩ := hψ γn hn
  have hu : ∀ t : K, (ψ.comp (blockSL2 K 2 c)) (uSL t) = pinnedX Tag.E6 K β ((a : K) * t) := by
    intro t
    rw [MonoidHom.comp_apply, blockSL2_uSL_eq, ← hxp, ha, hFp]
  have hv : ∀ t : K, (ψ.comp (blockSL2 K 2 c)) (vSL t) = pinnedX Tag.E6 K (-β) ((b : K) * t) := by
    intro t
    rw [MonoidHom.comp_apply, blockSL2_vSL_eq, ← hxn, hb, hFn]
  obtain ⟨s, hs⟩ := exists_comp_conjSL_eq_rootSL2 hβ (ψ.comp (blockSL2 K 2 c)) a b hu hv
  have hW : (ψ.comp (blockSL2 K 2 c)) (nSL s) = rootSL2 Tag.E6 K β WSL := by
    have := DFunLike.congr_fun hs WSL
    rwa [MonoidHom.comp_apply, conjSL_diagUnitOne_WSL] at this
  have hH : (ψ.comp (blockSL2 K 2 c)) (HSL s) = rootSL2 Tag.E6 K β (HSL s) := by
    have := DFunLike.congr_fun hs (HSL s)
    rwa [MonoidHom.comp_apply, conjSL_diagUnitOne_HSL] at this
  have hsplit : (ψ.comp (blockSL2 K 2 c)) (WSL) =
      ((ψ.comp (blockSL2 K 2 c)) (HSL s))⁻¹ * rootSL2 Tag.E6 K β WSL := by
    rw [← hW, nSL_eq_HSL_mul, map_mul, inv_mul_cancel_left]
  obtain ⟨hmon, hmap⟩ := rootSL2_WSL_mem_monomial_gen (τ := Tag.E6) (L := K) hβ
  have hT : (ψ.comp (blockSL2 K 2 c)) (HSL s) ∈ torusGroup Tag.E6 K := by
    rw [hH]
    exact (exceptional_Lang_root_rank_one_torus_transport Tag.E6 K hβ).2.1 s
  have hTm : (ψ.comp (blockSL2 K 2 c)) (HSL s) ∈ monomialSubgroup Tag.E6 K :=
    Subgroup.mem_sup_left hT
  have hmem : ψ (blockSL2 K 2 c WSL) ∈ monomialSubgroup Tag.E6 K := by
    have h1 : (ψ.comp (blockSL2 K 2 c)) (WSL) ∈ monomialSubgroup Tag.E6 K := by
      rw [hsplit]
      exact mul_mem (inv_mem hTm) hmon
    exact h1
  refine ⟨hmem, ?_⟩
  have h1 : (⟨ψ (blockSL2 K 2 c WSL), hmem⟩ : monomialSubgroup Tag.E6 K) =
      ⟨_, inv_mem hTm⟩ * ⟨_, hmon⟩ := Subtype.ext hsplit
  rw [h1, map_mul, hmap]
  have hτ : weylQuotientHom Tag.E6 K ⟨_, inv_mem hTm⟩ = 1 :=
    weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup (inv_mem hT))
  rw [hτ, one_mul]

theorem psi_block_HSL_mem (i : Fin 3) (ψ : SL(3, K) →* ModGL Tag.E6 K) (c : Fin 2)
    (γp γn : Fin 2 → ℤ) (β : Fin Tag.E6.rank → ℤ) (hβ : IsRoot Tag.E6 β)
    (hp : γp ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2)))
    (hn : γn ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2)))
    (hFp : e6A2Frame i γp = β) (hFn : e6A2Frame i γn = -β)
    (hxp : ∀ t : K, CFSG.LieType.Steinberg.SL.x 2 K γp t =
      Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := c)).ne t)
    (hxn : ∀ t : K, CFSG.LieType.Steinberg.SL.x 2 K γn t =
      Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := c)).ne' t)
    (hψ : ∀ γ ∈ CFSG.LieType.RootSystem.roots
        (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2)), ∃ ε : Kˣ,
        ∀ c : K, ψ (CFSG.LieType.Steinberg.SL.x 2 K γ c) =
          pinnedX Tag.E6 K (e6A2Frame i γ) ((ε : K) * c)) (u : Kˣ) :
    ψ (blockSL2 K 2 c (HSL u)) ∈ torusGroup Tag.E6 K := by
  obtain ⟨a, ha⟩ := hψ γp hp
  obtain ⟨b, hb⟩ := hψ γn hn
  have hu : ∀ t : K, (ψ.comp (blockSL2 K 2 c)) (uSL t) = pinnedX Tag.E6 K β ((a : K) * t) := by
    intro t
    rw [MonoidHom.comp_apply, blockSL2_uSL_eq, ← hxp, ha, hFp]
  have hv : ∀ t : K, (ψ.comp (blockSL2 K 2 c)) (vSL t) = pinnedX Tag.E6 K (-β) ((b : K) * t) := by
    intro t
    rw [MonoidHom.comp_apply, blockSL2_vSL_eq, ← hxn, hb, hFn]
  obtain ⟨s, hs⟩ := exists_comp_conjSL_eq_rootSL2 hβ (ψ.comp (blockSL2 K 2 c)) a b hu hv
  have hH : (ψ.comp (blockSL2 K 2 c)) (HSL u) = rootSL2 Tag.E6 K β (HSL u) := by
    have := DFunLike.congr_fun hs (HSL u)
    rwa [MonoidHom.comp_apply, conjSL_diagUnitOne_HSL] at this
  have h1 : ψ (blockSL2 K 2 c (HSL u)) = rootSL2 Tag.E6 K β (HSL u) := hH
  rw [h1]
  exact (exceptional_Lang_root_rank_one_torus_transport Tag.E6 K hβ).2.1 u

theorem prod_rootReflection_frame_eq :
    ([e6A2Simple₀ 0, e6A2Simple₁ 0, e6A2Simple₀ 1, e6A2Simple₁ 1, e6A2Simple₀ 2,
        e6A2Simple₁ 2].map (rootReflection (τ := Tag.E6))).prod = e6D4wp := by
  have hroots : ∀ γ ∈ [e6A2Simple₀ 0, e6A2Simple₁ 0, e6A2Simple₀ 1, e6A2Simple₁ 1, e6A2Simple₀ 2,
      e6A2Simple₁ 2], IsRoot Tag.E6 γ := by
    intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact isRoot_e6A2Simple₀ _ | exact isRoot_e6A2Simple₁ _
  refine eq_of_smul_single_eq fun j => ?_
  rw [list_prod_rootReflection_smul (τ := Tag.E6) rfl _ hroots, e6D4wp, wordProd_e6Word_smul]
  revert j
  decide +kernel

open CFSG.ClassicalInvolution.Phan (blockMat_apply) 
in
theorem coe_blockSL2_WSL_zero :
    ((blockSL2 K 2 0 WSL : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  rw [blockSL2, coe_blockSL]
  ext a b
  rw [blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp [WSL]

open CFSG.ClassicalInvolution.Phan (blockMat_apply) 
in
theorem coe_blockSL2_WSL_one :
    ((blockSL2 K 2 1 WSL : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, 0, 1; 0, -1, 0] := by
  rw [blockSL2, coe_blockSL]
  ext a b
  rw [blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp [WSL]

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

theorem psi_M_monomial (i : Fin 3) (ψ : SL(3, K) →* ModGL Tag.E6 K)
    (hψ : ∀ γ ∈ RA2, ∃ ε : Kˣ, ∀ c : K, ψ (CFSG.LieType.Steinberg.SL.x 2 K γ c) =
      pinnedX Tag.E6 K (e6A2Frame i γ) ((ε : K) * c))
    (M : SL(3, K)) (d : Fin 3 → Kˣ)
    (hM : (M : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal (fun j => (d j : K)) *
      Matrix.of (fun a b => if a = b + 1 then 1 else 0)) :
    ∃ h : ψ M ∈ monomialSubgroup Tag.E6 K,
      weylQuotientHom Tag.E6 K ⟨_, h⟩ =
        rootReflection (e6A2Simple₀ i) * rootReflection (e6A2Simple₁ i) := by
  set t : Fin 3 → Kˣ := ![-d 1, -d 2, d 0] with ht
  have hdet : (M : Matrix (Fin 3) (Fin 3) K).det = (d 0 : K) * d 1 * d 2 := by
    rw [hM, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three, Matrix.det_fin_three]
    simp
  have hdetD : Matrix.det (Matrix.diagonal fun j => (t j : K)) = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    have := M.2
    rw [hdet] at this
    simp only [ht, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_neg]
    have h2 : ((![-d 1, -d 2, d 0] : Fin 3 → Kˣ) 2 : K) = d 0 := rfl
    rw [h2]
    linear_combination this
  set Dd : SL(3, K) := ⟨Matrix.diagonal fun j => (t j : K), hdetD⟩ with hDd
  have hdec : M = blockSL2 K 2 0 WSL * blockSL2 K 2 1 WSL * Dd := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_blockSL2_WSL_zero, coe_blockSL2_WSL_one, hM]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, hDd, ht, Matrix.diagonal_apply]
  have hb0 := psi_block_WSL i ψ 0 ![1, 0] ![-1, 0] (e6A2Simple₀ i) (isRoot_e6A2Simple₀ i)
    (mem_RA2_of_toStd (i := 0) (j := 1) (by decide) (by decide))
    (mem_RA2_of_toStd (i := 1) (j := 0) (by decide) (by decide))
    (e6A2_frame_pos i).1 (e6A2_frame_pos i).2.2.1
    (fun t => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) t)
    (fun t => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) t) hψ
  have hb1 := psi_block_WSL i ψ 1 ![0, 1] ![0, -1] (e6A2Simple₁ i) (isRoot_e6A2Simple₁ i)
    (mem_RA2_of_toStd (i := 1) (j := 2) (by decide) (by decide))
    (mem_RA2_of_toStd (i := 2) (j := 1) (by decide) (by decide))
    (e6A2_frame_pos i).2.1 (e6A2_frame_pos i).2.2.2
    (fun t => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) t)
    (fun t => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) t) hψ
  obtain ⟨h0, w0⟩ := hb0
  obtain ⟨h1, w1⟩ := hb1
  have hAdec : Dd = blockSL2 K 2 0 (HSL (t 0)) * blockSL2 K 2 1 (HSL (t 0 * t 1)) := by
    apply Subtype.ext
    have hDcoe : (Dd : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal fun j => (t j : K) := rfl
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL2_HSL, coe_blockSL2_HSL, hDcoe,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    fin_cases j
    · simp
    · simp
    · simp
      have h0 : (t 0 : K) ≠ 0 := (t 0).ne_zero
      have h1 : (t 1 : K) ≠ 0 := (t 1).ne_zero
      have hd3 : (t 0 : K) * t 1 * t 2 = 1 := by
        have := hdetD
        rwa [Matrix.det_diagonal, Fin.prod_univ_three] at this
      field_simp
      linear_combination hd3
  have hb0T := psi_block_HSL_mem i ψ 0 ![1, 0] ![-1, 0] (e6A2Simple₀ i) (isRoot_e6A2Simple₀ i)
    (mem_RA2_of_toStd (i := 0) (j := 1) (by decide) (by decide))
    (mem_RA2_of_toStd (i := 1) (j := 0) (by decide) (by decide))
    (e6A2_frame_pos i).1 (e6A2_frame_pos i).2.2.1
    (fun t => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) t)
    (fun t => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) t) hψ (t 0)
  have hb1T := psi_block_HSL_mem i ψ 1 ![0, 1] ![0, -1] (e6A2Simple₁ i) (isRoot_e6A2Simple₁ i)
    (mem_RA2_of_toStd (i := 1) (j := 2) (by decide) (by decide))
    (mem_RA2_of_toStd (i := 2) (j := 1) (by decide) (by decide))
    (e6A2_frame_pos i).2.1 (e6A2_frame_pos i).2.2.2
    (fun t => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) t)
    (fun t => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) t) hψ (t 0 * t 1)
  have hDT : ψ Dd ∈ torusGroup Tag.E6 K := by
    rw [hAdec, map_mul]
    exact mul_mem hb0T hb1T
  have hDm : ψ Dd ∈ monomialSubgroup Tag.E6 K := Subgroup.mem_sup_left hDT
  have hmem : ψ M ∈ monomialSubgroup Tag.E6 K := by
    rw [hdec, map_mul, map_mul]
    exact mul_mem (mul_mem h0 h1) hDm
  refine ⟨hmem, ?_⟩
  have e : (⟨ψ M, hmem⟩ : monomialSubgroup Tag.E6 K) =
      ⟨_, h0⟩ * ⟨_, h1⟩ * ⟨_, hDm⟩ :=
    Subtype.ext (show ψ M = ψ _ * ψ _ * ψ Dd by rw [hdec, map_mul, map_mul])
  have hτ : weylQuotientHom Tag.E6 K ⟨_, hDm⟩ = 1 :=
    weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup hDT)
  rw [e, map_mul, map_mul, w0, w1, hτ, mul_one]

theorem e6D4_singer_monomial {Ω : Type} [Field Ω]
    (ψ : Fin 3 → SL(3, Ω) →* adjointGroup Tag.E6 Ω)
    (hψ : ∀ i : Fin 3, ∀ γ ∈ RA2, ∀ c : Ω,
      ((ψ i (CFSG.LieType.Steinberg.SL.x 2 Ω γ c) : adjointGroup Tag.E6 Ω) : ModGL Tag.E6 Ω) =
        pinnedX Tag.E6 Ω (e6A2Frame i γ) ((e6A2Sign i γ : Ω) * c))
    (M : SL(3, Ω)) (d : Fin 3 → Ωˣ)
    (hM : (M : Matrix (Fin 3) (Fin 3) Ω) = Matrix.diagonal (fun i => (d i : Ω)) *
      Matrix.of (fun i j => if i = j + 1 then 1 else 0)) :
    ∃ hn' : (((ψ 0 M * ψ 1 M * ψ 2 M : adjointGroup Tag.E6 Ω)) : ModGL Tag.E6 Ω) ∈
        monomialSubgroup Tag.E6 Ω,
      weylQuotientHom Tag.E6 Ω ⟨_, hn'⟩ = e6D4wp := by
  have hψ' : ∀ i : Fin 3, ∀ γ ∈ RA2, ∃ ε : Ωˣ, ∀ c : Ω,
      ((adjointGroup Tag.E6 Ω).subtype.comp (ψ i)) (CFSG.LieType.Steinberg.SL.x 2 Ω γ c) =
        pinnedX Tag.E6 Ω (e6A2Frame i γ) ((ε : Ω) * c) := by
    intro i γ hγ
    have hss : (e6A2Sign i γ : Ω) * (e6A2Sign i γ : Ω) = 1 := by
      rcases e6A2Sign_eq i γ with h | h <;> rw [h] <;> simp
    exact ⟨Units.mkOfMulEqOne _ _ hss, hψ i γ hγ⟩
  have key : ∀ i : Fin 3, ∃ h : (((ψ i M : adjointGroup Tag.E6 Ω)) : ModGL Tag.E6 Ω) ∈
      monomialSubgroup Tag.E6 Ω, weylQuotientHom Tag.E6 Ω ⟨_, h⟩ =
        rootReflection (e6A2Simple₀ i) * rootReflection (e6A2Simple₁ i) := fun i =>
    psi_M_monomial i ((adjointGroup Tag.E6 Ω).subtype.comp (ψ i)) (hψ' i) M d hM
  obtain ⟨h0, w0⟩ := key 0
  obtain ⟨h1, w1⟩ := key 1
  obtain ⟨h2, w2⟩ := key 2
  have hmem : (((ψ 0 M * ψ 1 M * ψ 2 M : adjointGroup Tag.E6 Ω)) : ModGL Tag.E6 Ω) ∈
      monomialSubgroup Tag.E6 Ω := mul_mem (mul_mem h0 h1) h2
  refine ⟨hmem, ?_⟩
  have e : (⟨_, hmem⟩ : monomialSubgroup Tag.E6 Ω) = ⟨_, h0⟩ * ⟨_, h1⟩ * ⟨_, h2⟩ := rfl
  rw [e, map_mul, map_mul, w0, w1, w2, ← prod_rootReflection_frame_eq]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]

end Block

end CFSG.HardMathSupport.Malle.SeitzCube
