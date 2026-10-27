module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoCalc
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoWeyl

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.CatLeafProof (weylWordElt)
open CFSG.RankThree.Chevalley (wordAct wordSign wordRep wordRep_conj_pinnedX wordSign_eq_one_or
  wordAct_eq_smul)
open CFSG.RankThree.E6 (chain13 chainRoot support13 mem_support13 e6Index a2Equiv₁ a2Mat₁
  a2Equiv₁_apply coe_a2Rep₁)
open CFSG.HardMathSupport.Malle.SeitzCube (chainRoot13_eq)
open CFSG.RankThree.Classical2 (exists_sl3_root_permuting_of_theta a2Mat₁_pinnedX_chainRoot13
  pinnedX_chainRoot13_mem exists_conj_map_of_root_permuting)
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Hom

variable {K : Type*} [Field K] {G : Type*} [Group G]

theorem bmN_map_range_eq (φ : Multiplicative K →* G) (f : MulAut G) {u : K} (hu : u ≠ 0)
    (h : ∀ t : K, f (φ (Multiplicative.ofAdd t)) = φ (Multiplicative.ofAdd (u * t))) :
    φ.range.map f.toMonoidHom = φ.range := by
  ext g
  constructor
  · intro hg
    obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hg
    exact ⟨_, (h (Multiplicative.toAdd t)).symm⟩
  · rintro ⟨t, rfl⟩
    refine Subgroup.mem_map.2
      ⟨φ (Multiplicative.ofAdd (u⁻¹ * Multiplicative.toAdd t)), ⟨_, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, h, mul_inv_cancel_left₀ hu]
    rfl

theorem bmN_range_ne_bot (φ : Multiplicative K →* G) (h : φ (Multiplicative.ofAdd 1) ≠ 1) :
    φ.range ≠ ⊥ := fun hR => h (by
  have hmem : φ (Multiplicative.ofAdd 1) ∈ φ.range := ⟨_, rfl⟩
  rwa [hR, Subgroup.mem_bot] at hmem)

theorem bmN_isPGroup_range (φ : Multiplicative K →* G) : IsPGroup (ringChar K) φ.range := by
  have hK : IsPGroup (ringChar K) (Multiplicative K) := fun g => ⟨1, by
    rw [pow_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]⟩
  exact hK.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective

end Hom

section Mat

variable {K : Type*} [Field K]

theorem bmN_fin3_funext {v w : Fin 3 → K} (h0 : v 0 = w 0) (h1 : v 1 = w 1) (h2 : v 2 = w 2) :
    v = w := by
  funext k
  fin_cases k
  exacts [h0, h1, h2]

theorem bmN_mat_ext {M N : Matrix (Fin 3) (Fin 3) K}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1) (h02 : M 0 2 = N 0 2)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) (h12 : M 1 2 = N 1 2)
    (h20 : M 2 0 = N 2 0) (h21 : M 2 1 = N 2 1) (h22 : M 2 2 = N 2 2) : M = N := by
  ext r c
  fin_cases r <;> fin_cases c
  exacts [h00, h01, h02, h10, h11, h12, h20, h21, h22]

theorem bmN_exists_hom {N : Matrix (Fin 3) (Fin 3) K} (hN : N * N = 0)
    (hdet : ∀ t : K, (1 + t • N).det = 1) :
    ∃ u : Multiplicative K →* SL(3, K), ∀ t : K,
      ((u (Multiplicative.ofAdd t) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = 1 + t • N := by
  refine ⟨{ toFun := fun t => ⟨1 + Multiplicative.toAdd t • N, hdet _⟩
            map_one' := Subtype.ext ?_
            map_mul' := fun s t => Subtype.ext ?_ }, fun t => rfl⟩
  · show 1 + Multiplicative.toAdd (1 : Multiplicative K) • N = 1
    rw [toAdd_one, zero_smul, add_zero]
  · show 1 + Multiplicative.toAdd (s * t) • N =
      (1 + Multiplicative.toAdd s • N) * (1 + Multiplicative.toAdd t • N)
    simp only [toAdd_mul, add_smul, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hN, smul_zero, add_zero]
    abel

theorem bmN_conj_one_add {A : Matrix.GeneralLinearGroup (Fin 3) K}
    {N : Matrix (Fin 3) (Fin 3) K} {c : K}
    (h : (A : Matrix (Fin 3) (Fin 3) K) * N = c • (N * A)) (t : K) :
    (A : Matrix (Fin 3) (Fin 3) K) * (1 + t • N) * (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) =
      1 + (c * t) • N := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, h, smul_smul, Matrix.add_mul, A.mul_inv,
    Matrix.smul_mul, Matrix.mul_assoc, A.mul_inv, Matrix.mul_one, mul_comm t c]

theorem bmN_apply_eq_ite {A : Matrix.GeneralLinearGroup (Fin 3) K} {i j k l : Fin 3} {β : K}
    (h : (A : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.single i j 1) *
      (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) =
      1 + Matrix.single k l β) (r : Fin 3) :
    (A : Matrix (Fin 3) (Fin 3) K) r i =
      if r = k then β * (A : Matrix (Fin 3) (Fin 3) K) l j else 0 := by
  have h' : (A : Matrix (Fin 3) (Fin 3) K) * Matrix.single i j 1 =
      Matrix.single k l β * (A : Matrix (Fin 3) (Fin 3) K) := by
    have e := congrArg (· * (A : Matrix (Fin 3) (Fin 3) K)) h
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul,
      Matrix.one_mul] at e
    exact add_left_cancel e
  have e := congrFun₂ h' r j
  rw [Matrix.mul_single_apply_same, mul_one] at e
  rw [e]
  split_ifs with hr
  · rw [hr, Matrix.single_mul_apply_same]
  · exact Matrix.single_mul_apply_of_ne (c := β) _ _ _ _ hr _

theorem bmN_eq_smul_gamma {A : Matrix.GeneralLinearGroup (Fin 3) K} {β₀₁ β₁₀ β₂₀ : K}
    (h01 : (A : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.single 0 1 1) *
      (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.single 2 0 β₀₁)
    (h10 : (A : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.single 1 0 1) *
      (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.single 0 2 β₁₀)
    (h20 : (A : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.single 2 0 1) *
      (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.single 1 2 β₂₀) :
    (A : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) 2 0 • !![0, β₁₀, 0; 0, 0, β₂₀; 1, 0, 0] := by
  have e0 := bmN_apply_eq_ite h01
  have e1 := bmN_apply_eq_ite h10
  have e2 := bmN_apply_eq_ite h20
  have z00 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 = 0 := (e0 0).trans (if_neg (by decide))
  have z10 : (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := (e0 1).trans (if_neg (by decide))
  have z11 : (A : Matrix (Fin 3) (Fin 3) K) 1 1 = 0 := (e1 1).trans (if_neg (by decide))
  have z21 : (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := (e1 2).trans (if_neg (by decide))
  have z02 : (A : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := (e2 0).trans (if_neg (by decide))
  have z22 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 = 0 := (e2 2).trans (if_neg (by decide))
  have v01 : (A : Matrix (Fin 3) (Fin 3) K) 0 1 = (A : Matrix (Fin 3) (Fin 3) K) 2 0 * β₁₀ :=
    ((e1 0).trans (if_pos rfl)).trans (mul_comm _ _)
  have v12 : (A : Matrix (Fin 3) (Fin 3) K) 1 2 = (A : Matrix (Fin 3) (Fin 3) K) 2 0 * β₂₀ :=
    ((e2 1).trans (if_pos rfl)).trans (mul_comm _ _)
  refine bmN_mat_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val, smul_eq_mul, mul_zero,
      mul_one, z00, z10, z11, z21, z02, z22, v01, v12]

theorem bmN_exists_nilp {ε₁ ε₂ ω : K} (h₁ : ε₁ * ε₁ = 1) (h₂ : ε₂ * ε₂ = 1)
    (hω : 1 + ω + ω ^ 2 = 0) (d : K) :
    ∃ N : Matrix (Fin 3) (Fin 3) K, N ≠ 0 ∧ N * N = 0 ∧ (∀ t : K, (1 + t • N).det = 1) ∧
      (d • !![0, ε₁, 0; 0, 0, ε₂; 1, 0, 0]) * N =
        ω ^ 2 • (N * d • !![0, ε₁, 0; 0, 0, ε₂; 1, 0, 0]) := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  obtain ⟨γ, hγ⟩ : ∃ γ : Matrix (Fin 3) (Fin 3) K, γ = !![0, ε₁, 0; 0, 0, ε₂; 1, 0, 0] :=
    ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → K, v = ![1, ε₂, ε₁ * ε₂] := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : Fin 3 → K, f = ![1, ε₂ * ω ^ 2, ε₁ * ε₂ * ω] := ⟨_, rfl⟩
  rw [← hγ]
  have hfv : f ⬝ᵥ v = 0 := by
    rw [hf, hv]
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val]
    linear_combination hω + (ω ^ 2 + ω) * h₂ + ω * ε₂ * ε₂ * h₁
  have hγv : γ *ᵥ v = (ε₁ * ε₂) • v := by
    refine bmN_fin3_funext ?_ ?_ ?_ <;>
      simp only [hγ, hv, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val, Pi.smul_apply, smul_eq_mul]
    · ring
    · ring
    · linear_combination (-(ε₂ * ε₂)) * h₁ - h₂
  have hfγ : f ᵥ* γ = (ε₁ * ε₂ * ω) • f := by
    refine bmN_fin3_funext ?_ ?_ ?_ <;>
      simp only [hγ, hf, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val, Pi.smul_apply, smul_eq_mul]
    · ring
    · linear_combination (-ε₁) * h₂ - ε₁ * ε₂ * ε₂ * hω3
    · linear_combination (-(ε₂ * ε₂ * ω ^ 2)) * h₁
  refine ⟨Matrix.vecMulVec v f, fun h => ?_, ?_, fun t => ?_, ?_⟩
  · have h0 := congrFun₂ h 0 0
    rw [Matrix.vecMulVec_apply, hv, hf] at h0
    simp at h0
  · rw [Matrix.vecMulVec_mul_vecMulVec, hfv, zero_smul, Matrix.vecMulVec_zero]
  · rw [← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq Unit,
      Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hfv, smul_zero, add_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_vecMulVec, hγv, Matrix.vecMulVec_mul, hfγ,
      Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    linear_combination (-(d * ε₁ * ε₂)) * hω3

end Mat

def bmNPerm : Equiv.Perm (Fin 3) where
  toFun := bmPi
  invFun := ![1, 2, 0]
  left_inv x := by fin_cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

section Chevalley


section Field

variable {K : Type} [Field K]

theorem bmN_coe_rootDiagAutHom (e : Fin Tag.E6.rank → Kˣ) (g : adjointGroup Tag.E6 K) :
    ((rootDiagAutHom .E6 K e g : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      rootDiagUnit Tag.E6 e * g * (rootDiagUnit Tag.E6 e)⁻¹ :=
  rfl

theorem bmN_exists_rootHom (β : Fin Tag.E6.rank → ℤ) :
    ∃ ψ : Multiplicative K →* adjointGroup Tag.E6 K, ∀ t : K,
      ((ψ (Multiplicative.ofAdd t) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        pinnedX Tag.E6 K β t := by
  refine ⟨{ toFun := fun t => ⟨pinnedX Tag.E6 K β (Multiplicative.toAdd t),
              pinnedX_mem_adjointGroup β _⟩
            map_one' := Subtype.ext ?_
            map_mul' := fun s t => Subtype.ext ?_ }, fun t => rfl⟩
  · show pinnedX Tag.E6 K β (Multiplicative.toAdd (1 : Multiplicative K)) = 1
    rw [toAdd_one, pinnedX_zero]
  · show pinnedX Tag.E6 K β (Multiplicative.toAdd (s * t)) =
      pinnedX Tag.E6 K β (Multiplicative.toAdd s) * pinnedX Tag.E6 K β (Multiplicative.toAdd t)
    rw [toAdd_mul, pinnedX_add]

theorem bmN_wordAct (i j : Fin 3) :
    wordAct Tag.E6 e6BadWord (chainRoot chain13 i j) =
      chainRoot chain13 (bmNPerm i) (bmNPerm j) := by
  rw [wordAct_eq_smul, chainRoot13_eq, chainRoot13_eq, bm_smul_e6A2Root]
  rfl

theorem bmN_subsystemGroup13_le :
    subsystemGroup Tag.E6 K support13 ≤ adjointGroup Tag.E6 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, -, c, rfl | rfl⟩
  exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]

theorem bmN_rootDiagUnit_conj {a : Fin Tag.E6.rank → Kˣ} (ha0 : a 0 = 1) (ha2 : a 2 = 1)
    {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support13) :
    rootDiagUnit Tag.E6 a * g * (rootDiagUnit Tag.E6 a)⁻¹ = g := by
  rw [subsystemGroup_eq_rootSpan] at hg
  refine conj_eq_iff_mem_centralizer.2 (rootSpan_le_centralizer a (fun α hα => ⟨hα.1, ?_⟩) hg)
  show ∏ i, a i ^ α i = 1
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases hi : i ∈ support13
  · rcases (mem_support13 i).1 hi with rfl | rfl
    · rw [show a (e6Index 0) = 1 from ha0, _root_.one_zpow]
    · rw [show a (e6Index 2) = 1 from ha2, _root_.one_zpow]
  · rw [hα.2 i hi, zpow_zero]

theorem bmN_rootDiagAutHom_apply {a : Fin Tag.E6.rank → Kˣ} (ha0 : a 0 = 1) (ha2 : a 2 = 1)
    (g : adjointGroup Tag.E6 K)
    (hg : (g : ModGL Tag.E6 K) ∈ subsystemGroup Tag.E6 K support13) :
    rootDiagAutHom .E6 K a g = g :=
  Subtype.ext ((bmN_coe_rootDiagAutHom a g).trans (bmN_rootDiagUnit_conj ha0 ha2 hg))

theorem bmN_X_apply {b : Fin Tag.E6.rank → Kˣ} (hb0 : b 0 = 1) (hb2 : b 2 = 1)
    (g : adjointGroup Tag.E6 K)
    (hg : (g : ModGL Tag.E6 K) ∈ subsystemGroup Tag.E6 K support13) :
    (((MulAut.conj (weylWordElt .E6 K e6BadWord) * rootDiagAutHom .E6 K b) g :
      adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      (wordRep Tag.E6 K e6BadWord : ModGL Tag.E6 K) * g * (wordRep Tag.E6 K e6BadWord)⁻¹ := by
  rw [MulAut.mul_apply, bmN_rootDiagAutHom_apply hb0 hb2 g hg, MulAut.conj_apply,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_weylWordElt]

theorem bmN_coe_a2Equiv₁ (g : subsystemGroup Tag.E6 K support13) :
    ((a2Equiv₁ K g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = a2Mat₁ (g : ModGL Tag.E6 K) := by
  rw [a2Equiv₁_apply, coe_a2Rep₁]

theorem bmN_exists_mono :
    ∃ (A : Matrix.GeneralLinearGroup (Fin 3) K) (ε₁ ε₂ d : K), ε₁ * ε₁ = 1 ∧ ε₂ * ε₂ = 1 ∧
      (A : Matrix (Fin 3) (Fin 3) K) = d • !![0, ε₁, 0; 0, 0, ε₂; 1, 0, 0] ∧
      ∀ g ∈ subsystemGroup Tag.E6 K support13,
        (wordRep Tag.E6 K e6BadWord : ModGL Tag.E6 K) * g * (wordRep Tag.E6 K e6BadWord)⁻¹ ∈
          subsystemGroup Tag.E6 K support13 ∧
        a2Mat₁ ((wordRep Tag.E6 K e6BadWord : ModGL Tag.E6 K) * g *
          (wordRep Tag.E6 K e6BadWord)⁻¹) =
          (A : Matrix (Fin 3) (Fin 3) K) * a2Mat₁ g * (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨θ', hθinj, hθ'⟩ : ∃ θ' : ModGL Tag.E6 K →* ModGL Tag.E6 K, Function.Injective θ' ∧
      ∀ g, θ' g = (wordRep Tag.E6 K e6BadWord : ModGL Tag.E6 K) * g *
        (wordRep Tag.E6 K e6BadWord)⁻¹ :=
    ⟨(MulAut.conj (wordRep Tag.E6 K e6BadWord : ModGL Tag.E6 K)).toMonoidHom,
      fun _ _ h => (MulAut.conj _).injective h, fun _ => rfl⟩
  have hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : K, e * e = 1 ∧ ∀ c : K,
      θ' (pinnedX Tag.E6 K (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 K (chainRoot chain13 (bmNPerm i) (bmNPerm j)) (e * RingHom.id K c) := by
    intro i j hij
    have hα := (CFSG.RankThree.Classical2.chainRoot13_mem_parabolicRoots hij).1
    refine ⟨_, CFSG.RankThree.Classical2.sign_mul_self (wordSign_eq_one_or e6BadWord hα),
      fun c => ?_⟩
    rw [hθ', wordRep_conj_pinnedX K e6BadWord hα c, RingHom.id_apply, bmN_wordAct i j]
  obtain ⟨hQ, Φ, hΦ, b, hb⟩ := exists_sl3_root_permuting_of_theta (Fr := RingHom.id K)
    (fun x => ⟨x, rfl⟩) θ' hθinj bmNPerm hθ
  obtain ⟨A, hA⟩ := exists_conj_map_of_root_permuting (le_refl 3) (RingHom.id K) bmNPerm
    Φ.toMonoidHom b hb
  have hconj : ∀ g ∈ subsystemGroup Tag.E6 K support13,
      a2Mat₁ (θ' g) = (A : Matrix (Fin 3) (Fin 3) K) * a2Mat₁ g *
        (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) := by
    intro g hg
    have h1 := hA (a2Equiv₁ K ⟨g, hg⟩)
    rw [RingHom.coe_id, Matrix.map_id, bmN_coe_a2Equiv₁] at h1
    rw [← hΦ ⟨g, hg⟩]
    exact h1
  have hpair : ∀ i j : Fin 3, i ≠ j → ∃ β : K, β * β = 1 ∧
      (A : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.single i j 1) *
        (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.single (bmNPerm i) (bmNPerm j) β := by
    intro i j hij
    obtain ⟨s, hs, hs'⟩ := a2Mat₁_pinnedX_chainRoot13 (Ω := K) hij
    obtain ⟨s', hs2, hs2'⟩ := a2Mat₁_pinnedX_chainRoot13 (Ω := K) (bmNPerm.injective.ne hij)
    obtain ⟨e, he, hec⟩ := hθ i j hij
    have h1 := CFSG.RankThree.Classical2.sign_mul_self (R := K) hs
    have h2 := CFSG.RankThree.Classical2.sign_mul_self (R := K) hs2
    refine ⟨(s' : K) * (e * s), ?_, ?_⟩
    · linear_combination (e * e * (s : K) * s) * h2 + ((s : K) * s) * he + h1
    · have h3 := hconj _ (pinnedX_chainRoot13_mem (Ω := K) hij (s : K))
      rw [hs' (s : K), h1, hec, RingHom.id_apply, hs2'] at h3
      exact h3.symm
  obtain ⟨β₀₁, -, h01⟩ := hpair 0 1 (by decide)
  obtain ⟨β₁₀, hβ₁₀, h10⟩ := hpair 1 0 (by decide)
  obtain ⟨β₂₀, hβ₂₀, h20⟩ := hpair 2 0 (by decide)
  refine ⟨A, β₁₀, β₂₀, _, hβ₁₀, hβ₂₀, bmN_eq_smul_gamma h01 h10 h20, fun g hg => ⟨?_, ?_⟩⟩
  · rw [← hθ']
    exact hQ g hg
  · rw [← hθ']
    exact hconj g hg

end Field

theorem bm_normalizes_rootSubgroup {K : Type} [Field K] [Finite K]
    {ν : List (Fin Tag.E6.rank)} (a : Fin Tag.E6.rank → Kˣ) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot .E6 β) (hν : (coxeterSystem .E6).wordProd ν • β = β) :
    ∃ R : Subgroup (adjointGroup Tag.E6 K), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
      (∀ e : Fin Tag.E6.rank → Kˣ, R.map (rootDiagAutHom .E6 K e).toMonoidHom = R) ∧
      R.map (MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom .E6 K a).toMonoidHom = R := by
  obtain ⟨ψ, hψ⟩ := bmN_exists_rootHom (K := K) β
  have hd : ∀ (e : Fin Tag.E6.rank → Kˣ) (t : K),
      rootDiagAutHom .E6 K e (ψ (Multiplicative.ofAdd t)) =
        ψ (Multiplicative.ofAdd ((rootChar e β : K) * t)) := fun e t => Subtype.ext (by
    rw [bmN_coe_rootDiagAutHom, hψ, hψ, rootDiagUnit_conj_pinnedX e hβ t])
  have hs := CFSG.RankThree.Classical2.sign_mul_self (R := K) (wordSign_eq_one_or ν hβ)
  have hX : ∀ t : K,
      (MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom .E6 K a) (ψ (Multiplicative.ofAdd t)) =
        ψ (Multiplicative.ofAdd ((wordSign Tag.E6 ν β : K) * (rootChar a β : K) * t)) :=
    fun t => Subtype.ext (by
      rw [MulAut.mul_apply, hd a t, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_weylWordElt, hψ, hψ, wordRep_conj_pinnedX K ν hβ, wordAct_eq_smul,
        hν, mul_assoc])
  refine ⟨ψ.range, bmN_range_ne_bot ψ fun h => ?_, bmN_isPGroup_range ψ,
    fun e => bmN_map_range_eq ψ _ (Units.ne_zero _) (hd e),
    bmN_map_range_eq ψ _ (mul_ne_zero (left_ne_zero_of_mul_eq_one hs) (Units.ne_zero _)) hX⟩
  exact one_ne_zero (pinnedX_injective Tag.E6 K β
    ((hψ 1).symm.trans ((congrArg Subtype.val h).trans (pinnedX_zero Tag.E6 K β).symm)))

theorem e6BadParabolic_normalizes {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    (b : Fin Tag.E6.rank → Kˣ) (hb0 : b 0 = 1) (hb2 : b 2 = 1) :
    ∃ R : Subgroup (adjointGroup Tag.E6 K), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
      R.map (MulAut.conj (e6LineElt ω)).toMonoidHom = R ∧
      R.map (rootDiagAutHom .E6 K (e6D0Char ω)).toMonoidHom = R ∧
      R.map (MulAut.conj (weylWordElt .E6 K e6BadWord) * rootDiagAutHom .E6 K b).toMonoidHom =
        R := by
  have _hK3 := hK3
  have h3' : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
  have h1' : (ω : K) ≠ 1 := fun h => h1 (Units.val_eq_one.1 h)
  have hω : 1 + (ω : K) + (ω : K) ^ 2 = 0 := by
    have h : ((ω : K) - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination h3'
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 h1')
  obtain ⟨A, ε₁, ε₂, d, hε₁, hε₂, hA, hm⟩ := bmN_exists_mono (K := K)
  obtain ⟨N, hN0, hNN, hdet, hAN⟩ := bmN_exists_nilp hε₁ hε₂ hω d
  rw [← hA] at hAN
  obtain ⟨u, hu⟩ := bmN_exists_hom hNN hdet
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Multiplicative K →* adjointGroup Tag.E6 K, ∀ t : K,
      ((ψ (Multiplicative.ofAdd t) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        (((a2Equiv₁ K).symm (u (Multiplicative.ofAdd t)) : subsystemGroup Tag.E6 K support13) :
          ModGL Tag.E6 K) :=
    ⟨(Subgroup.inclusion bmN_subsystemGroup13_le).comp ((a2Equiv₁ K).symm.toMonoidHom.comp u),
      fun _ => rfl⟩
  have hψQ : ∀ t : K, ((ψ (Multiplicative.ofAdd t) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
      subsystemGroup Tag.E6 K support13 := fun t => by
    rw [hψ]
    exact ((a2Equiv₁ K).symm _).2
  have hfix : ∀ {a : Fin Tag.E6.rank → Kˣ}, a 0 = 1 → a 2 = 1 → ∀ t : K,
      rootDiagAutHom .E6 K a (ψ (Multiplicative.ofAdd t)) = ψ (Multiplicative.ofAdd (1 * t)) :=
    fun ha0 ha2 t => by
      rw [one_mul]
      exact bmN_rootDiagAutHom_apply ha0 ha2 _ (hψQ t)
  have hX : ∀ t : K, (MulAut.conj (weylWordElt .E6 K e6BadWord) * rootDiagAutHom .E6 K b)
      (ψ (Multiplicative.ofAdd t)) = ψ (Multiplicative.ofAdd ((ω : K) ^ 2 * t)) := by
    intro t
    obtain ⟨hmem, hmat⟩ := hm _ ((a2Equiv₁ K).symm (u (Multiplicative.ofAdd t))).2
    have hg : a2Mat₁ (((a2Equiv₁ K).symm (u (Multiplicative.ofAdd t)) :
        subsystemGroup Tag.E6 K support13) : ModGL Tag.E6 K) = 1 + t • N := by
      rw [← bmN_coe_a2Equiv₁, MulEquiv.apply_symm_apply, hu]
    rw [hg, bmN_conj_one_add hAN t] at hmat
    have key : a2Equiv₁ K ⟨_, hmem⟩ = u (Multiplicative.ofAdd ((ω : K) ^ 2 * t)) :=
      Subtype.ext (by rw [bmN_coe_a2Equiv₁, hu]; exact hmat)
    refine Subtype.ext ?_
    rw [bmN_X_apply hb0 hb2 _ (hψQ t), hψ, hψ]
    exact (congrArg Subtype.val ((a2Equiv₁ K).symm_apply_eq.2 key.symm)).symm
  refine ⟨ψ.range, bmN_range_ne_bot ψ fun h => hN0 ?_, bmN_isPGroup_range ψ, ?_,
    bmN_map_range_eq ψ _ one_ne_zero (hfix (a := e6D0Char ω) rfl rfl),
    bmN_map_range_eq ψ _ (pow_ne_zero 2 (Units.ne_zero ω)) hX⟩
  · have h1u : u (Multiplicative.ofAdd 1) = 1 := by
      have e : (a2Equiv₁ K).symm (u (Multiplicative.ofAdd 1)) = 1 :=
        Subtype.ext ((hψ 1).symm.trans (congrArg Subtype.val h))
      rwa [MulEquiv.symm_apply_eq, map_one (a2Equiv₁ K)] at e
    have h2 := congrArg (fun B : SL(3, K) => (B : Matrix (Fin 3) (Fin 3) K)) h1u
    simpa [hu] using h2
  · rw [bm_conj_e6LineElt]
    exact bmN_map_range_eq ψ _ one_ne_zero (hfix (a := e6LineChar ω) rfl rfl)

end Chevalley

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
