module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpCent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinearBranches
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (eigenPlus eigenMinus invSMulOp
  similitudeCentralizer exists_bilin_split_equiv eigen_ne_bot isCompl_ker_sub_one_ker_add_one
  invSMulOp_mul_self bilin_eq_zero_swap)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

abbrev linA (A : gsp r K) : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K) :=
  Matrix.GeneralLinearGroup.toLin (A : GL (Fin r ⊕ Fin r) K)

theorem linA_apply (A : gsp r K) (v : Fin r ⊕ Fin r → K) :
    ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) v =
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v :=
  toLin_apply _ v

theorem mem_eigenPlus {A : gsp r K} {l : K} (hl0 : l ≠ 0) {v : Fin r ⊕ Fin r → K} :
    v ∈ eigenPlus l ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) ↔
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = l • v := by
  rw [eigenPlus, LinearMap.mem_ker, LinearMap.sub_apply, invSMulOp, LinearMap.smul_apply,
    linA_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · intro h
    calc ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v =
        l • (l⁻¹ • (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
          v)) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
      _ = l • v := by rw [h]
  · intro h
    rw [h, smul_smul, inv_mul_cancel₀ hl0, one_smul]

theorem mem_eigenMinus {A : gsp r K} {l : K} (hl0 : l ≠ 0) {v : Fin r ⊕ Fin r → K} :
    v ∈ eigenMinus l ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) ↔
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v =
        (-l) • v := by
  rw [eigenMinus, LinearMap.mem_ker, LinearMap.add_apply, invSMulOp, LinearMap.smul_apply,
    linA_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]
  constructor
  · intro h
    calc ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v =
        l • (l⁻¹ • (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
          v)) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
      _ = (-l) • v := by rw [h, smul_neg, neg_smul]
  · intro h
    rw [h, smul_smul, mul_neg, inv_mul_cancel₀ hl0, neg_one_smul]

theorem linA_mul_self {A : gsp r K} {d : K}
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1) :
    ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) *
      ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) = d • 1 := by
  refine LinearMap.ext fun v => ?_
  rw [Module.End.mul_apply, linA_apply, linA_apply, mulVec_mulVec, hAA, LinearMap.smul_apply,
    Module.End.one_apply, smul_mulVec, one_mulVec]

theorem form_mulVec (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (v w : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (M *ᵥ v) (M *ᵥ w) = v ⬝ᵥ ((Mᵀ * formJ r K * M) *ᵥ w) := by
  rw [CatalogueBSymplecticB.pairedSympForm_mulVec_eq_toBilin', Matrix.toBilin'_apply']

theorem form_similitude {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {μ : K}
    (hM : Mᵀ * formJ r K * M = μ • formJ r K) (v w : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (M *ᵥ v) (M *ᵥ w) = μ * pairedSympForm K r v w := by
  rw [form_mulVec, hM, smul_mulVec, dotProduct_smul, smul_eq_mul, pairedSympForm_eq]

theorem transpose_mul_formJ {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {d : K} (hd : d ≠ 0)
    (hJ : Aᵀ * formJ r K * A = d • formJ r K) (hAA : A * A = d • 1) :
    Aᵀ * formJ r K = formJ r K * A := by
  have h := congrArg (· * A) hJ
  simp only [Matrix.mul_assoc, hAA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one] at h
  have := congrArg (d⁻¹ • ·) h
  simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul] using this

theorem map_one_add_smul {ι : Type} [Fintype ι] [DecidableEq ι] (τ : K ≃+* K) (c : K)
    (N : Matrix ι ι K) : (1 + c • N).map τ = 1 + τ c • N.map τ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply]
  split_ifs <;> simp

section Split

variable {A : gsp r K} {l : K}

abbrev VPl (A : gsp r K) (l : K) : Submodule K (Fin r ⊕ Fin r → K) :=
  eigenPlus l ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K))

abbrev VMl (A : gsp r K) (l : K) : Submodule K (Fin r ⊕ Fin r → K) :=
  eigenMinus l ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K))

theorem mulVec_mem_VPl (hl0 : l ≠ 0) {g : StatedSp r K} (hg : g ∈ spCent r K A)
    {v : Fin r ⊕ Fin r → K} (hv : v ∈ VPl A l) :
    ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ VPl A l := by
  rw [mem_eigenPlus hl0] at hv ⊢
  rw [mulVec_mulVec, mem_spCent.1 hg, ← mulVec_mulVec, hv, mulVec_smul]

theorem mulVec_mem_VMl (hl0 : l ≠ 0) {g : StatedSp r K} (hg : g ∈ spCent r K A)
    {v : Fin r ⊕ Fin r → K} (hv : v ∈ VMl A l) :
    ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ VMl A l := by
  rw [mem_eigenMinus hl0] at hv ⊢
  rw [mulVec_mulVec, mem_spCent.1 hg, ← mulVec_mulVec, hv, mulVec_smul]

theorem transvSp_mem_spCent (hJ : ((A : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K =
      formJ r K * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    {v : Fin r ⊕ Fin r → K} {s : K}
    (hv : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = s • v)
    (c : K) : transvSp v c ∈ spCent r K A := by
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have h1 : M * transvN v = s • transvN v := by
    rw [transvN, mul_vecMulVec, hv]
    ext i j
    simp [vecMulVec_apply, mul_assoc]
  have h2 : transvN v * M = s • transvN v := by
    rw [transvN, vecMulVec_mul, vecMul_vecMul, ← hJ, ← vecMul_vecMul, vecMul_transpose, hv]
    ext i j
    simp [vecMulVec_apply, smul_vecMul, mul_left_comm]
  rw [mem_spCent, coe_transvSp, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul, h1, h2]

theorem glW_eq_one_iff {W : Submodule K (Fin r ⊕ Fin r → K)} {u : LinearMap.GeneralLinearGroup K W}
    {x : Module.End K (Fin r ⊕ Fin r → K)}
    (h : W.subtype ∘ₗ (u : Module.End K W) = x ∘ₗ W.subtype) : u = 1 ↔ ∀ v ∈ W, x v = v := by
  constructor
  · rintro rfl v hv
    have := congrArg (fun f : W →ₗ[K] (Fin r ⊕ Fin r → K) => f ⟨v, hv⟩) h
    simpa using this.symm
  · intro hx
    apply Units.ext
    refine LinearMap.ext fun w => Subtype.ext ?_
    have := congrArg (fun f : W →ₗ[K] (Fin r ⊕ Fin r → K) => f w) h
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, hx w w.2]
    rfl

theorem isQuasisimple_fixSub_of_equiv {W : Submodule K (Fin r ⊕ Fin r → K)} {U U' : Type*}
    [Group U] [Group U'] (E : spCent r K A ≃* U × U')
    (hE : ∀ g : spCent r K A, (E g).2 = 1 ↔ ∀ v ∈ W,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v)
    (hU : IsQuasisimple U) : IsQuasisimple (fixSub r K A W) := by
  set φ : fixSub r K A W →* U :=
    (MonoidHom.fst U U').comp (E.toMonoidHom.comp (Subgroup.inclusion (fixSub_le A W)))
    with hφ
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h1 : (E (Subgroup.inclusion (fixSub_le A W) g)).2 = 1 := (hE _).2 g.2.2
    have h2 : E (Subgroup.inclusion (fixSub_le A W) g) = 1 := Prod.ext hg h1
    rw [mem_bot]
    have h3 := E.injective (h2.trans (map_one E).symm)
    exact Subtype.ext (congrArg (fun x : spCent r K A => (x : StatedSp r K)) h3)
  have hsurj : Function.Surjective φ := by
    intro u
    set g := E.symm (u, 1) with hg
    have hfix := (hE g).1 (by rw [hg, MulEquiv.apply_symm_apply])
    refine ⟨⟨g, g.2, hfix⟩, ?_⟩
    change (E (Subgroup.inclusion (fixSub_le A W) ⟨g, g.2, hfix⟩)).1 = u
    have : Subgroup.inclusion (fixSub_le A W) ⟨g, g.2, hfix⟩ = g := rfl
    rw [this, hg, MulEquiv.apply_symm_apply]
  exact LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm hU

theorem vecMul_formJ_ne_zero {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) : v ᵥ* formJ r K ≠ 0 := by
  intro h
  apply hv
  have hJJ : formJ r K * formJ r K = -1 := by
    rw [formJ, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg]
    rw [← fromBlocks_one, fromBlocks_neg, neg_zero]
  have : v ᵥ* formJ r K ᵥ* formJ r K = -v := by
    rw [vecMul_vecMul, hJJ, vecMul_neg, vecMul_one]
  rw [h, zero_vecMul] at this
  exact neg_eq_zero.1 this.symm

theorem eigen_of_transvSp_mem [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    {Q : Subgroup (StatedSp r K)} (hQF : Q ≤ spCent r K A)
    (hQn : ∀ f ∈ spCent r K A, ∀ q ∈ Q, f * q * f⁻¹ ∈ Q) (hQq : IsQuasisimple Q)
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hTQ : ∀ v ∈ W, ∀ c, transvSp v c ∈ Q)
    {D : gsp r K} {τ : K ≃+* K}
    (hy : conjAut r K D * fieldAut r K τ ∈ oddCoreIn B (conjAut r K A)) :
    (W ≠ ⊥ → τ = 1) ∧ ∀ v ∈ W, ∃ μ : K,
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = μ • v := by
  have hqim := isQuasisimple_map_conjProjH hinj hQq
  have hfix : ∀ g ∈ Q, (conjAut r K D * fieldAut r K τ) (proj r K g) = proj r K g :=
    fun g hg => commute_oddCoreIn_of_normal hinj hB (conjSp r K A).toMonoidHom (conjAut_proj A)
      hQF hQn hqim hy hg
  have hperf := commutator_eq_self_of_isQuasisimple hQq
  have key : ∀ v ∈ W, v ≠ 0 → τ = 1 ∧ ∃ μ : K,
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = μ • v := by
    intro v hv hv0
    obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    obtain ⟨b, hb⟩ : ∃ b, (v ᵥ* formJ r K) b ≠ 0 := by
      by_contra h
      push Not at h
      exact vecMul_formJ_ne_zero hv0 (funext h)
    have hab : transvN v a b ≠ 0 := by
      simp only [transvN, vecMulVec_apply]
      exact mul_ne_zero ha hb
    have hfam : ∀ c : K, ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        (1 + τ c • (transvN v).map τ) * (((D : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + c • transvN v := by
      intro c
      have h := semilinear_eq_of_fix hperf hfix (hTQ v hv c)
      rwa [coe_transvSp, map_one_add_smul] at h
    obtain ⟨hτ, hcomm⟩ := fix_unipotent_family_matrix hab hfam
    exact ⟨hτ, exists_eigen_of_commute_vecMulVec' hb hcomm⟩
  refine ⟨fun hW => ?_, fun v hv => ?_⟩
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact (key v hv hv0).1
  · by_cases hv0 : v = 0
    · exact ⟨0, by rw [hv0, mulVec_zero, smul_zero]⟩
    · exact (key v hv hv0).2

theorem multiplier_eq_sq_of_smul {D : gsp r K} [NeZero r] {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : W ≠ ⊥) (hnd : ((pairedSympForm K r).domRestrict₁₂ W W).Nondegenerate) {a : K}
    (ha : ∀ v ∈ W,
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = a • v) :
    (multiplier r K D : K) = a ^ 2 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨y, hy⟩ : ∃ y : W, (pairedSympForm K r).domRestrict₁₂ W W ⟨x, hx⟩ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (congrArg Subtype.val (hnd.1 ⟨x, hx⟩ h))
  rw [LinearMap.domRestrict₁₂_apply] at hy
  have h := form_similitude (multiplier_spec D) x y
  rw [ha x hx, ha y y.2, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    at h
  have : ((multiplier r K D : K) - a ^ 2) * pairedSympForm K r x y = 0 := by
    linear_combination -h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hy)

theorem splitSelf_conclude [Finite K] (hK : ringChar K ≠ 2) (hr : 2 ≤ r)
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    (hl0 : l ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (l ^ 2) • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (l ^ 2) • formJ r K)
    {D : gsp r K} (hoddy : Odd (orderOf (conjAut r K D)))
    (hPe : ∀ v ∈ VPl A l, ∃ μ : K,
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = μ • v)
    (hMe : ∀ v ∈ VMl A l, ∃ μ : K,
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = μ • v) :
    conjAut r K D = 1 := by
  have : NeZero r := ⟨by omega⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hd0 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl0
  have hAA' := linA_mul_self hAA
  have hTB : ∀ v w, pairedSympForm K r (invSMulOp l ((linA A :
      LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (invSMulOp l ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = pairedSympForm K r v w := by
    intro v w
    simp only [invSMulOp, LinearMap.smul_apply, linA_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [form_similitude hJ]
    field_simp
  have hAns' : ∀ c : K, ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) ≠ c • 1 :=
    CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns
  obtain ⟨hPne, hMne⟩ := eigen_ne_bot h2 hl0 hAA' hAns'
  obtain ⟨-, -, -, hndP, hndM, -⟩ :=
    exists_bilin_split_equiv h2 pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      hl0 hAA' hTB
  obtain ⟨a, ha⟩ := exists_smul_of_eigen hPe
  obtain ⟨b, hb⟩ := exists_smul_of_eigen hMe
  have hab : a ^ 2 = b ^ 2 := by
    rw [← multiplier_eq_sq_of_smul hPne hndP ha, ← multiplier_eq_sq_of_smul hMne hndM hb]
  have hc := isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA')
  set Dm := ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hDm
  have hDx : ∀ x : Fin r ⊕ Fin r → K, ∃ x₁ ∈ VPl A l, ∃ x₂ ∈ VMl A l, x = x₁ + x₂ ∧
      Dm *ᵥ x = a • x₁ + b • x₂ ∧ M *ᵥ x = l • x₁ + (-l) • x₂ := by
    intro x
    obtain ⟨x₁, x₂, hx₁, hx₂, hx⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint x
    refine ⟨x₁, hx₁, x₂, hx₂, hx.symm, ?_, ?_⟩
    · rw [← hx, mulVec_add, ha x₁ hx₁, hb x₂ hx₂]
    · rw [← hx, mulVec_add, (mem_eigenPlus hl0).1 hx₁, (mem_eigenMinus hl0).1 hx₂]
  have horder : orderOf (conjAut r K A) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, ← map_mul, conjAut_eq_one_iff (by omega)]
      refine ⟨Units.mk0 (l ^ 2) hd0, Units.ext ?_⟩
      rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
      exact hAA.trans (by rw [Matrix.smul_one_eq_diagonal]; rfl)
    · intro h1
      obtain ⟨c, hc⟩ := (conjAut_eq_one_iff (by omega) A).1 h1
      exact hAns c hc
  have ha0 : a ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPne
    have h1 := ha v hv
    rw [h0, zero_smul] at h1
    apply hv0
    calc v = (((D : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (Dm *ᵥ v) := by
          rw [mulVec_mulVec, hDm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      _ = 0 := by rw [h1, mulVec_zero]
  rcases (show a = b ∨ a = -b by
      have : (a - b) * (a + b) = 0 := by linear_combination hab
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)) with hab' | hab'
  ·
    have hDs : Dm = a • 1 := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun x => ?_
      obtain ⟨x₁, -, x₂, -, rfl, hD, -⟩ := hDx x
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hD, hab', smul_mulVec, one_mulVec, smul_add]
    rw [conjAut_eq_one_iff (by omega)]
    refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar]
    exact hDs.trans (by rw [Matrix.smul_one_eq_diagonal]; rfl)
  ·
    exfalso
    have hDA : Dm = (a / l) • M := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun x => ?_
      obtain ⟨x₁, -, x₂, -, -, hD, hMx'⟩ := hDx x
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hD, smul_mulVec, hMx', smul_add, smul_smul,
        smul_smul, hab']
      congr 2
      · field_simp
      · field_simp
    have hq : conjAut r K (A⁻¹ * D) = 1 := by
      rw [conjAut_eq_one_iff (by omega)]
      refine ⟨Units.mk0 (a / l) (div_ne_zero ha0 hl0), Units.ext ?_⟩
      rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
      change ((A⁻¹ : gsp r K) : GL (Fin r ⊕ Fin r) K).val * Dm = _
      rw [hDA, Matrix.mul_smul, Subgroup.coe_inv, hM, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.smul_one_eq_diagonal]
      rfl
    have hDeq : conjAut r K D = conjAut r K A := by
      have : D = A * (A⁻¹ * D) := by group
      rw [this, map_mul, hq, mul_one]
    rw [hDeq, horder] at hoddy
    exact absurd hoddy (by decide)


theorem splitSelf_oddCoreIn_eq_bot [Finite K] (hK : ringChar K ≠ 2) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    (hl0 : l ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (l ^ 2) • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (l ^ 2) • formJ r K)
    (hPx : Module.finrank K (VPl A l) ≠ 2 ∨ Nat.card K ≠ 3)
    (hMx : Module.finrank K (VMl A l) ≠ 2 ∨ Nat.card K ≠ 3) :
    oddCoreIn B (conjAut r K A) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have : NeZero r := ⟨by omega⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hd0 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl0
  have hJA : Mᵀ * formJ r K = formJ r K * M := transpose_mul_formJ hd0 hJ hAA
  have hAA' := linA_mul_self hAA
  have hTB : ∀ v w, pairedSympForm K r (invSMulOp l ((linA A :
      LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (invSMulOp l ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = pairedSympForm K r v w := by
    intro v w
    simp only [invSMulOp, LinearMap.smul_apply, linA_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [form_similitude hJ]
    field_simp
  have hAns' : ∀ c : K, ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) ≠ c • 1 :=
    CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns
  obtain ⟨hPne, hMne⟩ := eigen_ne_bot h2 hl0 hAA' hAns'
  obtain ⟨horth, haltP, haltM, hndP, hndM, e, he⟩ :=
    exists_bilin_split_equiv h2 pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      hl0 hAA' hTB
  set Ψ := (spCentEquiv A).trans e with hΨ
  have hres : ∀ g : spCent r K A, (Ψ g).2 = 1 ↔ ∀ v ∈ VMl A l,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v := by
    intro g
    change (e (spCentEquiv A g)).2 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv A g)).2]
    simp only [spCentEquiv_apply]
  have hres' : ∀ g : spCent r K A, ((Ψ.trans (MulEquiv.prodComm)) g).2 = 1 ↔ ∀ v ∈ VPl A l,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v := by
    intro g
    change (e (spCentEquiv A g)).1 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv A g)).1]
    simp only [spCentEquiv_apply]
  have hqP : IsQuasisimple (fixSub r K A (VMl A l)) :=
    isQuasisimple_fixSub_of_equiv Ψ hres
      (LocalCores.isQuasisimple_of_mulEquiv (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _).symm
        (CatalogueBAlternatingIsometry.isometry_quasisimple _ haltP hndP
          (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hPne _ haltP hndP) hodd hPx))
  have hqM : IsQuasisimple (fixSub r K A (VPl A l)) :=
    isQuasisimple_fixSub_of_equiv (Ψ.trans (MulEquiv.prodComm)) hres'
      (LocalCores.isQuasisimple_of_mulEquiv (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _).symm
        (CatalogueBAlternatingIsometry.isometry_quasisimple _ haltM hndM
          (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hMne _ haltM hndM) hodd hMx))
  have hTP : ∀ v ∈ VPl A l, ∀ c, transvSp v c ∈ fixSub r K A (VMl A l) := by
    intro v hv c
    refine ⟨transvSp_mem_spCent hJA ((mem_eigenPlus hl0).1 hv) c, fun w hw => ?_⟩
    rw [coe_transvSp, add_mulVec, one_mulVec, smul_mulVec, transvN_mulVec, horth v hv w hw,
      zero_smul, smul_zero, add_zero]
  have hTM : ∀ v ∈ VMl A l, ∀ c, transvSp v c ∈ fixSub r K A (VPl A l) := by
    intro v hv c
    refine ⟨transvSp_mem_spCent hJA ((mem_eigenMinus hl0).1 hv) c, fun w hw => ?_⟩
    rw [coe_transvSp, add_mulVec, one_mulVec, smul_mulVec, transvN_mulVec,
      bilin_eq_zero_swap (B := pairedSympForm K r) pairedSympForm_isAlt (horth w hw v hv),
      zero_smul, smul_zero, add_zero]
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hoddy := odd_orderOf_of_mem_oddCoreIn hy
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr y
  obtain ⟨hτ, hPe⟩ := eigen_of_transvSp_mem hinj hB (fixSub_le A _)
    (fun f hf q hq => conj_mem_fixSub (fun g hg v hv => mulVec_mem_VMl hl0 hg hv) hf hq) hqP hTP
    hy
  obtain ⟨-, hMe⟩ := eigen_of_transvSp_mem hinj hB (fixSub_le A _)
    (fun f hf q hq => conj_mem_fixSub (fun g hg v hv => mulVec_mem_VPl hl0 hg hv) hf hq) hqM hTM
    hy
  rw [hτ hPne, map_one, mul_one] at hoddy ⊢
  exact splitSelf_conclude hK hr hAns hl0 hAA hJ hoddy hPe hMe

end Split

end CFSG.ComponentClassification.Burgoyne.Sp
