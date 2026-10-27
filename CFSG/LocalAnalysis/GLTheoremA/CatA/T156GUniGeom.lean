module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniSub
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearDescent
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearGeom
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156.Uni

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.StandardType
open scoped commutatorElement

variable {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {j : ℕ}

local notation "SUq" => LargeEvenSUGroup (Fin d) K (2 ^ j)

theorem dq_ne_of_sub {r : ℕ} (hj : 1 ≤ j) (hr : j = j / r * r) (hdq : (d, 2 ^ (j / r)) ≠ (3, 2)) :
    (d, 2 ^ j) ≠ (3, 2) := by
  intro h
  apply hdq
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  have hj1 : j = 1 := by
    have : 2 ^ j = 2 ^ 1 := by rw [h2]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  have hr1 : j / r = 1 := by
    rcases Nat.eq_zero_or_pos (j / r) with h0 | h0
    · rw [h0, zero_mul] at hr
      omega
    · have : j / r ≤ j := Nat.div_le_self j r
      omega
  rw [h1, hr1]
  norm_num

theorem pow_pow_eq_self (hK : Nat.card K = (2 ^ j) ^ 2) (c : K) : (c ^ 2 ^ j) ^ 2 ^ j = c := by
  haveI := Fintype.ofFinite K
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hK] at h
  rw [← pow_mul, ← sq]
  exact h

theorem exists_conj_of_commute (hd : 3 ≤ d) (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2)
    {σ : K ≃+* K} (hσ : Odd (orderOf σ)) (hdq : (d, 2 ^ (j / orderOf σ)) ≠ (3, 2))
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j)))} (hf : Induced (2 ^ j) σ f)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j)))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ j)))
      (LargeEvenGUSet (Fin d) K (2 ^ j)))
    (hc : φ * f = f * φ) :
    ∃ B ∈ LargeEvenGUSet (Fin d) (fixF σ) (2 ^ (j / orderOf σ)),
      ∀ g g' : LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ)),
        (g' : GL (Fin d) (fixF σ)) = B * g * B⁻¹ →
          φ (subfieldHom hj hK σ hσ g) = subfieldHom hj hK σ hσ g' := by
  obtain ⟨hjr, -, -⟩ := fixF_data hj hK σ hσ
  have hdK : (d, 2 ^ j) ≠ (3, 2) := dq_ne_of_sub hj hjr hdq
  obtain ⟨A, hAGU, hA⟩ := hφ
  have hmem : ∀ x : SUq, A * (x : GL (Fin d) K) * A⁻¹ ∈ SUq := fun x => conj_mem_su hAGU x.2
  let conjA : SUq → SUq := fun x => ⟨A * (x : GL (Fin d) K) * A⁻¹, hmem x⟩
  have conjA_val : ∀ x : SUq, ((conjA x : SUq) : GL (Fin d) K) = A * (x : GL (Fin d) K) * A⁻¹ :=
    fun _ => rfl
  let ρ : MulAut SUq := matAct SUq (suMapStable d K (2 ^ j)) σ
  have hc_apply : ∀ x : SUq, φ (f ((LargeEvenProjMk SUq) x)) = f (φ ((LargeEvenProjMk SUq) x)) := by
    intro x
    have h := congrArg (fun ψ : MulAut (LargeEvenProj SUq) => ψ ((LargeEvenProjMk SUq) x)) hc
    simpa only [MulAut.mul_apply] using h
  set S : GL (Fin d) K := Matrix.GeneralLinearGroup.map σ.toRingHom A with hSdef
  set T : GL (Fin d) K := A⁻¹ * S with hTdef
  have hcenter_x : ∀ x : SUq,
      ⁅((ρ x : SUq) : GL (Fin d) K)⁻¹, T⁆ ∈ Subgroup.center (GL (Fin d) K) := by
    intro x
    have hstep : (LargeEvenProjMk SUq) (conjA (ρ x)) = (LargeEvenProjMk SUq) (ρ (conjA x)) := by
      calc (LargeEvenProjMk SUq) (conjA (ρ x))
          = φ ((LargeEvenProjMk SUq) (ρ x)) := (hA (ρ x) (conjA (ρ x)) rfl).symm
        _ = φ (f ((LargeEvenProjMk SUq) x)) := congrArg φ (hf x).symm
        _ = f (φ ((LargeEvenProjMk SUq) x)) := hc_apply x
        _ = f ((LargeEvenProjMk SUq) (conjA x)) := by rw [hA x (conjA x) rfl]
        _ = (LargeEvenProjMk SUq) (ρ (conjA x)) := hf (conjA x)
    have hZ := QuotientGroup.eq.mp hstep
    have hZgl : ((conjA (ρ x) : SUq) : GL (Fin d) K)⁻¹ * ((ρ (conjA x) : SUq) : GL (Fin d) K) ∈
        LargeEvenScalars (Fin d) K := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using (Subgroup.mem_subgroupOf.mp hZ)
    have h2 : ((ρ (conjA x) : SUq) : GL (Fin d) K) =
        S * ((ρ x : SUq) : GL (Fin d) K) * S⁻¹ := by
      rw [matAct_coe SUq (suMapStable d K (2 ^ j)) σ (conjA x), conjA_val x,
        Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
        Matrix.GeneralLinearGroup.map_inv, matAct_coe SUq (suMapStable d K (2 ^ j)) σ x, hSdef]
    rw [conjA_val, h2] at hZgl
    have hEk : A * ⁅((ρ x : SUq) : GL (Fin d) K)⁻¹, T⁆ * A⁻¹ ∈ LargeEvenScalars (Fin d) K := by
      convert hZgl using 1
      rw [hTdef, commutatorElement_def]
      group
    have hcenter : A * ⁅((ρ x : SUq) : GL (Fin d) K)⁻¹, T⁆ * A⁻¹ ∈
        Subgroup.center (GL (Fin d) K) := by
      simpa only [largeEvenScalars_def, Matrix.GeneralLinearGroup.center_eq_range_scalar]
        using hEk
    have hconj := Subgroup.Normal.conj_mem'
      (inferInstance : (Subgroup.center (GL (Fin d) K)).Normal)
      (A * ⁅((ρ x : SUq) : GL (Fin d) K)⁻¹, T⁆ * A⁻¹) hcenter A
    convert hconj using 1
    group
  have hcomm : ∀ g ∈ SUq, ⁅T, g⁆ ∈ Subgroup.center (GL (Fin d) K) := by
    intro g hg
    have h1 : ⁅g, T⁆ ∈ Subgroup.center (GL (Fin d) K) := by
      let y : SUq := ⟨g⁻¹, Subgroup.inv_mem _ hg⟩
      have h := hcenter_x (ρ.symm y)
      rw [ρ.apply_symm_apply] at h
      dsimp only [y] at h
      simpa using h
    rw [← commutatorElement_inv g T]
    exact (Subgroup.center (GL (Fin d) K)).inv_mem h1
  have hT : T ∈ LargeEvenScalars (Fin d) K := by
    refine mem_scalars_of_commute_su (k := K) (g := j) hj hK hd (RingHom.id K) fun x hx => ?_
    have hid : Matrix.GeneralLinearGroup.map (RingHom.id K) x = x := by
      apply Units.ext
      ext a b
      rfl
    rw [hid]
    exact LinearFieldFix.commute_of_commutator_mem_center (commutator_su hK hd hdK) hcomm hx
  rw [largeEvenScalars_def] at hT
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hT
  have hS : Matrix.GeneralLinearGroup.map σ.toRingHom A =
      A * Matrix.GeneralLinearGroup.scalar (Fin d) c := by
    rw [hc, hTdef, hSdef]
    group
  have hmat : ((Matrix.GeneralLinearGroup.map σ.toRingHom A : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = (c : K) • (A : Matrix (Fin d) (Fin d) K) := by
    rw [hS, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨μ, B, hdesc⟩ := LinearFieldFix.exists_descend_of_map_eq_smul σ A c hmat
  have hBGU : B ∈ LargeEvenGUSet (Fin d) (fixF σ) (2 ^ (j / orderOf σ)) := by
    refine mem_guSet_of_map (fixF σ).subtype (q := 2 ^ j) (fun b => ?_) (pow_pow_eq_self hK)
      (by omega) hAGU μ.ne_zero hdesc
    rw [map_pow]
    exact (fixF_pow hj hK σ hσ b).symm
  refine ⟨B, hBGU, fun g g' hgg' => ?_⟩
  have hBmap : Matrix.GeneralLinearGroup.map (fixF σ).subtype B =
      Matrix.GeneralLinearGroup.scalar (Fin d) μ * A := by
    apply Units.ext
    rw [hdesc, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  have hmap : Matrix.GeneralLinearGroup.map (fixF σ).subtype g' =
      A * Matrix.GeneralLinearGroup.map (fixF σ).subtype g * A⁻¹ := by
    have h1 : Matrix.GeneralLinearGroup.map (fixF σ).subtype g' =
        Matrix.GeneralLinearGroup.map (fixF σ).subtype B *
          Matrix.GeneralLinearGroup.map (fixF σ).subtype g *
          (Matrix.GeneralLinearGroup.map (fixF σ).subtype B)⁻¹ := by
      conv_lhs => rw [hgg']
      rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
        Matrix.GeneralLinearGroup.map_inv]
    rw [h1, hBmap]
    calc (Matrix.GeneralLinearGroup.scalar (Fin d) μ * A) *
            Matrix.GeneralLinearGroup.map (fixF σ).subtype g *
            (Matrix.GeneralLinearGroup.scalar (Fin d) μ * A)⁻¹
        = Matrix.GeneralLinearGroup.scalar (Fin d) μ *
            (A * Matrix.GeneralLinearGroup.map (fixF σ).subtype g * A⁻¹) *
            (Matrix.GeneralLinearGroup.scalar (Fin d) μ)⁻¹ := by
          rw [mul_inv_rev]
          group
      _ = (A * Matrix.GeneralLinearGroup.map (fixF σ).subtype g * A⁻¹) *
            Matrix.GeneralLinearGroup.scalar (Fin d) μ *
            (Matrix.GeneralLinearGroup.scalar (Fin d) μ)⁻¹ := by
          rw [Matrix.GeneralLinearGroup.scalar_commute]
      _ = A * Matrix.GeneralLinearGroup.map (fixF σ).subtype g * A⁻¹ := by group
  have hx' : (subfieldInclusion hj hK σ hσ g' : SUq) = conjA (subfieldInclusion hj hK σ hσ g) := by
    apply Subtype.ext
    rw [coe_subfieldInclusion, conjA_val, coe_subfieldInclusion]
    exact hmap
  have hφx : φ ((LargeEvenProjMk SUq) (subfieldInclusion hj hK σ hσ g)) =
      (LargeEvenProjMk SUq) (subfieldInclusion hj hK σ hσ g') :=
    hA (subfieldInclusion hj hK σ hσ g) (subfieldInclusion hj hK σ hσ g') (by
      change ((subfieldInclusion hj hK σ hσ g' : SUq) : GL (Fin d) K) =
        A * ((subfieldInclusion hj hK σ hσ g : SUq) : GL (Fin d) K) * A⁻¹
      rw [hx', conjA_val])
  simpa only [subfieldHom, MonoidHom.comp_apply] using hφx

theorem eq_one_of_fixes_subfield (hd : 3 ≤ d) (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2)
    (σ : K ≃+* K) (hσ : Odd (orderOf σ)) (hdq : (d, 2 ^ (j / orderOf σ)) ≠ (3, 2))
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j)))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ j)))
      (LargeEvenGUSet (Fin d) K (2 ^ j)))
    (h : ∀ g : LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ)),
      φ (subfieldHom hj hK σ hσ g) = subfieldHom hj hK σ hσ g) :
    φ = 1 := by
  classical
  obtain ⟨-, hj', hk⟩ := fixF_data hj hK σ hσ
  haveI : CharP (fixF σ) 2 := charP_fixF hj hK σ hσ
  obtain ⟨A, hAGU, hA⟩ := hφ
  have hscalarCenter : LargeEvenScalars (Fin d) K = Subgroup.center (GL (Fin d) K) :=
    largeEvenScalars_def.trans Matrix.GeneralLinearGroup.center_eq_range_scalar.symm
  have hconj_mem : ∀ x : SUq, A * (x : GL (Fin d) K) * A⁻¹ ∈ SUq := fun x => conj_mem_su hAGU x.2
  let F₁ : GL (Fin d) (fixF σ) →* GL (Fin d) K := Matrix.GeneralLinearGroup.map (fixF σ).subtype
  let H1 : Subgroup (GL (Fin d) K) :=
    (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ))).map F₁
  have hH1 : ⁅H1, H1⁆ = H1 := by
    dsimp only [H1, F₁]
    rw [← Subgroup.map_commutator, commutator_su hk hd hdq]
  have hcent : ∀ g ∈ H1, ⁅A, g⁆ ∈ Subgroup.center (GL (Fin d) K) := by
    intro g hg
    dsimp only [H1, F₁] at hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    let xH : SUq := subfieldInclusion hj hK σ hσ ⟨x, hx⟩
    have hxH_eq : (xH : GL (Fin d) K) = F₁ x := by
      simp only [xH, F₁, coe_subfieldInclusion]
    let xA : SUq := ⟨A * (xH : GL (Fin d) K) * A⁻¹, hconj_mem xH⟩
    have hfix : φ (LargeEvenProjMk SUq xH) = LargeEvenProjMk SUq xH := by
      simpa only [subfieldHom, MonoidHom.comp_apply, xH] using h ⟨x, hx⟩
    have hquot : LargeEvenProjMk SUq xA = LargeEvenProjMk SUq xH := (hA xH xA rfl).symm.trans hfix
    have hmemZ : xH⁻¹ * xA ∈ (LargeEvenScalars (Fin d) K).subgroupOf SUq :=
      QuotientGroup.eq.mp hquot.symm
    let z : GL (Fin d) K := ((xH⁻¹ * xA : SUq) : GL (Fin d) K)
    have hzmem : z ∈ Subgroup.center (GL (Fin d) K) := by
      rw [← hscalarCenter]
      exact Subgroup.mem_subgroupOf.mp hmemZ
    have hz_eq : z = (xH : GL (Fin d) K)⁻¹ * (A * (xH : GL (Fin d) K) * A⁻¹) := rfl
    have hconj1 : (xH : GL (Fin d) K) * z * (xH : GL (Fin d) K)⁻¹ = ⁅A, (xH : GL (Fin d) K)⁆ := by
      rw [commutatorElement_def, hz_eq]
      group
    have hconj2 : (xH : GL (Fin d) K) * z * (xH : GL (Fin d) K)⁻¹ = z := by
      rw [Subgroup.mem_center_iff.mp hzmem (xH : GL (Fin d) K)]
      group
    have hfinal : ⁅A, F₁ x⁆ = z := by
      rw [← hxH_eq]
      exact hconj1.symm.trans hconj2
    rw [hfinal]
    exact hzmem
  have hH1comm : ∀ g ∈ H1, Commute A g :=
    fun g hg => LinearFieldFix.commute_of_commutator_mem_center hH1 hcent hg
  have hAscalar : A ∈ LargeEvenScalars (Fin d) K :=
    mem_scalars_of_commute_su (k := fixF σ) (g := j / orderOf σ) hj' hk hd (fixF σ).subtype
      fun x hx => hH1comm _ ⟨x, hx, rfl⟩
  have hAcenter : A ∈ Subgroup.center (GL (Fin d) K) := by
    rw [← hscalarCenter]
    exact hAscalar
  refine MulEquiv.ext fun y => ?_
  change φ y = y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  change φ (LargeEvenProjMk SUq y) = LargeEvenProjMk SUq y
  let yA : SUq := ⟨A * (y : GL (Fin d) K) * A⁻¹, hconj_mem y⟩
  have h1 : φ (LargeEvenProjMk SUq y) = LargeEvenProjMk SUq yA := hA y yA rfl
  have hyA : yA = y := by
    apply Subtype.ext
    show A * (y : GL (Fin d) K) * A⁻¹ = (y : GL (Fin d) K)
    rw [← Subgroup.mem_center_iff.mp hAcenter (y : GL (Fin d) K)]
    group
  rw [h1, hyA]

theorem ggFixGeom_unitary (hd : 3 ≤ d) (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2)
    {σ : K ≃+* K} (hσ : Odd (orderOf σ)) (hdq : (d, 2 ^ (j / orderOf σ)) ≠ (3, 2))
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j)))} (hf : Induced (2 ^ j) σ f) :
    GGFixGeom (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ j)))
        (LargeEvenGUSet (Fin d) K (2 ^ j))) f
      (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ))))
        (LargeEvenGUSet (Fin d) (fixF σ) (2 ^ (j / orderOf σ))))
      (subfieldEquiv hd hj hK hσ hdq hf).symm := by
  set e := subfieldEquiv hd hj hK hσ hdq hf with he
  refine ⟨fun φ hφ hc => ?_, fun φ hφ _ htriv => ?_⟩
  · obtain ⟨B, hB, hBc⟩ := exists_conj_of_commute hd hj hK hσ hdq hf hφ hc
    refine ⟨(e.trans (LinearFieldFix.ggFixDerRestrict hc)).trans e.symm, ⟨B, hB, ?_⟩, ?_⟩
    · intro g g' hg
      change ((e.trans (LinearFieldFix.ggFixDerRestrict hc)).trans e.symm) (QuotientGroup.mk g) =
        QuotientGroup.mk g'
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
      exact Subtype.ext (hBc g g' hg)
    · intro g hg
      simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
  · refine eq_one_of_fixes_subfield hd hj hK σ hσ hdq hφ fun g => htriv _ ?_
    rw [← range_subfieldHom hd hj hK hσ hdq hf]
    exact ⟨g, rfl⟩

theorem simple_noncomm_proj {k : Type} [Field k] [Finite k] {g : ℕ} (hk : Nat.card k = (2 ^ g) ^ 2)
    (hd : 3 ≤ d) (hdq : (d, 2 ^ g) ≠ (3, 2)) :
    IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin d) k (2 ^ g))) ∧
      ∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin d) k (2 ^ g)), a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin d) k (2 ^ g))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU k 2 g hk d hd hdq
  refine ⟨hS, ?_⟩
  haveI hP : Group.IsPerfect ↥(LargeEvenSUGroup (Fin d) k (2 ^ g)) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := g) hk hd hdq
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin d) k (2 ^ g))) :=
    Group.IsPerfect.ofSurjective (f := LargeEvenProjMk (LargeEvenSUGroup (Fin d) k (2 ^ g)))
      (QuotientGroup.mk'_surjective _)
  haveI : Nontrivial (LargeEvenProj (LargeEvenSUGroup (Fin d) k (2 ^ g))) := hS.toNontrivial
  by_contra h
  push Not at h
  haveI : IsMulCommutative (LargeEvenProj (LargeEvenSUGroup (Fin d) k (2 ^ g))) :=
    IsMulCommutative.of_comm h
  exact Group.IsPerfect.not_isMulCommutative (LargeEvenProj (LargeEvenSUGroup (Fin d) k (2 ^ g)))
    inferInstance

theorem exists_raw_unitary (hd : 3 ≤ d) (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdq : (d, 2 ^ (j / p)) ≠ (3, 2))
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ j))))
    (hord : orderOf f = p) :
    LargeEvenRecipeUnitary d (2 ^ (j / p)) fun R₀ _ I₀ _ => IsSimpleGroup R₀ ∧
      (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer f ≃* R₀,
        GGFixGeom (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ j)))
          (LargeEvenGUSet (Fin d) K (2 ^ j))) f I₀ θ₀ := by
  obtain ⟨σ, hσf⟩ := exists_induced hf
  have hσord : orderOf σ = p := (orderOf_eq_of_induced hd hj hK hσf).trans hord
  have hσ : Odd (orderOf σ) := by
    rw [hσord]
    exact hp.odd_of_ne_two hp2
  have hdq' : (d, 2 ^ (j / orderOf σ)) ≠ (3, 2) := by rw [hσord]; exact hdq
  obtain ⟨-, -, hk⟩ := fixF_data hj hK σ hσ
  rw [hσord] at hk
  have hS := simple_noncomm_proj hk hd hdq
  refine ⟨fixF σ, inferInstance, inferInstance, hk, ?_⟩
  have e1 : j / orderOf σ = j / p := by rw [hσord]
  have key : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ)))) ∧
      (∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ))),
        a * b ≠ b * a) ∧
      ∃ θ₀ : ggFixDer f ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ))),
        GGFixGeom (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ j)))
          (LargeEvenGUSet (Fin d) K (2 ^ j))) f
          (LargeEvenMatConjImage
            (LargeEvenProjMk (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ))))
            (LargeEvenGUSet (Fin d) (fixF σ) (2 ^ (j / orderOf σ)))) θ₀ := by
    rw [e1]
    refine ⟨hS.1, hS.2, ?_⟩
    rw [← e1]
    exact ⟨(subfieldEquiv hd hj hK hσ hdq' hσf).symm, ggFixGeom_unitary hd hj hK hσ hdq' hσf⟩
  rw [e1] at key
  exact key

end CFSG.LocalAnalysis.GLTheoremA.T156.Uni

end
