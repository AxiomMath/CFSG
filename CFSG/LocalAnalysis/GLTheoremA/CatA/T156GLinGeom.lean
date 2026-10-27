module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GLinSub
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearDescent
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearGeom
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearFaithful

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156.Lin

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG.StandardType CFSG.StandardType.LinearFieldFix
open scoped commutatorElement

variable {d : ℕ} {K : Type} [Field K] [Finite K]

local notation "SLK" => LargeEvenSLGroup (Fin d) K

theorem exists_descend_of_commute' (hd : 2 ≤ d) (hKok : SLOK d K) {σ : K ≃+* K}
    {f : MulAut (LargeEvenProj SLK)} (hf : Induced σ f) {φ : MulAut (LargeEvenProj SLK)}
    {A : GL (Fin d) K}
    (hA : LargeEvenGraphAut (LargeEvenProjMk SLK)
      (fun h h' => (h' : GL (Fin d) K) = A * h * A⁻¹) φ)
    (hc : φ * f = f * φ) :
    ∃ (μ : Kˣ) (B : GL (Fin d) (fixF σ)),
      ((Matrix.GeneralLinearGroup.map (fixF σ).subtype B : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = (μ : K) • (A : Matrix (Fin d) (Fin d) K) := by
  have hmem : ∀ x : SLK, A * (x : GL (Fin d) K) * A⁻¹ ∈ SLK := by
    intro x
    rw [TypeA.mem_largeEvenSLGroup_iff]
    have hx : Matrix.GeneralLinearGroup.det (x : GL (Fin d) K) = 1 := by
      apply Units.ext
      rw [Units.val_one]
      exact TypeA.mem_largeEvenSLGroup_iff.mp x.2
    have hdet : Matrix.GeneralLinearGroup.det (A * (x : GL (Fin d) K) * A⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hx]
      group
    change ((Matrix.GeneralLinearGroup.det (A * (x : GL (Fin d) K) * A⁻¹) : Kˣ) : K) = 1
    rw [hdet]
    exact Units.val_one
  let conjA : SLK → SLK := fun x => ⟨A * (x : GL (Fin d) K) * A⁻¹, hmem x⟩
  have conjA_val : ∀ x : SLK, ((conjA x : SLK) : GL (Fin d) K) = A * (x : GL (Fin d) K) * A⁻¹ :=
    fun _ => rfl
  let ρ : MulAut SLK := matAct SLK (slMapStable d K) σ
  have hc_apply : ∀ x : SLK, φ (f ((LargeEvenProjMk SLK) x)) = f (φ ((LargeEvenProjMk SLK) x)) := by
    intro x
    have h := congrArg (fun ψ : MulAut (LargeEvenProj SLK) => ψ ((LargeEvenProjMk SLK) x)) hc
    simpa only [MulAut.mul_apply] using h
  set S : GL (Fin d) K := Matrix.GeneralLinearGroup.map σ.toRingHom A with hSdef
  set T : GL (Fin d) K := A⁻¹ * S with hTdef
  have hcenter_x : ∀ x : SLK,
      ⁅((ρ x : SLK) : GL (Fin d) K)⁻¹, T⁆ ∈ Subgroup.center (GL (Fin d) K) := by
    intro x
    have hstep : (LargeEvenProjMk SLK) (conjA (ρ x)) = (LargeEvenProjMk SLK) (ρ (conjA x)) := by
      calc (LargeEvenProjMk SLK) (conjA (ρ x))
          = φ ((LargeEvenProjMk SLK) (ρ x)) := (hA (ρ x) (conjA (ρ x)) rfl).symm
        _ = φ (f ((LargeEvenProjMk SLK) x)) := congrArg φ (hf x).symm
        _ = f (φ ((LargeEvenProjMk SLK) x)) := hc_apply x
        _ = f ((LargeEvenProjMk SLK) (conjA x)) := by rw [hA x (conjA x) rfl]
        _ = (LargeEvenProjMk SLK) (ρ (conjA x)) := hf (conjA x)
    have hZ := QuotientGroup.eq.mp hstep
    have hZgl : ((conjA (ρ x) : SLK) : GL (Fin d) K)⁻¹ * ((ρ (conjA x) : SLK) : GL (Fin d) K) ∈
        LargeEvenScalars (Fin d) K := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using (Subgroup.mem_subgroupOf.mp hZ)
    have h2 : ((ρ (conjA x) : SLK) : GL (Fin d) K) =
        S * ((ρ x : SLK) : GL (Fin d) K) * S⁻¹ := by
      rw [matAct_coe SLK (slMapStable d K) σ (conjA x), conjA_val x,
        Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
        Matrix.GeneralLinearGroup.map_inv, matAct_coe SLK (slMapStable d K) σ x, hSdef]
    rw [conjA_val, h2] at hZgl
    have hEk : A * ⁅((ρ x : SLK) : GL (Fin d) K)⁻¹, T⁆ * A⁻¹ ∈ LargeEvenScalars (Fin d) K := by
      convert hZgl using 1
      rw [hTdef, commutatorElement_def]
      group
    have hcenter : A * ⁅((ρ x : SLK) : GL (Fin d) K)⁻¹, T⁆ * A⁻¹ ∈
        Subgroup.center (GL (Fin d) K) := by
      simpa only [largeEvenScalars_def, Matrix.GeneralLinearGroup.center_eq_range_scalar]
        using hEk
    have hconj := Subgroup.Normal.conj_mem'
      (inferInstance : (Subgroup.center (GL (Fin d) K)).Normal)
      (A * ⁅((ρ x : SLK) : GL (Fin d) K)⁻¹, T⁆ * A⁻¹) hcenter A
    convert hconj using 1
    group
  have hcomm : ∀ g ∈ SLK, ⁅T, g⁆ ∈ Subgroup.center (GL (Fin d) K) := by
    intro g hg
    have h1 : ⁅g, T⁆ ∈ Subgroup.center (GL (Fin d) K) := by
      let y : SLK := ⟨g⁻¹, Subgroup.inv_mem _ hg⟩
      have h := hcenter_x (ρ.symm y)
      rw [ρ.apply_symm_apply] at h
      dsimp only [y] at h
      simpa using h
    rw [← commutatorElement_inv g T]
    exact (Subgroup.center (GL (Fin d) K)).inv_mem h1
  have hT : T ∈ LargeEvenScalars (Fin d) K :=
    mem_scalars_of_commute_elemSL T (fun i j hij =>
      commute_of_commutator_mem_center (commutator_slGroup' hd hKok) hcomm (elemSL K hij).2)
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
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  exact exists_descend_of_map_eq_smul σ A c hmat

theorem exists_conj_of_commute' (hd : 2 ≤ d) (hKok : SLOK d K) {σ : K ≃+* K}
    {f : MulAut (LargeEvenProj SLK)} (hf : Induced σ f) {φ : MulAut (LargeEvenProj SLK)}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk SLK) Set.univ) (hc : φ * f = f * φ) :
    ∃ B : GL (Fin d) (fixF σ), ∀ g g' : LargeEvenSLGroup (Fin d) (fixF σ),
      (g' : GL (Fin d) (fixF σ)) = B * g * B⁻¹ → φ (subfieldHom σ g) = subfieldHom σ g' := by
  obtain ⟨A, -, hA⟩ := hφ
  obtain ⟨μ, B, hdesc⟩ := exists_descend_of_commute' hd hKok hf hA hc
  have hmem : ∀ x : SLK, A * (x : GL (Fin d) K) * A⁻¹ ∈ SLK := by
    intro x
    rw [TypeA.mem_largeEvenSLGroup_iff]
    have hx : Matrix.GeneralLinearGroup.det (x : GL (Fin d) K) = 1 := by
      apply Units.ext
      rw [Units.val_one]
      exact TypeA.mem_largeEvenSLGroup_iff.mp x.2
    have hdet : Matrix.GeneralLinearGroup.det (A * (x : GL (Fin d) K) * A⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hx]
      group
    change ((Matrix.GeneralLinearGroup.det (A * (x : GL (Fin d) K) * A⁻¹) : Kˣ) : K) = 1
    rw [hdet]
    exact Units.val_one
  let conjA : SLK → SLK := fun x => ⟨A * (x : GL (Fin d) K) * A⁻¹, hmem x⟩
  have conjA_val : ∀ x : SLK, ((conjA x : SLK) : GL (Fin d) K) = A * (x : GL (Fin d) K) * A⁻¹ :=
    fun _ => rfl
  refine ⟨B, fun g g' hgg' => ?_⟩
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
  have hx' : (subfieldInclusion σ g' : SLK) = conjA (subfieldInclusion σ g) := by
    apply Subtype.ext
    rw [coe_subfieldInclusion, conjA_val, coe_subfieldInclusion]
    exact hmap
  have hφx : φ ((LargeEvenProjMk SLK) (subfieldInclusion σ g)) =
      (LargeEvenProjMk SLK) (subfieldInclusion σ g') :=
    hA (subfieldInclusion σ g) (subfieldInclusion σ g') (by
      change ((subfieldInclusion σ g' : SLK) : GL (Fin d) K) =
        A * ((subfieldInclusion σ g : SLK) : GL (Fin d) K) * A⁻¹
      rw [hx', conjA_val])
  simpa only [subfieldHom, MonoidHom.comp_apply] using hφx

theorem eq_one_of_fixes_subfield' (hd : 2 ≤ d) (σ : K ≃+* K) (hk : SLOK d (fixF σ))
    {φ : MulAut (LargeEvenProj SLK)}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk SLK) Set.univ)
    (h : ∀ g : LargeEvenSLGroup (Fin d) (fixF σ), φ (subfieldHom σ g) = subfieldHom σ g) :
    φ = 1 := by
  classical
  obtain ⟨A, -, hA⟩ := hφ
  have hscalarCenter : LargeEvenScalars (Fin d) K = Subgroup.center (GL (Fin d) K) :=
    largeEvenScalars_def.trans Matrix.GeneralLinearGroup.center_eq_range_scalar.symm
  have hconj_mem : ∀ x : SLK, A * (x : GL (Fin d) K) * A⁻¹ ∈ SLK := by
    intro x
    have hxdet : Matrix.GeneralLinearGroup.det (x : GL (Fin d) K) = 1 := by
      rw [← Units.val_eq_one, Matrix.GeneralLinearGroup.val_det_apply]
      exact TypeA.mem_largeEvenSLGroup_iff.mp x.2
    have hAdet : Matrix.GeneralLinearGroup.det (A * (x : GL (Fin d) K) * A⁻¹) = 1 := by
      rw [map_mul, map_mul, hxdet]
      simp
    refine TypeA.mem_largeEvenSLGroup_iff.mpr ?_
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hAdet, Units.val_one]
  let F₁ : GL (Fin d) (fixF σ) →* GL (Fin d) K := Matrix.GeneralLinearGroup.map (fixF σ).subtype
  let H1 : Subgroup (GL (Fin d) K) := (LargeEvenSLGroup (Fin d) (fixF σ)).map F₁
  have hH1 : ⁅H1, H1⁆ = H1 := by
    dsimp only [H1, F₁]
    rw [← Subgroup.map_commutator, commutator_slGroup' (F := fixF σ) hd hk]
  have hcent : ∀ g ∈ H1, ⁅A, g⁆ ∈ Subgroup.center (GL (Fin d) K) := by
    intro g hg
    dsimp only [H1, F₁] at hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    let xH : SLK := subfieldInclusion σ ⟨x, hx⟩
    have hxH_eq : (xH : GL (Fin d) K) = F₁ x := by
      simp only [xH, F₁, coe_subfieldInclusion]
    let xA : SLK := ⟨A * (xH : GL (Fin d) K) * A⁻¹, hconj_mem xH⟩
    have hfix : φ (LargeEvenProjMk SLK xH) = LargeEvenProjMk SLK xH := by
      simpa only [subfieldHom, MonoidHom.comp_apply, xH] using h ⟨x, hx⟩
    have hquot : LargeEvenProjMk SLK xA = LargeEvenProjMk SLK xH := (hA xH xA rfl).symm.trans hfix
    have hmemZ : xH⁻¹ * xA ∈ (LargeEvenScalars (Fin d) K).subgroupOf SLK :=
      QuotientGroup.eq.mp hquot.symm
    let z : GL (Fin d) K := ((xH⁻¹ * xA : SLK) : GL (Fin d) K)
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
    fun g hg => commute_of_commutator_mem_center hH1 hcent hg
  have helem_mem : ∀ (i j : Fin d) (hij : i ≠ j),
      ((elemSL K hij : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) ∈ H1 := by
    intro i j hij
    dsimp only [H1, F₁]
    rw [Subgroup.mem_map]
    exact ⟨((elemSL (fixF σ) hij : LargeEvenSLGroup (Fin d) (fixF σ)) : GL (Fin d) (fixF σ)),
      (elemSL (fixF σ) hij).2, map_elemSL (fixF σ) hij⟩
  have hAscalar : A ∈ LargeEvenScalars (Fin d) K :=
    mem_scalars_of_commute_elemSL A fun i j hij => hH1comm _ (helem_mem i j hij)
  have hAcenter : A ∈ Subgroup.center (GL (Fin d) K) := by
    rw [← hscalarCenter]
    exact hAscalar
  refine MulEquiv.ext fun y => ?_
  change φ y = y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  change φ (LargeEvenProjMk SLK y) = LargeEvenProjMk SLK y
  let yA : SLK := ⟨A * (y : GL (Fin d) K) * A⁻¹, hconj_mem y⟩
  have h1 : φ (LargeEvenProjMk SLK y) = LargeEvenProjMk SLK yA := hA y yA rfl
  have hyA : yA = y := by
    apply Subtype.ext
    show A * (y : GL (Fin d) K) * A⁻¹ = (y : GL (Fin d) K)
    rw [← Subgroup.mem_center_iff.mp hAcenter (y : GL (Fin d) K)]
    group
  rw [h1, hyA]

theorem ggFixGeom_linear' (hd : 2 ≤ d) (hKok : SLOK d K) {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) {σ : K ≃+* K} (hk : SLOK d (fixF σ))
    {f : MulAut (LargeEvenProj SLK)} (hf : Induced σ f) :
    GGFixGeom (LargeEvenMatConjImage (LargeEvenProjMk SLK) Set.univ) f
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) (fixF σ))) Set.univ)
      (subfieldEquiv' hd hm hK hk hf).symm := by
  set e := subfieldEquiv' hd hm hK hk hf with he
  refine ⟨fun φ hφ hc => ?_, fun φ hφ _ htriv => ?_⟩
  · obtain ⟨B, hB⟩ := exists_conj_of_commute' hd hKok hf hφ hc
    refine ⟨(e.trans (ggFixDerRestrict hc)).trans e.symm, ⟨B, Set.mem_univ _, ?_⟩, ?_⟩
    · intro g g' hg
      change ((e.trans (ggFixDerRestrict hc)).trans e.symm) (QuotientGroup.mk g) =
        QuotientGroup.mk g'
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
      exact Subtype.ext (hB g g' hg)
    · intro g hg
      simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
  · refine eq_one_of_fixes_subfield' hd σ hk hφ fun g => htriv _ ?_
    rw [← range_subfieldHom' hd hm hK hk hf]
    exact ⟨g, rfl⟩

theorem exists_raw_linear' (hd : 2 ≤ d) (hKok : SLOK d K) {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) {p : ℕ}
    (hkok : ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 ^ (m / p) → SLOK d k)
    {f : MulAut (LargeEvenProj SLK)}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk SLK)) (hord : orderOf f = p) :
    LargeEvenRecipeLinear d (2 ^ (m / p)) fun R₀ _ I₀ _ => IsSimpleGroup R₀ ∧
      (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer f ≃* R₀,
        GGFixGeom (LargeEvenMatConjImage (LargeEvenProjMk SLK) Set.univ) f I₀ θ₀ := by
  obtain ⟨σ, hσ⟩ := exists_induced hf
  have hσord : orderOf σ = p :=
    (orderOf_eq_of_mk_matAct hd (slMapStable d K) hσ).trans hord
  obtain ⟨-, hcard⟩ := card_fixedPoints_field hm hK σ
  have hk : Nat.card (fixF σ) = 2 ^ (m / p) := by rw [card_fixF, hcard, hσord]
  have hkok' : SLOK d (fixF σ) := hkok (fixF σ) hk
  exact ⟨fixF σ, inferInstance, inferInstance, hk, isSimpleGroup_proj' hd _ hkok',
    exists_noncomm_proj' hd _ hkok', (subfieldEquiv' hd hm hK hkok' hσ).symm,
    ggFixGeom_linear' hd hKok hm hK hkok' hσ⟩

end CFSG.LocalAnalysis.GLTheoremA.T156.Lin

end
