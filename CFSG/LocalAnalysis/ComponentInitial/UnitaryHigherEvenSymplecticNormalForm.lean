module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSymplecticPrimeCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherOuterQuotient
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {r : ℕ} {K : Type} [Field K]

theorem spScalars_eq_bot_of_charTwo [NeZero r] [CharP K 2] : spScalars r K = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have h1 : Matrix.scalar (Fin r ⊕ Fin r) (c : K) ∈ symplecticGroup (Fin r) K := by
    rw [← CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup,
      ← GeneralLinearGroup.coe_scalar, hc]
    exact SymplecticTorusWeyl.mem_statedSp_iff.mp z.2
  have h2 := (CFSG.ClassicalGroups.Symplectic.scalar_mem_symplecticGroup_iff
    (Nat.pos_of_neZero r) (c : K)).mp h1
  have hc1 : c = 1 := by
    refine Units.ext ?_
    rcases (mul_self_eq_one_iff (a := (c : K))).mp (by rw [← sq]; exact h2) with h | h
    · exact h
    · rw [h, CharTwo.neg_eq, Units.val_one]
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [← hc, hc1, map_one]
  rfl

theorem proj_bijective_of_charTwo [NeZero r] [CharP K 2] : Function.Bijective (proj r K) :=
  ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [ker_proj, spScalars_eq_bot_of_charTwo]),
    proj_surjective⟩

theorem exists_conjAut_eq_statedSp [Finite K] [CharP K 2] (A : gsp r K) :
    ∃ s : StatedSp r K, conjAut r K A = conjAut r K ⟨s, statedSp_le_gsp s.2⟩ := by
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  have hμ' : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      fromBlocks 0 1 (-1) 0 *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          (μ : K) • fromBlocks 0 1 (-1) 0 := hμ
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) ((μ⁻¹ : Kˣ) : K)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact Units.ne_zero _ hb
  set z := GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (Units.mk0 b hb0) with hz
  have hs : z * (A : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff, Units.val_mul, hz, GeneralLinearGroup.coe_scalar,
      scalar_apply, ← smul_eq_diagonal_mul, transpose_smul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, hμ', smul_smul, smul_smul, Units.val_mk0, ← hb,
      Units.val_inv_eq_inv_val, inv_mul_cancel₀ μ.ne_zero, one_smul]
  have hzc : z ∈ Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  refine ⟨⟨_, hs⟩, ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [conjAut_proj, conjAut_proj]
  congr 1
  refine Subtype.ext ?_
  rw [coe_conjSp, coe_conjSp]
  change (A : GL (Fin r ⊕ Fin r) K) * g * (A : GL (Fin r ⊕ Fin r) K)⁻¹ =
    z * A * g * (z * A)⁻¹
  calc (A : GL (Fin r ⊕ Fin r) K) * g * (A : GL (Fin r ⊕ Fin r) K)⁻¹
      = (A : GL (Fin r ⊕ Fin r) K) * g * (A : GL (Fin r ⊕ Fin r) K)⁻¹ * z * z⁻¹ := by group
    _ = z * A * g * (z * A)⁻¹ := by
        rw [Subgroup.mem_center_iff.mp hzc]
        group

theorem spLinearAutGroup_eq_inner_of_charTwo [Finite K] [CharP K 2] :
    spLinearAutGroup r K = inner (StatedProj (StatedSp r K)) := by
  apply le_antisymm
  · intro α hα
    obtain ⟨A, rfl⟩ := mem_spLinearAutGroup_iff.mp hα
    obtain ⟨s, hs⟩ := exists_conjAut_eq_statedSp A
    rw [hs, conjAut_statedSp]
    exact ⟨_, rfl⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective x
    rw [← conjAut_statedSp]
    exact conjAut_mem_spLinearAutGroup _

variable (r K) in
@[expose] noncomputable def spNormalFormHom :
    StatedSp r K ⋊[fieldSp r K] (K ≃+* K) →* MulAut (StatedProj (StatedSp r K)) :=
  SemidirectProduct.lift ((conjAut r K).comp (Subgroup.inclusion statedSp_le_gsp)) (fieldAut r K)
    fun φ => MonoidHom.ext fun g => by
      change conjAut r K (Subgroup.inclusion statedSp_le_gsp (fieldSp r K φ g)) =
        fieldAut r K φ * conjAut r K (Subgroup.inclusion statedSp_le_gsp g) * (fieldAut r K φ)⁻¹
      rw [fieldAut_mul_conjAut_mul_inv]
      rfl

theorem spNormalFormHom_apply (g : StatedSp r K) (φ : K ≃+* K) :
    spNormalFormHom r K ⟨g, φ⟩ = conjAut r K ⟨g, statedSp_le_gsp g.2⟩ * fieldAut r K φ :=
  rfl

theorem range_spNormalFormHom [Finite K] [CharP K 2] :
    (spNormalFormHom r K).range = spSemilinearAutGroup r K := by
  apply le_antisymm
  · rintro _ ⟨⟨g, φ⟩, rfl⟩
    rw [spNormalFormHom_apply]
    exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup _))
      (fieldAut_mem_spSemilinearAutGroup φ)
  · intro α hα
    obtain ⟨A, φ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp hα
    obtain ⟨s, hs⟩ := exists_conjAut_eq_statedSp A
    exact ⟨⟨s, φ⟩, by rw [spNormalFormHom_apply, hs]⟩

theorem spNormalFormHom_injective [NeZero r] [CharP K 2] :
    Function.Injective (spNormalFormHom r K) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, φ⟩ hgφ
  rw [spNormalFormHom_apply] at hgφ
  have hπ := proj_bijective_of_charTwo (r := r) (K := K)
  have hcent : (g : GL (Fin r ⊕ Fin r) K) ∈
      Subgroup.centralizer (primeFieldSp r K : Set (GL (Fin r ⊕ Fin r) K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : (conjAut r K ⟨g, statedSp_le_gsp g.2⟩ * fieldAut r K φ)
        (proj r K ⟨h, primeFieldSp_le hh⟩) = proj r K ⟨h, primeFieldSp_le hh⟩ := by
      rw [hgφ, MulAut.one_apply]
    have hfix : fieldSp r K φ ⟨h, primeFieldSp_le hh⟩ = ⟨h, primeFieldSp_le hh⟩ :=
      Subtype.ext (glFieldEquiv_primeFieldSp φ hh)
    rw [MulAut.mul_apply, fieldAut_proj, hfix, conjAut_proj] at h1
    have h2 := congrArg (fun x : StatedSp r K => (x : GL (Fin r ⊕ Fin r) K)) (hπ.1 h1)
    change (g : GL (Fin r ⊕ Fin r) K) * h * (g : GL (Fin r ⊕ Fin r) K)⁻¹ = h at h2
    calc h * g = (g * h * (g : GL (Fin r ⊕ Fin r) K)⁻¹) * g := by rw [h2]
      _ = g * h := by group
  rw [centralizer_primeFieldSp] at hcent
  have hg1 : g = 1 := by
    have hz : g ∈ spScalars r K := Subgroup.mem_subgroupOf.mpr hcent
    rwa [spScalars_eq_bot_of_charTwo, Subgroup.mem_bot] at hz
  subst hg1
  have hf : fieldAut r K φ = 1 := by
    rw [show (⟨((1 : StatedSp r K) : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp (1 : StatedSp r K).2⟩ :
      gsp r K) = 1 from rfl, map_one, one_mul] at hgφ
    exact hgφ
  have hφ : φ = 1 := by
    ext t
    have hC : (t • single (0 : Fin r) (0 : Fin r) (1 : K))ᵀ = t • single 0 0 1 := by
      rw [transpose_smul, transpose_single]
    have h1 : fieldAut r K φ (proj r K (upperUnipotentSp r K hC)) =
        proj r K (upperUnipotentSp r K hC) := by
      rw [hf, MulAut.one_apply]
    rw [fieldAut_proj] at h1
    have h2 := congrArg (fun x : StatedSp r K =>
      ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl 0)
        (Sum.inr 0)) (hπ.1 h1)
    simp only [coe_fieldSp, Matrix.map_apply, coe_upperUnipotentSp] at h2
    simpa using h2
  exact SemidirectProduct.ext rfl hφ

theorem even_symplectic_semilinear_normal_form [NeZero r] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    Function.Bijective (proj r K) ∧
    spLinearAutGroup r K = inner (StatedProj (StatedSp r K)) ∧
    (∃ Ψ : StatedSp r K ⋊[fieldSp r K] (K ≃+* K) ≃* spSemilinearAutGroup r K,
      ∀ g φ, (Ψ ⟨g, φ⟩ : MulAut (StatedProj (StatedSp r K))) =
        conjAut r K ⟨g, statedSp_le_gsp g.2⟩ * fieldAut r K φ) ∧
    (∀ α ∈ spSemilinearAutGroup r K, ∃! x : StatedSp r K × (K ≃+* K),
      α = conjAut r K ⟨x.1, statedSp_le_gsp x.1.2⟩ * fieldAut r K x.2) ∧
    (∃ F : spSemilinearAutGroup r K →* (K ≃+* K),
      (∀ (α : spSemilinearAutGroup r K) (g : StatedSp r K) (φ : K ≃+* K),
        (α : MulAut (StatedProj (StatedSp r K))) =
          conjAut r K ⟨g, statedSp_le_gsp g.2⟩ * fieldAut r K φ → F α = φ) ∧
      F.ker = (inner (StatedProj (StatedSp r K))).subgroupOf (spSemilinearAutGroup r K) ∧
      Function.Surjective F ∧ IsCyclic (K ≃+* K) ∧ Nat.card (K ≃+* K) = f) ∧
    (∃ ι : StatedSp r K ≃* inner (StatedProj (StatedSp r K)),
      ∀ g, (ι g : MulAut (StatedProj (StatedSp r K))) = conjAut r K ⟨g, statedSp_le_gsp g.2⟩) ∧
    Subgroup.centralizer (primeFieldSp r K : Set (GL (Fin r ⊕ Fin r) K)) =
      StatedScalars (Fin r ⊕ Fin r) K := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  set Ψ : StatedSp r K ⋊[fieldSp r K] (K ≃+* K) ≃* spSemilinearAutGroup r K :=
    (MonoidHom.ofInjective spNormalFormHom_injective).trans
      (MulEquiv.subgroupCongr range_spNormalFormHom) with hΨdef
  have hΨ : ∀ x, (Ψ x : MulAut (StatedProj (StatedSp r K))) = spNormalFormHom r K x :=
    fun _ => rfl
  have hΨeq : ∀ (α : spSemilinearAutGroup r K) (g : StatedSp r K) (φ : K ≃+* K),
      (α : MulAut (StatedProj (StatedSp r K))) =
        conjAut r K ⟨g, statedSp_le_gsp g.2⟩ * fieldAut r K φ → Ψ ⟨g, φ⟩ = α :=
    fun α g φ h => Subtype.ext (by rw [hΨ, spNormalFormHom_apply, h])
  obtain ⟨σ, -, -, hzp, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  set j : StatedSp r K →* MulAut (StatedProj (StatedSp r K)) :=
    (spNormalFormHom r K).comp SemidirectProduct.inl with hjdef
  have hj : ∀ g, j g = conjAut r K ⟨g, statedSp_le_gsp g.2⟩ := fun g => by
    rw [show j g = spNormalFormHom r K ⟨g, 1⟩ from rfl, spNormalFormHom_apply, map_one, mul_one]
  have hjinj : Function.Injective j :=
    spNormalFormHom_injective.comp SemidirectProduct.inl_injective
  have hjrange : j.range = inner (StatedProj (StatedSp r K)) := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      rw [hj, conjAut_statedSp]
      exact ⟨_, rfl⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨g, rfl⟩ := proj_surjective x
      exact ⟨g, by rw [hj, conjAut_statedSp]⟩
  set F : spSemilinearAutGroup r K →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom with hFdef
  have hF : ∀ (α : spSemilinearAutGroup r K) (g : StatedSp r K) (φ : K ≃+* K),
      (α : MulAut (StatedProj (StatedSp r K))) =
        conjAut r K ⟨g, statedSp_le_gsp g.2⟩ * fieldAut r K φ → F α = φ := by
    intro α g φ h
    rw [← hΨeq α g φ h]
    change SemidirectProduct.rightHom (Ψ.symm (Ψ ⟨g, φ⟩)) = φ
    rw [MulEquiv.symm_apply_apply]
    rfl
  refine ⟨proj_bijective_of_charTwo, spLinearAutGroup_eq_inner_of_charTwo, ⟨Ψ, fun _ _ => rfl⟩,
    fun α hα => ?_, ⟨F, hF, ?_, fun φ => ⟨Ψ ⟨1, φ⟩, ?_⟩, isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨σ, hzp⟩, hcard⟩, ⟨(MonoidHom.ofInjective hjinj).trans (MulEquiv.subgroupCongr hjrange),
        fun g => hj g⟩, centralizer_primeFieldSp⟩
  ·
    obtain ⟨x, hx⟩ := Ψ.surjective ⟨α, hα⟩
    refine ⟨(x.left, x.right), ?_, ?_⟩
    · have h1 := congrArg Subtype.val hx
      rw [hΨ] at h1
      exact h1.symm
    · rintro ⟨g, φ⟩ hgφ
      have h1 := Ψ.injective ((hΨeq ⟨α, hα⟩ g φ hgφ).trans hx.symm)
      rw [← h1]
  ·
    ext α
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    obtain ⟨⟨g, φ⟩, rfl⟩ := Ψ.surjective α
    have hFΨ : F (Ψ ⟨g, φ⟩) = φ := hF _ g φ (by rw [hΨ, spNormalFormHom_apply])
    rw [hFΨ, hΨ, spNormalFormHom_apply]
    constructor
    · rintro rfl
      rw [map_one, mul_one, ← hjrange, ← hj]
      exact ⟨g, rfl⟩
    · intro hmem
      rw [← hjrange] at hmem
      obtain ⟨g', hg'⟩ := hmem
      rw [hj] at hg'
      have h1 : Ψ ⟨g', 1⟩ = Ψ ⟨g, φ⟩ :=
        Subtype.ext (by rw [hΨ, hΨ, spNormalFormHom_apply, spNormalFormHom_apply, map_one,
          mul_one, hg'])
      exact (congrArg SemidirectProduct.right (Ψ.injective h1)).symm
  ·
    exact hF _ 1 φ (by rw [hΨ, spNormalFormHom_apply])

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
