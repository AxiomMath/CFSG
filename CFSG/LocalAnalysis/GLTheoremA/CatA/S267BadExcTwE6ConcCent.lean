module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldBase
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LeviCatalogue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRTypes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6A5Cube CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Levi

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

@[expose] def primePowerOf (ℓ f : ℕ) [Fact ℓ.Prime] (hf : 1 ≤ f) : TauCeti.PrimePower :=
  ⟨ℓ, f, Fact.out, hf⟩

theorem card_primePowerOf (hf : 1 ≤ f) : (primePowerOf ℓ f hf).card = ℓ ^ f := by
  rw [TauCeti.PrimePower.card_def]
  rfl

theorem twE6LeviSA_le_twistedE6RootGroup (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) :
    twE6LeviSA K (unitaryInvolution K ℓ f) ≤ twistedE6RootGroup K (unitaryInvolution K ℓ f) := by
  have hperf := twE6LeviSA_perfect (unitaryInvolution K ℓ f) hK
    (unitaryInvolution_apply K ℓ f) (primePowerOf ℓ f hf) (card_primePowerOf hf)
  rw [← hperf]
  exact (Subgroup.commutator_mono inf_le_right inf_le_right).trans
    (commutator_twistedFixedGroup_le (unitaryInvolution K ℓ f).surjective)

omit [Finite K] in
theorem rootSpan_perpRoots_E6_eq_groupA :
    rootSpan Tag.E6 K (perpRoots Tag.E6) = groupA K := by
  have h := subsystemGroup_eq_rootSpan (τ := Tag.E6) (K := K)
    (C2E6Std.setA : Set (Fin Tag.E6.rank))
  refine Eq.trans ?_ h.symm
  congr 1
  ext γ
  simp only [perpRoots, parabolicRoots, Set.mem_setOf_eq]
  have hnode : ∀ i : Fin 6, i ∉ ({0, 2, 3, 4, 5} : Set (Fin 6)) ↔ i = 1 := by
    intro i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    fin_cases i <;> decide
  constructor
  · rintro ⟨hγ, h1⟩
    refine ⟨hγ, fun i hi => ?_⟩
    have hi1 : i = (1 : Fin 6) := (hnode i).1 hi
    rw [hi1]
    exact h1
  · rintro ⟨hγ, h1⟩
    exact ⟨hγ, h1 (1 : Fin 6) ((hnode 1).2 rfl)⟩

end Levi

section Iota

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)

@[expose] noncomputable def leviAnti : SU (unitaryInvolution K ℓ f) 6 →* ModGL Tag.E6 K :=
  (fixAToMod K (unitaryInvolution K ℓ f)).comp (leviHom (unitaryInvolution K ℓ f) hζ hσζ)

theorem range_leviAnti (hK : Nat.card K = (ℓ ^ f) ^ 2) :
    (leviAnti hζ hσζ).range = twE6LeviSA K (unitaryInvolution K ℓ f) := by
  rw [leviAnti, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 (leviHom_surjective (unitaryInvolution K ℓ f) hζ
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive hK) hσζ),
    ← MonoidHom.range_eq_map, range_fixAToMod]

theorem exists_smul_of_leviAnti_eq_one {x : SU (unitaryInvolution K ℓ f) 6}
    (hx : leviAnti hζ hσζ x = 1) :
    ∃ l : K, ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      l • (1 : Matrix (Fin 6) (Fin 6) K) :=
  leviHom_eq_one _ hζ hσζ (fixAToMod_injective _ (by rw [map_one]; exact hx))

theorem leviAnti_mul_self_eq_one {z : SU (unitaryInvolution K ℓ f) 6} {l : K}
    (hz : ((z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = l • (1 : Matrix (Fin 6) (Fin 6) K)) :
    leviAnti hζ hσζ (z * z) = 1 := by
  rw [leviAnti, MonoidHom.comp_apply, leviHom_scalar_sq _ hζ hσζ hz, map_one]

omit [Finite K] [Fact ℓ.Prime] [CharP K ℓ] in
theorem mem_center_of_coe_eq_smul {σ : K ≃+* K} {n : ℕ} {z : SU σ n} {l : K}
    (hz : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • (1 : Matrix (Fin n) (Fin n) K)) :
    z ∈ Subgroup.center (SU σ n) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hz, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

include hζ hσζ in
theorem isQuasisimple_twE6LeviSA (hK : Nat.card K = (ℓ ^ f) ^ 2) :
    CFSG.Open.IsQuasisimple ↥(twE6LeviSA K (unitaryInvolution K ℓ f)) ∧
      ∀ z ∈ Subgroup.center ↥(twE6LeviSA K (unitaryInvolution K ℓ f)), z * z = 1 := by
  have hmem : ∀ x, leviAnti hζ hσζ x ∈ twE6LeviSA K (unitaryInvolution K ℓ f) := fun x => by
    rw [← range_leviAnti hζ hσζ hK]
    exact ⟨x, rfl⟩
  set φ : SU (unitaryInvolution K ℓ f) 6 →* ↥(twE6LeviSA K (unitaryInvolution K ℓ f)) :=
    (leviAnti hζ hσζ).codRestrict _ hmem with hφ
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← range_leviAnti hζ hσζ hK] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hker : φ.ker ≤ Subgroup.center (SU (unitaryInvolution K ℓ f) 6) := by
    intro x hx
    have h1 : leviAnti hζ hσζ x = 1 := congrArg Subtype.val hx
    obtain ⟨l, hl⟩ := exists_smul_of_leviAnti_eq_one hζ hσζ h1
    exact mem_center_of_coe_eq_smul hl
  have hQS : CFSG.IsQuasisimple (SU (unitaryInvolution K ℓ f) 6) :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_SU hK (by norm_num) (by simp)
  refine ⟨(CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
    (CFSG.LocalCores.isQuasisimple_of_surjective hQS φ hφs hker), ?_⟩
  obtain ⟨-, hcen, -⟩ := cover_properties hQS hφs hker
  intro z hz
  rw [hcen] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨l, hl⟩ := (mem_center_SU_iff (unitaryInvolution K ℓ f) hK
    (CFSG.LieType.BorelTits.unitaryInvolution_apply K ℓ f) ⟨ℓ, f, Fact.out, rfl⟩ w).1 hw
  rw [← map_mul]
  exact Subtype.ext (leviAnti_mul_self_eq_one hζ hσζ hl)

end Iota

section RootSL2

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem pinnedX_highRoot_mem {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β = e6HighestRoot ∨ β = -e6HighestRoot) {c : K} (hc : unitaryInvolution K ℓ f c = c) :
    pinnedX TwistTag.E6.tag K β c ∈ twistedE6RootGroup K (unitaryInvolution K ℓ f) := by
  have hβmem : pinnedX TwistTag.E6.tag K β c ∈
      rootSubgroup TwistTag.E6.tag K e6HighestRoot ⊔
        rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) := by
    rcases hβ with rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨c, rfl⟩)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨c, rfl⟩)
  have hxfix : twistHom TwistTag.E6 K (unitaryInvolution K ℓ f).toRingHom
      (pinnedX TwistTag.E6.tag K β c) = pinnedX TwistTag.E6.tag K β c := by
    rw [twistHom_apply, units_map_entrywiseHom_eq_baseChangeGL_self, baseChangeGL_pinnedX]
    have hσc : (unitaryInvolution K ℓ f).toRingHom c = c := hc
    rw [hσc]
    exact diagramMap_fix_theta hβmem
  have hΓ : pinnedX TwistTag.E6.tag K β c ∈
      twistedFixedGroup TwistTag.E6 K (unitaryInvolution K ℓ f).toRingHom :=
    ⟨pinnedX_mem_adjointGroup _ _, hxfix⟩
  rcases hβ with rfl | rfl
  · refine Subgroup.mem_sup_left ⟨?_, hΓ⟩
    exact pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α})
      ⟨isRoot_e6HighestRoot, by rw [height_e6HighestRoot]; norm_num⟩ c
  · refine Subgroup.mem_sup_right ⟨?_, hΓ⟩
    exact pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.E6.tag α ∧ height α < 0})
      ⟨IsRoot.neg isRoot_e6HighestRoot, by rw [height_neg, height_e6HighestRoot]; norm_num⟩ c

noncomputable abbrev fixQ (K : Type) [Field K] [Finite K] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP K ℓ] : Subfield K :=
  RingHom.eqLocusField (unitaryInvolution K ℓ f).toRingHom (RingHom.id K)

theorem map_sl2Upper_eq_uSL' {R S : Type} [Field R] [Field S] (g : R →+* S) (c : R) :
    Matrix.SpecialLinearGroup.map g (CFSG.LocalAnalysis.ComponentInitial.sl2Upper R c) =
      uSL (g c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.LocalAnalysis.ComponentInitial.sl2Upper, uSL]

theorem map_sl2Lower_eq_vSL' {R S : Type} [Field R] [Field S] (g : R →+* S) (c : R) :
    Matrix.SpecialLinearGroup.map g (CFSG.LocalAnalysis.ComponentInitial.sl2Lower R c) =
      vSL (g c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.LocalAnalysis.ComponentInitial.sl2Lower, vSL]

theorem rootSL2_highRoot_mem (B₀ : SL2 (fixQ K ℓ f)) :
    rootSL2 TwistTag.E6.tag K e6HighestRoot (Matrix.SpecialLinearGroup.map (fixQ K ℓ f).subtype B₀) ∈
      twistedE6RootGroup K (unitaryInvolution K ℓ f) := by
  let φ : SL2 (fixQ K ℓ f) →* ModGL TwistTag.E6.tag K :=
    (rootSL2 TwistTag.E6.tag K e6HighestRoot).comp
      (Matrix.SpecialLinearGroup.map (fixQ K ℓ f).subtype)
  have hM : (twistedE6RootGroup K (unitaryInvolution K ℓ f)).comap φ = ⊤ := by
    rw [eq_top_iff, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply, map_sl2Upper_eq_uSL',
        rootSL2_uSL_eq]
      refine pinnedX_highRoot_mem (Or.inl rfl) ?_
      have hcσ : unitaryInvolution K ℓ f (c : K) = c := c.2
      rw [map_zsmul]
      exact congrArg _ hcσ
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply, map_sl2Lower_eq_vSL']
      obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := K) (τ := TwistTag.E6.tag)
        (β := e6HighestRoot) isRoot_e6HighestRoot
      rw [hv]
      refine pinnedX_highRoot_mem (Or.inr rfl) ?_
      have hcσ : unitaryInvolution K ℓ f (c : K) = c := c.2
      rcases mul_self_eq_one_iff.1 hε with rfl | rfl
      · simpa using hcσ
      · simpa using hcσ
  exact (Subgroup.mem_comap.1 (hM ▸ Subgroup.mem_top B₀ : B₀ ∈ _))

end RootSL2

section Centralizer

variable {K : Type} [Field K]

theorem mem_normalizer_groupA_of_commute {A P : SL2 K} {c : Kˣ} (hc1 : c ≠ 1) (hc2 : c ^ 2 ≠ 1)
    (hPA : P⁻¹ * A * P = CFSG.LieType.Chevalley.HSL c) {g : ModGL Tag.E6 K}
    (hg : g ∈ adjointGroup Tag.E6 K)
    (hgA : g * rootSL2 Tag.E6 K (highRoot Tag.E6) A = rootSL2 Tag.E6 K (highRoot Tag.E6) A * g) :
    g ∈ Subgroup.normalizer (groupA K : Set (ModGL Tag.E6 K)) := by
  have hτ : Tag.E6 = .F4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inr (Or.inl rfl)
  have hD := hrRootData_E (Or.inl rfl : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8)
  set ρ := rootSL2 Tag.E6 K (highRoot Tag.E6) with hρ
  have hρP : ρ P ∈ adjointGroup Tag.E6 K :=
    (exceptional_Lang_root_rank_one_data Tag.E6 K (highRoot Tag.E6)).2.2.2.2.1 P
  have hρPc : ∀ x ∈ rootSpan Tag.E6 K (perpRoots Tag.E6), ρ P * x = x * ρ P := by
    intro x hx
    have hle : (rootSL2 Tag.E6 K (highRoot Tag.E6)).range ≤
        Subgroup.centralizer (rootSpan Tag.E6 K (perpRoots Tag.E6) : Set (ModGL Tag.E6 K)) := by
      rw [range_rootSL2_of_isRoot (isRoot_highRoot Tag.E6)]
      refine sup_le ?_ ?_
      · have h := rootSubgroup_highRoot_le_centralizer (K := K) (ε := 1) (Or.inl rfl) hD.abs_le
          hD.eq_highRoot hD.highRoot_highNode
        rwa [one_smul] at h
      · have h := rootSubgroup_highRoot_le_centralizer (K := K) (ε := -1) (Or.inr rfl) hD.abs_le
          hD.eq_highRoot hD.highRoot_highNode
        rwa [neg_one_smul] at h
    exact (Subgroup.mem_centralizer_iff.1 (hle ⟨P, rfl⟩) x hx).symm
  set y := (ρ P)⁻¹ * g * ρ P with hy
  have hyA : y ∈ adjointGroup Tag.E6 K := mul_mem (mul_mem (inv_mem hρP) hg) hρP
  have hAe : A = P * HSL c * P⁻¹ := by
    calc A = P * (P⁻¹ * A * P) * P⁻¹ := by group
      _ = P * HSL c * P⁻¹ := by rw [hPA]
  have hyd : y * rootDiagUnit Tag.E6 (Pi.mulSingle (highNode Tag.E6) c) =
      rootDiagUnit Tag.E6 (Pi.mulSingle (highNode Tag.E6) c) * y := by
    rw [← rootTorusSL2_highRoot hτ c]
    change y * ρ (HSL c) = ρ (HSL c) * y
    have e : ρ (HSL c) = (ρ P)⁻¹ * ρ A * ρ P := by
      rw [hAe, map_mul, map_mul, map_inv]
      group
    rw [e, hy]
    calc (ρ P)⁻¹ * g * ρ P * ((ρ P)⁻¹ * ρ A * ρ P)
        = (ρ P)⁻¹ * (g * ρ A) * ρ P := by group
      _ = (ρ P)⁻¹ * (ρ A * g) * ρ P := by rw [hgA]
      _ = (ρ P)⁻¹ * ρ A * ρ P * ((ρ P)⁻¹ * g * ρ P) := by group
  have hyN := toralCentralizer_mulSingle_le_normalizer (τ := Tag.E6) (K := K) hc1 hc2 hD.abs_le
    (mem_toralCentralizer_of_commute (τ := Tag.E6) hyA hyd)
  rw [← rootSpan_perpRoots_E6_eq_groupA]
  have hρPN : ρ P ∈ Subgroup.normalizer
      (rootSpan Tag.E6 K (perpRoots Tag.E6) : Set (ModGL Tag.E6 K)) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun x hx => (hρPc x hx).symm)
  have hge : g = ρ P * y * (ρ P)⁻¹ := by rw [hy]; group
  rw [hge]
  exact mul_mem (mul_mem hρPN hyN) (inv_mem hρPN)

theorem rootSL2_highRoot_commute_of_mem_groupA (B : SL2 K) {x : ModGL Tag.E6 K}
    (hx : x ∈ groupA K) :
    rootSL2 Tag.E6 K (highRoot Tag.E6) B * x = x * rootSL2 Tag.E6 K (highRoot Tag.E6) B := by
  have hD := hrRootData_E (Or.inl rfl : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8)
  have hle : (rootSL2 Tag.E6 K (highRoot Tag.E6)).range ≤
      Subgroup.centralizer (rootSpan Tag.E6 K (perpRoots Tag.E6) : Set (ModGL Tag.E6 K)) := by
    rw [range_rootSL2_of_isRoot (isRoot_highRoot Tag.E6)]
    refine sup_le ?_ ?_
    · have h := rootSubgroup_highRoot_le_centralizer (K := K) (ε := 1) (Or.inl rfl) hD.abs_le
        hD.eq_highRoot hD.highRoot_highNode
      rwa [one_smul] at h
    · have h := rootSubgroup_highRoot_le_centralizer (K := K) (ε := -1) (Or.inr rfl) hD.abs_le
        hD.eq_highRoot hD.highRoot_highNode
      rwa [neg_one_smul] at h
  rw [← rootSpan_perpRoots_E6_eq_groupA] at hx
  exact (Subgroup.mem_centralizer_iff.1 (hle ⟨B, rfl⟩) x hx).symm

end Centralizer

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc

end
