module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieDescent
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootDefs
public import CFSG.RankThree.Chevalley.SteinbergBTE6HighestRootGraph
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.LieType.HighestRoot.CentChevalley

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial

section Aux

private abbrev fixSubfield {K : Type} [Field K] (σ : K ≃+* K) : Subfield K :=
  RingHom.eqLocusField σ.toRingHom (RingHom.id K)

private theorem exists_map_eq_of_forall_entry_mem_range {R S : Type} [Field R] [Field S]
    (f : R →+* S) (B : Matrix.SpecialLinearGroup (Fin 2) S)
    (h : ∀ i j, ∃ r : R, f r = (B : Matrix (Fin 2) (Fin 2) S) i j) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) R, Matrix.SpecialLinearGroup.map f A = B := by
  choose r hr using h
  have hmat : f.mapMatrix (Matrix.of r) = (B : Matrix (Fin 2) (Fin 2) S) := by
    ext i j
    simp [hr]
  have hdet : (Matrix.of r : Matrix (Fin 2) (Fin 2) R).det = 1 := by
    apply f.injective
    rw [RingHom.map_det, hmat, map_one]
    exact B.2
  let A : Matrix.SpecialLinearGroup (Fin 2) R := ⟨Matrix.of r, hdet⟩
  refine ⟨A, Subtype.ext ?_⟩
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  exact hmat

private theorem map_sl2Upper_eq_uSL {R S : Type} [Field R] [Field S] (f : R →+* S) (c : R) :
    Matrix.SpecialLinearGroup.map f (sl2Upper R c) = uSL (f c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Upper, uSL]

private theorem map_sl2Lower_eq_vSL {R S : Type} [Field R] [Field S] (f : R →+* S) (c : R) :
    Matrix.SpecialLinearGroup.map f (sl2Lower R c) = vSL (f c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Lower, vSL]

private theorem exists_twistedFrobenius {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    CharP K ℓ ∧ ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
      (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
        (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom =
          Fr.comp (algebraMap K (AlgebraicClosure K)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hchar : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI := hchar
  refine ⟨hchar, iterateFrobenius (AlgebraicClosure K) ℓ f, fun c => iterateFrobenius_def ℓ f c,
    RingHom.ext fun c => ?_⟩
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ, map_pow,
    iterateFrobenius_def]

end Aux

section SL2


private theorem baseChangeGL_mem_rootSubgroup {τ : Tag} {K L : Type} [Field K] [Field L]
    (ι : K →+* L) {β : Fin τ.rank → ℤ} {g : ModGL τ K} (hg : g ∈ rootSubgroup τ K β) :
    baseChangeGL ι g ∈ rootSubgroup τ L β := by
  have hle : rootSubgroup τ K β ≤ (rootSubgroup τ L β).comap (baseChangeGL ι) := by
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_pinnedX]
    exact Subgroup.subset_closure ⟨ι c, rfl⟩
  exact hle hg

private theorem pinnedX_pow_nat {τ : Tag} {K : Type} [Field K] (β : Fin τ.rank → ℤ) (c : K)
    (n : ℕ) : pinnedX τ K β c ^ n = pinnedX τ K β (n • c) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, pinnedX_zero]
  | succ n ih => rw [pow_succ, ih, ← pinnedX_add, succ_nsmul]

theorem pinnedX_mem_twistedE6RootGroup {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β = e6HighestRoot ∨ β = -e6HighestRoot) {c : K} (hc : σ c = c) :
    pinnedX TwistTag.E6.tag K β c ∈ twistedE6RootGroup K σ := by
  obtain ⟨hchar, Fr, hFr, hcomm⟩ := exists_twistedFrobenius hℓ K hK σ hσ
  haveI := hchar
  have hβmem : pinnedX TwistTag.E6.tag K β c ∈
      rootSubgroup TwistTag.E6.tag K e6HighestRoot ⊔
        rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) := by
    rcases hβ with rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨c, rfl⟩)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨c, rfl⟩)
  have hxfix : twistHom TwistTag.E6 K σ.toRingHom (pinnedX TwistTag.E6.tag K β c) =
      pinnedX TwistTag.E6.tag K β c := by
    rw [twistHom_apply, units_map_entrywiseHom_eq_baseChangeGL_self, baseChangeGL_pinnedX]
    have hσc : σ.toRingHom c = c := hc
    rw [hσc]
    exact diagramMap_fix_theta hβmem
  have hy := baseChangeGL_pinnedX (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K)) β c
  obtain ⟨w, hw, hwy⟩ := twE6_descent_of_pow hℓ hf K hK σ hσ Fr hFr hℓ hℓ3
    (x := baseChangeGL (algebraMap K (AlgebraicClosure K)) (pinnedX TwistTag.E6.tag K β c))
    (by rw [hy]; exact pinnedX_mem_adjointGroup _ _)
    (by rw [twistHom_baseChangeGL (algebraMap K (AlgebraicClosure K)) hcomm, hxfix])
    ⟨1, by
      rw [pow_one, ← map_pow, pinnedX_pow_nat, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
        pinnedX_zero, map_one]⟩
  rw [← baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) hwy]
  exact hw

private theorem rootSL2_mem_twE6LongRootSL2 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (B₀ : SL2 (fixSubfield σ)) :
    ∃ w ∈ twE6LongRootSL2 (twE6RootSubgroup K σ e6HighestRoot)
        (twE6RootSubgroup K σ (-e6HighestRoot)),
      (w : ModGL TwistTag.E6.tag K) = rootSL2 TwistTag.E6.tag K e6HighestRoot
        (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype B₀) := by
  let φ : SL2 (fixSubfield σ) →* ModGL TwistTag.E6.tag K :=
    (rootSL2 TwistTag.E6.tag K e6HighestRoot).comp
      (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype)
  have hX₀ : twE6RootSubgroup K σ e6HighestRoot ≤
      twE6LongRootSL2 (twE6RootSubgroup K σ e6HighestRoot)
        (twE6RootSubgroup K σ (-e6HighestRoot)) :=
    fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hX₀m : twE6RootSubgroup K σ (-e6HighestRoot) ≤
      twE6LongRootSL2 (twE6RootSubgroup K σ e6HighestRoot)
        (twE6RootSubgroup K σ (-e6HighestRoot)) :=
    fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hM : ((twE6LongRootSL2 (twE6RootSubgroup K σ e6HighestRoot)
      (twE6RootSubgroup K σ (-e6HighestRoot))).map (twistedE6RootGroup K σ).subtype).comap φ =
        ⊤ := by
    rw [eq_top_iff, ← sl2_closure_upper_lower (K := fixSubfield σ)]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply, map_sl2Upper_eq_uSL,
        rootSL2_uSL_eq]
      have hcσ : σ (c : K) = c := c.2
      have hc' : σ ((pinnedData TwistTag.E6.tag e6HighestRoot).2.2 • ((fixSubfield σ).subtype c)) =
          (pinnedData TwistTag.E6.tag e6HighestRoot).2.2 • ((fixSubfield σ).subtype c) := by
        rw [map_zsmul]
        exact congrArg _ hcσ
      have hmem := pinnedX_mem_twistedE6RootGroup hℓ hf hℓ3 K hK σ hσ (Or.inl rfl) hc'
      exact ⟨⟨_, hmem⟩, hX₀ (Subgroup.subset_closure ⟨_, rfl⟩), rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply, map_sl2Lower_eq_vSL]
      obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := K) (τ := TwistTag.E6.tag)
        (β := e6HighestRoot) isRoot_e6HighestRoot
      rw [hv]
      have hcσ : σ (c : K) = c := c.2
      have hc' : σ (ε * (fixSubfield σ).subtype c) = ε * (fixSubfield σ).subtype c := by
        rcases mul_self_eq_one_iff.1 hε with rfl | rfl
        · simpa using hcσ
        · simpa using hcσ
      have hmem := pinnedX_mem_twistedE6RootGroup hℓ hf hℓ3 K hK σ hσ (Or.inr rfl) hc'
      exact ⟨⟨_, hmem⟩, hX₀m (Subgroup.subset_closure ⟨_, rfl⟩), rfl⟩
  obtain ⟨w, hwH, hw⟩ := Subgroup.mem_map.1
    (Subgroup.mem_comap.1 (hM ▸ Subgroup.mem_top B₀ : B₀ ∈ _))
  exact ⟨w, hwH, hw⟩

private theorem exists_rootSL2_eq_of_mem_rootSpan {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (u : twistedE6RootGroup K σ)
    (hu : baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
      rootSpan TwistTag.E6.tag (AlgebraicClosure K) {e6HighestRoot, -e6HighestRoot}) :
    ∃ B₀ : SL2 (fixSubfield σ), (u : ModGL TwistTag.E6.tag K) =
      rootSL2 TwistTag.E6.tag K e6HighestRoot
        (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype B₀) := by
  obtain ⟨hchar, Fr, hFr, hcomm⟩ := exists_twistedFrobenius hℓ K hK σ hσ
  haveI := hchar
  set ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hι
  rw [CFSG.LieType.HighestRoot.rootSpan_pair_eq,
    ← range_rootSL2_of_isRoot (K := AlgebraicClosure K) isRoot_e6HighestRoot] at hu
  obtain ⟨B, hB⟩ := hu
  have hGfix : twistHom TwistTag.E6 K σ.toRingHom (u : ModGL TwistTag.E6.tag K) = u :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ u.2)).2
  have hFu : twistHom TwistTag.E6 (AlgebraicClosure K) Fr (baseChangeGL ι (u : ModGL _ K)) =
      baseChangeGL ι (u : ModGL _ K) := by
    rw [twistHom_baseChangeGL ι hcomm, hGfix]
  have hFρ : ∀ B' : SL2 (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr
          (rootSL2 TwistTag.E6.tag (AlgebraicClosure K) e6HighestRoot B') =
        rootSL2 TwistTag.E6.tag (AlgebraicClosure K) e6HighestRoot
          (Matrix.SpecialLinearGroup.map Fr B') := by
    intro B'
    rw [twistHom_apply, entrywise_rootSL2_of_field]
    refine diagramMap_fix_theta ?_
    rw [← range_rootSL2_of_isRoot isRoot_e6HighestRoot]
    exact ⟨_, rfl⟩
  have hBfix : Matrix.SpecialLinearGroup.map Fr B = B := by
    refine rootSL2_injective_of_field e6HighestRoot ?_
    calc rootSL2 TwistTag.E6.tag (AlgebraicClosure K) e6HighestRoot
          (Matrix.SpecialLinearGroup.map Fr B) =
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr
          (rootSL2 TwistTag.E6.tag (AlgebraicClosure K) e6HighestRoot B) := (hFρ B).symm
      _ = rootSL2 TwistTag.E6.tag (AlgebraicClosure K) e6HighestRoot B := by rw [hB, hFu]
  have hk : ∀ i j, ∃ d : fixSubfield σ, (ι.comp (fixSubfield σ).subtype) d =
      (B : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) i j := by
    intro i j
    have h1 : Fr ((B : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) i j) =
        (B : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) i j := by
      have := congrArg (fun M : SL2 (AlgebraicClosure K) =>
        (M : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) i j) hBfix
      simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
    rw [hFr] at h1
    have h2 : (B : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) i j ^ Nat.card K =
        (B : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) i j := by
      rw [hK, sq, pow_mul, h1, h1]
    obtain ⟨d, hd⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq h2
    refine ⟨⟨d, ?_⟩, hd⟩
    show σ.toRingHom d = (RingHom.id K) d
    apply ι.injective
    have hcd := congrArg (fun g => g d) hcomm
    simp only [RingHom.comp_apply] at hcd
    rw [RingHom.id_apply, hcd, hFr, hι, hd, h1]
  obtain ⟨B₀, hB₀⟩ := exists_map_eq_of_forall_entry_mem_range (ι.comp (fixSubfield σ).subtype) B hk
  refine ⟨B₀, baseChangeGL_injective ι ?_⟩
  rw [← hB, ← hB₀, baseChangeGL_rootSL2_of_field ι e6HighestRoot]
  congr 1

theorem mem_twE6LongRootSL2_std_iff {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (u : twistedE6RootGroup K σ) :
    u ∈ twE6LongRootSL2 (twE6RootSubgroup K σ e6HighestRoot)
        (twE6RootSubgroup K σ (-e6HighestRoot)) ↔
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
        rootSpan TwistTag.E6.tag (AlgebraicClosure K) {e6HighestRoot, -e6HighestRoot} := by
  constructor
  ·
    intro hu
    have hle : twE6LongRootSL2 (twE6RootSubgroup K σ e6HighestRoot)
        (twE6RootSubgroup K σ (-e6HighestRoot)) ≤
        (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {e6HighestRoot, -e6HighestRoot}).comap
          ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
            (twistedE6RootGroup K σ).subtype) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x (hx | hx)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply,
          CFSG.LieType.HighestRoot.rootSpan_pair_eq]
        exact Subgroup.mem_sup_left (baseChangeGL_mem_rootSubgroup _ hx)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply,
          CFSG.LieType.HighestRoot.rootSpan_pair_eq]
        exact Subgroup.mem_sup_right (baseChangeGL_mem_rootSubgroup _ hx)
    exact hle hu
  · intro hu
    obtain ⟨B₀, hB₀⟩ := exists_rootSL2_eq_of_mem_rootSpan hℓ K hK σ hσ u hu
    obtain ⟨w, hwS, hw⟩ := rootSL2_mem_twE6LongRootSL2 hℓ hf hℓ3 K hK σ hσ B₀
    have hwu : w = u := Subtype.ext (hw.trans hB₀.symm)
    rwa [hwu] at hwS

end SL2

end CFSG.LieType.SeitzGeneration.ExcWideThree
