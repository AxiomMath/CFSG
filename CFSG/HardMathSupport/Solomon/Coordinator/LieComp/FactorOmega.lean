module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OmegaFacts
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
import CFSG.Blueprint.SourceClassicalTransportOrthogonal
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofKleinSixB
import CFSG.RankThree.PartOne.K159.RowFourFixed
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LieType.Universal.SymplecticRoots
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDerived
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveSymplectic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroAction
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.RankThree.Classical2

namespace OmegaAux


private theorem orthFactorOver_sl {ℓ q : ℕ} {X E : Type} [Field E] [Fintype E] [Group X]
    {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hchar : ringChar E = ℓ)
    (hcard : Fintype.card E = q ^ j) (h4 : m = 2 → 4 ≤ Fintype.card E)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin m) E) : OrthFactorOver ℓ q X :=
  Or.inl ⟨m, j, E, inferInstance, inferInstance, hm, hj, hchar, hcard, h4, ⟨e⟩⟩

private theorem orthFactorOver_su {ℓ q : ℕ} {X E : Type} [Field E] [Fintype E] [Group X]
    {m j q' : ℕ} (hm : 3 ≤ m) (hj : 1 ≤ j) (hchar : ringChar E = ℓ) (hq' : q' = q ^ j)
    (hcard : Fintype.card E = q' ^ 2) (hne : (m, q') ≠ (3, 2))
    (e : X ≃* ↥(CFSG.Open.StatedSU m q' E)) : OrthFactorOver ℓ q X :=
  Or.inr (Or.inl ⟨m, j, q', E, inferInstance, inferInstance, hm, hj, hchar, hq', hcard, hne,
    ⟨e⟩⟩)

private theorem orthFactorOver_sp {ℓ q : ℕ} {X K' : Type} [Field K'] [Fintype K'] [Group X]
    (hK : Nat.card K' = q) (hchar : ringChar K' = ℓ) {s : ℕ} (hs : 2 ≤ s)
    (hne : (s, Nat.card K') ≠ (2, 2)) (e : X ≃* ↥(CFSG.Open.StatedSp s K')) :
    OrthFactorOver ℓ q X :=
  Or.inr (Or.inr (Or.inl ⟨K', inferInstance, inferInstance, hK, hchar, s, hs, hne, ⟨e⟩⟩))

private theorem orthFactorOver_orth {ℓ q : ℕ} {X K' : Type} [Field K'] [Fintype K'] [Group X]
    {V : Type} [AddCommGroup V] [Module K' V] [FiniteDimensional K' V]
    {Q : QuadraticForm K' V} (hK : Nat.card K' = q) (hchar : ringChar K' = ℓ)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : 7 ≤ Module.finrank K' V)
    (hT : ∃ U : Submodule K' V, Module.finrank K' U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (e : X ≃* ↥(orthDerived Q)) : OrthFactorOver ℓ q X :=
  Or.inr (Or.inr (Or.inr ⟨K', inferInstance, inferInstance, V, inferInstance, inferInstance,
    inferInstance, Q, hK, hchar, hQ, hd, hT, ⟨e⟩⟩))

private structure Cover (p d q : ℕ) {G : Type} [Group G] (L : Subgroup G) : Prop where
  fact : ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData p X ∧ OrthFactorOver p q X ∧
    ∃ f : X →* ↥L, Function.Surjective f ∧ f.ker ≤ Subgroup.center X
  a6 : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 6)) → p = 3 ∧ d ≤ 4

private theorem cover_of_range {p d q : ℕ} {G : Type} [Group G] {L : Subgroup G}
    (hL : CFSG.IsQuasisimple ↥L) {S : Type} [Group S] [Finite S]
    (hS : LieFactorData p S) (hSq : CFSG.IsQuasisimple S) (hfac : OrthFactorOver p q S)
    (hA6 : Nonempty ((S ⧸ Subgroup.center S) ≃* alternatingGroup (Fin 6)) → p = 3 ∧ d ≤ 4)
    (ψ : S →* G) (hψ : ψ.range = L) : Cover p d q L := by
  have hnt : ψ.range ≠ ⊥ := by
    rw [hψ]
    intro h
    have := CFSG.LocalCores.isQuasisimple_nontrivial hL
    rw [h] at this
    exact not_nontrivial_iff_subsingleton.mpr inferInstance this
  let f : S →* ↥L := (MulEquiv.subgroupCongr hψ).toMonoidHom.comp ψ.rangeRestrict
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨z, hz⟩ := ψ.rangeRestrict_surjective ((MulEquiv.subgroupCongr hψ).symm y)
    exact ⟨z, by simp [f, hz]⟩
  have hkerf : f.ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change (MulEquiv.subgroupCongr hψ) (ψ.rangeRestrict x) = 1 ↔ ψ x = 1
    rw [MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hker : f.ker ≤ Subgroup.center S := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hSq
      (MonoidHom.normal_ker ψ).isSubnormal with h | h
    · exfalso
      apply hnt
      rw [eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
    · rwa [hkerf]
  refine ⟨⟨S, inferInstance, inferInstance, hS, hfac, f, hf, hker⟩, fun ⟨e⟩ => hA6 ?_⟩
  obtain ⟨e'⟩ := nonempty_centralQuotient_mulEquiv hS.perfect f hf hker
  exact ⟨e'.trans e⟩


section Components

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

private def ιO (Q : QuadraticForm K V) :
    ↥(orthDerived Q) →* ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
  Subgroup.inclusion CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup

private theorem ιO_injective (Q : QuadraticForm K V) : Function.Injective (ιO Q) :=
  Subgroup.inclusion_injective _

@[simp] private theorem coe_ιO (Q : QuadraticForm K V) (x : ↥(orthDerived Q)) :
    ((ιO Q x : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) : V ≃ₗ[K] V) = (x : V ≃ₗ[K] V) :=
  rfl

private theorem range_ιO (Q : QuadraticForm K V) :
    (ιO Q).range = commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have hc : commutator ↥O = (orthDerived Q).subgroupOf O := by
    apply Subgroup.map_injective O.subtype_injective
    rw [Subgroup.map_subtype_commutator, Subgroup.map_subgroupOf_eq_of_le
      CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup]
  rw [hc]
  exact Subgroup.inclusion_range _

private theorem isComponent_map_ιO (Q : QuadraticForm K V) {L : Subgroup ↥(orthDerived Q)}
    [hL : L.Normal] (hLq : CFSG.IsQuasisimple ↥L) : CFSG.IsComponent (L.map (ιO Q)) := by
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (L.equivMapOfInjective (ιO Q) (ιO_injective Q)) hLq, ?_⟩
  have hC : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)).Normal := inferInstance
  have hle : L.map (ιO Q) ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [← range_ιO]
    exact Subgroup.map_le_range _ _
  refine Subgroup.IsSubnormal.step _ (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) hle
    hC.isSubnormal ?_
  rw [Subgroup.normal_subgroupOf_iff hle]
  rintro _ k ⟨a, ha, rfl⟩ hk
  rw [← range_ιO] at hk
  obtain ⟨b, rfl⟩ := hk
  exact ⟨b * a * b⁻¹, hL.conj_mem a ha b, by simp⟩

private theorem exists_lift_of_range_eq {Q : QuadraticForm K V} {S : Type} [Group S]
    (φ : S →* ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) (L : Subgroup ↥(orthDerived Q))
    (h : φ.range = L.map (ιO Q)) : ∃ ψ : S →* ↥(orthDerived Q), ψ.range = L := by
  have hle : ∀ s, φ s ∈ (ιO Q).range := fun s => by
    have : φ s ∈ L.map (ιO Q) := h ▸ ⟨s, rfl⟩
    exact Subgroup.map_le_range _ _ this
  let e : ↥(orthDerived Q) ≃* ↥(ιO Q).range := MonoidHom.ofInjective (ιO_injective Q)
  let ψ : S →* ↥(orthDerived Q) := e.symm.toMonoidHom.comp (φ.codRestrict _ hle)
  have hψ : ∀ s, ιO Q (ψ s) = φ s := fun s => by
    have := e.apply_symm_apply (φ.codRestrict _ hle s)
    exact congrArg Subtype.val this
  refine ⟨ψ, ?_⟩
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    have h1 : ιO Q (ψ s) ∈ L.map (ιO Q) := by rw [hψ, ← h]; exact ⟨s, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h1
    rwa [← ιO_injective Q hyx]
  · intro hx
    have h1 : ιO Q x ∈ φ.range := by rw [h]; exact ⟨x, hx, rfl⟩
    obtain ⟨s, hs⟩ := h1
    exact ⟨s, ιO_injective Q ((hψ s).trans hs)⟩

end Components



section Generic
variable {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

private theorem not_le_center_of_isQuasisimple {G : Type} [Group G] {L : Subgroup G}
    (hL : CFSG.IsQuasisimple ↥L) : ¬ L ≤ Subgroup.center G := by
  intro h
  obtain ⟨a, b, hab⟩ := hL.2.2
  induction a using QuotientGroup.induction_on with | H x => ?_
  induction b using QuotientGroup.induction_on with | H y => ?_
  apply hab
  have : (x : G) * y = y * (x : G) := (Subgroup.mem_center_iff.mp (h x.2) y).symm
  have h' : x * y = y * x := Subtype.ext this
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h']

private theorem eq_top_of_isQuasisimple {G : Type} [Group G] (hG : CFSG.IsQuasisimple G)
    {L : Subgroup G} (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) : L = ⊤ := by
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hG
    hLn.isSubnormal with h | h
  · exact h
  · exact absurd h (not_le_center_of_isQuasisimple hL)

private theorem finite_orthDerived (Q : QuadraticForm K V) : Finite ↥(orthDerived Q) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  infer_instance


end Generic

section C

open CFSG.RankThree.Classical2 CFSG.HardMathSupport.Solomon.Coordinator.LieComp

namespace C


section Singular

variable {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem exists_singular_of_similar {W : Type} [AddCommGroup W] [Module K W]
    {Q' : QuadraticForm K W} (e : V ≃ₗ[K] W) {d : K} (hd : d ≠ 0)
    (h : ∀ v, Q' (e v) = d * Q v)
    (hT : ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q' x = 0) :
    ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  obtain ⟨T', hT3, hT'⟩ := hT
  refine ⟨T'.map (e.symm : W →ₗ[K] V), ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq e.symm T', hT3]
  · rintro x ⟨y, hy, rfl⟩
    have h1 := h (e.symm y)
    rw [LinearEquiv.apply_symm_apply, hT' y hy] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hd

private theorem ringChar_ne_two_of_odd_finrank
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hn : Module.finrank K V = 2 * n + 1) : ringChar K ≠ 2 := by
  intro h2
  haveI : CharP K 2 := ringChar.of_eq h2
  have := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  rw [hn, Nat.even_iff] at this
  omega

private theorem large_exists_singular (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : 7 ≤ Module.finrank K V) :
    ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  rcases Nat.even_or_odd' (Module.finrank K V) with ⟨n, hn | hn⟩
  ·
    have hn4 : 4 ≤ n := by omega
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Q hQ
      (by omega) hn with ⟨⟨e⟩⟩ | ⟨b, c, hirr, ⟨e⟩⟩
    · exact exists_singular_of_similar e.toLinearEquiv one_ne_zero
        (fun v => by rw [one_mul]; exact e.map_app v)
        (CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (by omega)).2
    · exact exists_singular_of_similar e.toLinearEquiv one_ne_zero
        (fun v => by rw [one_mul]; exact e.map_app v)
        (CFSG.ClassicalGroups.Orthogonal.regular_quadMinus hn4 hirr).2
  ·
    have h2 := ringChar_ne_two_of_odd_finrank hQ hn
    obtain ⟨d, hd0, ⟨e⟩⟩ := CFSG.GroupTheory.WeirSylow.exists_smul_isometry_quadOdd h2 Q hQ hn
    exact exists_singular_of_similar e.toLinearEquiv hd0 (fun v => e.map_app v)
      (CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (Ring.two_ne_zero h2) (by omega)).2

end Singular

section Stated

open TauCeti CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.Adapters.RankTwoModelTransports
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv statedOmega_eq_comap mem_statedScalars_iff)

private theorem nonempty_statedProj_equiv_projOrthDerived {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    Nonempty (StatedProj (StatedOmega Q₀) ≃* ProjOrthDerived Q) := by
  have hmap : (StatedOmega Q₀).map (toLinEquiv ι K).toMonoidHom = orthDerived Q := by
    rw [statedOmega_eq_comap hQ]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective _
  let e₁ : StatedOmega Q₀ ≃* orthDerived Q :=
    ((toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans (MulEquiv.subgroupCongr hmap)
  have he₁ : ∀ A : StatedOmega Q₀,
      ((e₁ A : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) = toLinEquiv ι K A := fun _ => rfl
  refine ⟨QuotientGroup.congr _ _ e₁ ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff] at hy
    rw [Subgroup.mem_subgroupOf]
    exact hy
  · intro hx
    refine ⟨e₁.symm x, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
    rw [Subgroup.mem_subgroupOf] at hx
    have h1 : ((e₁ (e₁.symm x) : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) = x := by
      rw [MulEquiv.apply_symm_apply]
    rw [he₁] at h1
    rw [h1]
    exact hx

private theorem nonempty_ringEquiv_fixedField {K : Type} [Field K] [Fintype K]
    (d : ValidLieTypeIndex)
    (hK : Fintype.card K = d.fieldOrder) : Nonempty (K ≃+* ↥d.fixedField) := by
  haveI : Finite d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let _ : Fintype d.fixedField := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card d.fixedField := by
    rw [← Nat.card_eq_fintype_card (α := d.fixedField), ValidLieTypeIndex.card_fixedField]
    exact hK
  exact ⟨FiniteField.ringEquivOfCardEq hcard⟩

theorem exists_mulEquiv_catalogue_statedProj_odd {K : Type} [Field K] [Fintype K] (n : ℕ)
    (hn : 3 ≤ n) (h2 : ringChar K ≠ 2) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.B n q).Valid), q.card = Fintype.card K ∧
      q.p = ringChar K ∧
      Nonempty (StatedProj (StatedOmega (StatedQuadOdd n K)) ≃*
        (TauCeti.CFSGIndex.lie ⟨.B n q, hv⟩).Group) := by
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  let q : PrimePower := ⟨ringChar K, f, hp, f.pos⟩
  have hv : (LieTypeIndex.B n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
  obtain ⟨φ⟩ := nonempty_ringEquiv_fixedField (K := K) ⟨.B n q, hv⟩ (by
    simp [ValidLieTypeIndex.fieldOrder, q, hcard])
  refine ⟨q, hv, ?_, rfl, ⟨(statedProjCongr (glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadOdd_comp φ)) (glCongr_statedScalars φ)).trans
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n q hv h2
        hn).symm⟩⟩
  rw [PrimePower.card_def, hcard]

private theorem isChevSimple_statedProj_odd {K : Type} [Field K] [Fintype K] (n : ℕ) (hn : 3 ≤ n)
    (h2 : ringChar K ≠ 2) :
    IsChevSimple (ringChar K) (StatedProj (StatedOmega (StatedQuadOdd n K))) := by
  obtain ⟨q, hv, -, hqp, ⟨iso⟩⟩ := exists_mulEquiv_catalogue_statedProj_odd (K := K) n hn h2
  exact Or.inl ⟨.lie ⟨.B n q, hv⟩, (LieTypeIndex.characteristic_B n q).trans hqp, ⟨iso⟩⟩

theorem exists_mulEquiv_catalogue_statedProj_plus {K : Type} [Field K] [Fintype K] (n : ℕ)
    (hn : 4 ≤ n) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.D n q).Valid), q.card = Fintype.card K ∧
      q.p = ringChar K ∧
      Nonempty (StatedProj (StatedOmega (StatedQuadPlus n K)) ≃*
        (TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩).Group) := by
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  let q : PrimePower := ⟨ringChar K, f, hp, f.pos⟩
  have hv : (LieTypeIndex.D n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨φ⟩ := nonempty_ringEquiv_fixedField (K := K) ⟨.D n q, hv⟩ (by
    simp [ValidLieTypeIndex.fieldOrder, q, hcard])
  refine ⟨q, hv, ?_, rfl, ⟨(statedProjCongr (glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ)) (glCongr_statedScalars φ)).trans
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n q hv).symm⟩⟩
  rw [PrimePower.card_def, hcard]

private theorem isChevSimple_statedProj_plus {K : Type} [Field K] [Fintype K] (n : ℕ) (hn : 4 ≤ n) :
    IsChevSimple (ringChar K) (StatedProj (StatedOmega (StatedQuadPlus n K))) := by
  obtain ⟨q, hv, -, hqp, ⟨iso⟩⟩ := exists_mulEquiv_catalogue_statedProj_plus (K := K) n hn
  exact Or.inl ⟨.lie ⟨.D n q, hv⟩, (LieTypeIndex.characteristic_D n q).trans hqp, ⟨iso⟩⟩

theorem exists_mulEquiv_catalogue_statedProj_minus {K : Type} [Field K] [Fintype K] (n : ℕ)
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedD n q).Valid), q.card = Fintype.card K ∧
      q.p = ringChar K ∧
      Nonempty (StatedProj (StatedOmega (StatedQuadMinus n K b c)) ≃*
        (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group) := by
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  let q : PrimePower := ⟨ringChar K, f, hp, f.pos⟩
  have hv : (LieTypeIndex.twistedD n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      n q hv
  obtain ⟨φ⟩ := nonempty_ringEquiv_fixedField (K := K) ⟨.twistedD n q, hv⟩ (by
    simp [ValidLieTypeIndex.fieldOrder, q, hcard])
  haveI : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD n q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := n) (by omega)
    (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hirr) hirr₀
  let e1 := statedProjCongr (glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := n) (b := b) (c := c) φ rfl
        rfl))
    (glCongr_statedScalars φ)
  refine ⟨q, hv, ?_, rfl, ⟨(e1.trans e2).trans eT.symm⟩⟩
  rw [PrimePower.card_def, hcard]

private theorem isChevSimple_statedProj_minus {K : Type} [Field K] [Fintype K] (n : ℕ) (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsChevSimple (ringChar K) (StatedProj (StatedOmega (StatedQuadMinus n K b c))) := by
  obtain ⟨q, hv, -, hqp, ⟨iso⟩⟩ := exists_mulEquiv_catalogue_statedProj_minus (K := K) n hn hirr
  exact Or.inl ⟨.lie ⟨.twistedD n q, hv⟩,
    (LieTypeIndex.characteristic_twistedD n q).trans hqp, ⟨iso⟩⟩

end Stated

section Main

variable {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LieType.Universal.Spin

private theorem large_chev (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : 7 ≤ Module.finrank K V) :
    CFSG.Yardstones.Md0ec50421ce4.IsChevSimple (ringChar K)
      (↥(orthDerived Q) ⧸ Subgroup.center ↥(orthDerived Q)) := by
  obtain ⟨T, hT3, hT⟩ := large_exists_singular hQ hd
  obtain ⟨-, hcenter, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ
      ⟨T, hT3, hT⟩
  refine isChevSimple_congr (QuotientGroup.quotientMulEquivOfEq hcenter).symm ?_
  rcases Nat.even_or_odd' (Module.finrank K V) with ⟨n, hn | hn⟩
  ·
    have hn4 : 4 ≤ n := by omega
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Q hQ
      (by omega) hn with ⟨⟨e⟩⟩ | ⟨b, c, hirr, ⟨e⟩⟩
    · exact isChevSimple_congr
        (((nonempty_statedProj_equiv_projOrthDerived (coe_quadPlus n K)).some).trans
          (CFSG.RankThree.PartOne.KCOrthogonalDescent.projOrthDerivedEquiv e.toLinearEquiv 1
            (fun v => by rw [Units.val_one, one_mul]; exact e.map_app v)).symm)
        (isChevSimple_statedProj_plus n hn4)
    · exact isChevSimple_congr
        (((nonempty_statedProj_equiv_projOrthDerived (coe_quadMinus n K b c)).some).trans
          (CFSG.RankThree.PartOne.KCOrthogonalDescent.projOrthDerivedEquiv e.toLinearEquiv 1
            (fun v => by rw [Units.val_one, one_mul]; exact e.map_app v)).symm)
        (isChevSimple_statedProj_minus n hn4 hirr)
  ·
    have hn3 : 3 ≤ n := by omega
    have h2 := ringChar_ne_two_of_odd_finrank hQ hn
    obtain ⟨d, hd0, ⟨e⟩⟩ := CFSG.GroupTheory.WeirSylow.exists_smul_isometry_quadOdd h2 Q hQ hn
    exact isChevSimple_congr
      (((nonempty_statedProj_equiv_projOrthDerived (coe_quadOdd n K)).some).trans
        (CFSG.RankThree.PartOne.KCOrthogonalDescent.projOrthDerivedEquiv e.toLinearEquiv
          (Units.mk0 d hd0) (fun v => e.map_app v)).symm)
      (isChevSimple_statedProj_odd n hn3 h2)

end Main


end C

end C

section M

open CFSG.RankThree.Classical2 CFSG.HardMathSupport.Solomon.Coordinator.LieComp

namespace M


variable {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem comm_of_finrank_le_one (hd : Module.finrank K V ≤ 1) (f g : V ≃ₗ[K] V) :
    f * g = g * f := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hd
  obtain ⟨a, ha⟩ := hv (f v)
  obtain ⟨b, hb⟩ := hv (g v)
  ext w
  obtain ⟨c, rfl⟩ := hv w
  have h1 : f (g (c • v)) = (c * b * a) • v := by
    rw [map_smul g, ← hb, map_smul f, map_smul f, ← ha, smul_smul, smul_smul]
  have h2 : g (f (c • v)) = (c * a * b) • v := by
    rw [map_smul f, ← ha, map_smul g, map_smul g, ← hb, smul_smul, smul_smul]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, h2]
  congr 1
  ring

private theorem case_le_two (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V ≤ 2) (L : Subgroup ↥(orthDerived Q))
    (hL : CFSG.IsQuasisimple ↥L) : False := by
  have hcomm : ∀ x y : ↥(orthDerived Q), x * y = y * x := by
    intro x y
    apply Subtype.ext
    rcases Nat.lt_or_ge (Module.finrank K V) 2 with h | h
    · exact comm_of_finrank_le_one (show Module.finrank K V ≤ 1 by omega) x y
    · exact CFSG.RankThree.PartOne.KCOrthogonal.commute_of_dicksonHom_eq_one hQ
        (show Module.finrank K V = 2 by omega)
        (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup x.2)
        (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup y.2)
        (CFSG.RankThree.PartOne.KCOrthogonal.dicksonHom_apply_orthDerived_eq_one hQ x.2)
        (CFSG.RankThree.PartOne.KCOrthogonal.dicksonHom_apply_orthDerived_eq_one hQ y.2)
  refine OmegaAux.not_le_center_of_isQuasisimple hL fun x _ => ?_
  rw [Subgroup.mem_center_iff]
  intro y
  exact hcomm y x


private theorem odd_case_contra {q a k W : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (ha : 9 ≤ a)
    (hdvd : q ^ a ∣ 2 ^ k * W) (hW : W ∣ 720) : False := by
  have hcop : Nat.Coprime (q ^ a) (2 ^ k) := Nat.Coprime.pow _ _ (Nat.coprime_two_right.2 hqodd)
  have h1 : q ^ a ∣ W := hcop.dvd_of_dvd_mul_left hdvd
  have h2 : q ^ a ∣ 720 := h1.trans hW
  have h3 : q ^ a ≤ 720 := Nat.le_of_dvd (by norm_num) h2
  have h4 : 3 ^ 9 ≤ q ^ a :=
    (Nat.pow_le_pow_left hq 9).trans (Nat.pow_le_pow_right (by omega) ha)
  have h5 : (3 : ℕ) ^ 9 = 19683 := by norm_num
  omega

private theorem even_case_contra {q k W : ℕ} (hq : 2 ≤ q) (hqeven : Even q)
    (hdvd : q ^ 6 - 1 ∣ 2 ^ k * W) (hW : W ∣ 720) : False := by
  have hq6 : 64 ≤ q ^ 6 := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
  have hodd : Odd (q ^ 6 - 1) := by
    obtain ⟨t, ht⟩ := hqeven.pow_of_ne_zero (show (6 : ℕ) ≠ 0 by norm_num)
    exact ⟨t - 1, by omega⟩
  have hcop : Nat.Coprime (q ^ 6 - 1) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  have h1 : q ^ 6 - 1 ∣ W := hcop.dvd_of_dvd_mul_left hdvd
  have h2 : q ^ 6 - 1 ∣ 720 := h1.trans hW
  have h3 : 63 ≤ q ^ 6 - 1 := by omega
  have h4 : q ^ 6 - 1 ∈ Nat.divisors 720 := Nat.mem_divisors.2 ⟨h2, by norm_num⟩
  have key : ∀ d ∈ Nat.divisors 720, 63 ≤ d → Even d := by decide
  exact (Nat.not_even_iff_odd.2 hodd) (key _ h4 h3)


private theorem large_no_a6 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : 7 ≤ Module.finrank K V) :
    IsEmpty ((↥(orthDerived Q) ⧸ Subgroup.center ↥(orthDerived Q)) ≃*
      alternatingGroup (Fin 6)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨T, hT3, hT⟩ := OmegaAux.C.large_exists_singular hQ hd
  obtain ⟨-, hcenter, hZ2, -, -, hsq, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ
      ⟨T, hT3, hT⟩
  haveI := OmegaAux.finite_orthDerived Q
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have h360 : Nat.card (↥(orthDerived Q) ⧸ Subgroup.center ↥(orthDerived Q)) = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hmul := (Subgroup.center ↥(orthDerived Q)).card_eq_card_quotient_mul_card_subgroup
  rw [h360] at hmul
  have hz2 : Nat.card ↥(Subgroup.center ↥(orthDerived Q)) ≤ 2 := by rw [hcenter]; exact hZ2
  have hz0 : 0 < Nat.card ↥(Subgroup.center ↥(orthDerived Q)) := Nat.card_pos
  have hW : Nat.card ↥(orthDerived Q) ∣ 720 := by
    rcases (show Nat.card ↥(Subgroup.center ↥(orthDerived Q)) = 1 ∨
        Nat.card ↥(Subgroup.center ↥(orthDerived Q)) = 2 by omega) with h | h
    · rw [hmul, h] <;> norm_num
    · rw [hmul, h] <;> norm_num
  have hsq' : ∀ g : ↥O, g ^ 2 ∈ commutator ↥O := by
    intro g
    rw [← OmegaAux.range_ιO]
    exact ⟨⟨(g : V ≃ₗ[K] V) ^ 2, hsq g g.2⟩, Subtype.ext rfl⟩
  have hp2 : IsPGroup 2 (↥O ⧸ commutator ↥O) :=
    CFSG.LocalAnalysis.ComponentInitial.isPGroup_two_of_forall_sq_mem hsq'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥O := by
    have : Finite V := Module.finite_of_finite K
    have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    infer_instance
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp2
  have hN : Nat.card ↥O = 2 ^ k * Nat.card ↥(orthDerived Q) := by
    rw [(commutator ↥O).card_eq_card_quotient_mul_card_subgroup, hk]
    congr 1
    rw [← OmegaAux.range_ιO]
    exact (Nat.card_congr (MonoidHom.ofInjective (OmegaAux.ιO_injective Q)).toEquiv).symm
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  rcases Nat.even_or_odd (Module.finrank K V) with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hdim : Module.finrank K V = 2 * (m' + 1) := by omega
    have hm3 : 3 ≤ m' := by omega
    obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (ε = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q) ∨
        (ε = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) := by
      by_cases h : CFSG.GroupTheory.WeirSylow.IsPlusType Q
      · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
      · exact ⟨-1, Or.inr ⟨rfl, h⟩⟩
    have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hdim hε
    by_cases hqe : Even (Nat.card K)
    ·
      have h3 : (3 : ℕ) ∈ Finset.Icc 1 m' := Finset.mem_Icc.2 ⟨by norm_num, hm3⟩
      have hP := Finset.dvd_prod_of_mem (fun i : ℕ => (((Nat.card K : ℤ) ^ 2) ^ i - 1)) h3
      have hdvdZ : ((Nat.card K : ℤ) ^ 6 - 1) ∣ (Nat.card ↥O : ℤ) := by
        rw [hcard]
        have h6 : (((Nat.card K : ℤ) ^ 2) ^ 3 - 1) = (Nat.card K : ℤ) ^ 6 - 1 := by ring
        rw [h6] at hP
        exact Dvd.dvd.mul_left hP _
      have hq6 : 1 ≤ Nat.card K ^ 6 := Nat.one_le_pow _ _ (by omega)
      have hdvd : Nat.card K ^ 6 - 1 ∣ Nat.card ↥O := by
        have : (((Nat.card K ^ 6 - 1 : ℕ)) : ℤ) = (Nat.card K : ℤ) ^ 6 - 1 := by
          push_cast [Nat.cast_sub hq6]
          ring
        rw [← Int.natCast_dvd_natCast, this]
        exact hdvdZ
      rw [hN] at hdvd
      exact even_case_contra hq2 hqe hdvd hW
    ·
      have hqo : Odd (Nat.card K) := Nat.not_even_iff_odd.1 hqe
      have hq3 : 3 ≤ Nat.card K := by
        obtain ⟨t, ht⟩ := hqo
        omega
      have hdvdZ : ((Nat.card K : ℤ) ^ (m' * (m' + 1))) ∣ (Nat.card ↥O : ℤ) := by
        rw [hcard]
        exact Dvd.intro ((2 * ((Nat.card K : ℤ) ^ (m' + 1) - ε)) *
          ∏ i ∈ Finset.Icc 1 m', (((Nat.card K : ℤ) ^ 2) ^ i - 1)) (by ring)
      have hdvd : Nat.card K ^ (m' * (m' + 1)) ∣ Nat.card ↥O := by
        rw [← Int.natCast_dvd_natCast]
        push_cast
        exact hdvdZ
      rw [hN] at hdvd
      refine odd_case_contra hq3 hqo ?_ hdvd hW
      calc 9 ≤ 3 * 4 := by norm_num
        _ ≤ m' * (m' + 1) := Nat.mul_le_mul hm3 (by omega)
  ·
    have hm3 : 3 ≤ m := by omega
    have h2 : ringChar K ≠ 2 := by
      intro h
      haveI : CharP K 2 := ringChar.of_eq h
      have hev := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
      rw [hm] at hev
      exact (Nat.not_even_iff_odd.2 ⟨m, rfl⟩) hev
    have hqo : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
    have hq3 : 3 ≤ Nat.card K := by
      obtain ⟨t, ht⟩ := hqo
      omega
    have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd h2 hQ (n := m)
      (by omega)
    have hdvdZ : ((Nat.card K : ℤ) ^ (m ^ 2)) ∣ (Nat.card ↥O : ℤ) := by
      rw [hcard]
      exact Dvd.intro (2 * ∏ i ∈ Finset.Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1)) (by ring)
    have hdvd : Nat.card K ^ (m ^ 2) ∣ Nat.card ↥O := by
      rw [← Int.natCast_dvd_natCast]
      push_cast
      exact hdvdZ
    rw [hN] at hdvd
    refine odd_case_contra hq3 hqo ?_ hdvd hW
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ m ^ 2 := Nat.pow_le_pow_left hm3 2


end M

end M

section A

open CFSG.RankThree.Classical2 CFSG.HardMathSupport.Solomon.Coordinator.LieComp

namespace A


private theorem ringChar_eq_of_card {E : Type} [Field E] [Fintype E] {a b : ℕ} (ha : a.Prime)
    (h : Fintype.card E = a ^ b) : ringChar E = a := by
  haveI : Fact a.Prime := ⟨ha⟩
  haveI : CharP E a := charP_of_card_eq_prime_pow h
  exact ringChar.eq E a

section Cases

variable {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem ringChar_ne_two_of_finrank_odd (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Odd (Module.finrank K V)) : ringChar K ≠ 2 := by
  intro h
  haveI : CharP K 2 := ringChar.of_eq h
  have := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  exact (Nat.not_even_iff_odd.mpr hd) this

private theorem cover_of_phi {p d q : ℕ} {L : Subgroup ↥(orthDerived Q)}
    (hL : CFSG.IsQuasisimple ↥L) {S : Type} [Group S] [Finite S]
    (hS : LieFactorData p S) (hSq : CFSG.IsQuasisimple S) (hfac : OrthFactorOver p q S)
    (hA6 : Nonempty ((S ⧸ Subgroup.center S) ≃* alternatingGroup (Fin 6)) → p = 3 ∧ d ≤ 4)
    (φ : S →* ↥(TauCeti.QuadraticMap.orthogonalGroup Q))
    (h : φ.range = L.map (OmegaAux.ιO Q)) : OmegaAux.Cover p d q L := by
  obtain ⟨ψ, hψ⟩ := OmegaAux.exists_lift_of_range_eq φ L h
  exact OmegaAux.cover_of_range hL hS hSq hfac hA6 ψ hψ

private theorem range_comp_symm {G H S : Type*} [Group G] [Group H] [Group S] (e : G ≃* H)
    (f : S →* H) :
    (e.symm.toMonoidHom.comp f).range = f.range.map e.symm.toMonoidHom :=
  MonoidHom.range_comp _ _

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonal CFSG.LocalAnalysis.ComponentInitial in
private theorem case_three (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 3) (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal)
    (hL : CFSG.IsQuasisimple ↥L) :
    OmegaAux.Cover (ringChar K) (Module.finrank K V) (Nat.card K) L := by
  have h2 : ringChar K ≠ 2 := ringChar_ne_two_of_finrank_odd hQ (by rw [hd]; decide)
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  by_cases hK3 : Nat.card K = 3
  · have := ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_three_p_components_frontier
      hodd Q hQ hd).2 hK3).1
    exact (not_isComponent_of_isSolvable hM).elim
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_three_derived hodd hK3 Q hQ hd
  have hMeq := eq_commutator_of_isComponent hq hM
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have h4 : 4 ≤ Fintype.card K := by rw [← Nat.card_eq_fintype_card]; omega
  refine cover_of_phi hL (slFactorFacts_holds K 2 le_rfl (fun _ => h4))
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2) (Or.inr hK3))
    (orthFactorOver_sl (ℓ := ringChar K) (q := Nat.card K) (E := K) (m := 2) (j := 1)
      le_rfl le_rfl rfl (by rw [pow_one, Nat.card_eq_fintype_card]) (fun _ => h4)
      (MulEquiv.refl _))
    (fun ⟨e⟩ => ?_)
    (e'.symm.toMonoidHom.comp (traceZeroOrthogonalAction.comp
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* _))) ?_
  · obtain ⟨-, h9⟩ := slAltSixFacts_holds K 2 le_rfl ⟨e⟩
    exact ⟨ringChar_eq_of_card (by norm_num : Nat.Prime 3) (b := 2) (by rw [h9]; norm_num),
      by omega⟩
  · rw [range_comp_symm]
    exact (hMeq.trans hcomm).symm

private theorem isSolvable_orthogonalGroup_of_smallFixedException (R : QuadraticForm K V)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (h3 : 3 ≤ Module.finrank K V)
    (hS : CFSG.RankThree.PartOne.KCOrthogonal.SmallFixedException R) :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hno := (CFSG.RankThree.PartOne.KCOrthogonal.orthogonal_regular_space_coverage R hR h3).1 hS
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  have hsub : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R)).primeFactors ⊆ {2, 3} := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hdvd : r ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
      Nat.dvd_of_mem_primeFactors hr
    haveI : Fact r.Prime := ⟨hrp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hdvd
    by_contra hne
    have h3r : 3 < r := by
      have h2 := hrp.two_le
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
      omega
    exact hno g r hrp h3r hg
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial in
private theorem case_four_split (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 4)
    (hS : ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    OmegaAux.Cover (ringChar K) (Module.finrank K V) (Nat.card K) L := by
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  by_cases hK : Nat.card K = 2 ∨ Nat.card K = 3
  · haveI := isSolvable_orthogonalGroup_of_smallFixedException Q hQ (by omega)
      (Or.inr ⟨⟨hd, hS⟩, hK⟩)
    exact (not_isComponent_of_isSolvable hM).elim
  push Not at hK
  obtain ⟨hK2, hK3⟩ := hK
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := inferInstance
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, -, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hd hS
  have hMD : L.map (OmegaAux.ιO Q) ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [← OmegaAux.range_ιO]
    exact Subgroup.map_le_range _ _
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have h4 : 4 ≤ Fintype.card K := by rw [← Nat.card_eq_fintype_card]; omega
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  have hA6 : Nonempty ((Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) ≃* alternatingGroup (Fin 6)) →
      ringChar K = 3 ∧ Module.finrank K V ≤ 4 := fun ⟨e⟩ => by
    obtain ⟨-, h9⟩ := slAltSixFacts_holds K 2 le_rfl ⟨e⟩
    exact ⟨ringChar_eq_of_card (by norm_num : Nat.Prime 3) (b := 2) (by rw [h9]; norm_num),
      by omega⟩
  rcases CatLeafProof.eq_or_eq_of_isComponent_le_sup hsup hq₁ hq₂ hn₁ hn₂ hM hMD with h | h
  · refine cover_of_phi hL (slFactorFacts_holds K 2 le_rfl (fun _ => h4)) hSL
      (orthFactorOver_sl (ℓ := ringChar K) (q := Nat.card K) (E := K) (m := 2) (j := 1)
        le_rfl le_rfl rfl (by rw [pow_one, Nat.card_eq_fintype_card]) (fun _ => h4)
        (MulEquiv.refl _)) hA6
      (e'.symm.toMonoidHom.comp ((specialRho (K := K)).comp (MonoidHom.inl _ _))) ?_
    rw [range_comp_symm]
    exact h.symm
  · refine cover_of_phi hL (slFactorFacts_holds K 2 le_rfl (fun _ => h4)) hSL
      (orthFactorOver_sl (ℓ := ringChar K) (q := Nat.card K) (E := K) (m := 2) (j := 1)
        le_rfl le_rfl rfl (by rw [pow_one, Nat.card_eq_fintype_card]) (fun _ => h4)
        (MulEquiv.refl _)) hA6
      (e'.symm.toMonoidHom.comp ((specialRho (K := K)).comp (MonoidHom.inr _ _))) ?_
    rw [range_comp_symm]
    exact h.symm

private theorem ringChar_eq_of_algebra {F E : Type} [Field F] [Field E] [Algebra F E] :
    ringChar E = ringChar F := by
  haveI : CharP E (ringChar F) :=
    charP_of_injective_algebraMap (algebraMap F E).injective (ringChar F)
  exact ringChar.eq E (ringChar F)

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
  CFSG.LocalAnalysis.ComponentInitial in
private theorem case_four_nonsplit_odd (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 4) (h2 : ringChar K ≠ 2)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    OmegaAux.Cover (ringChar K) (Module.finrank K V) (Nat.card K) L := by
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have h2' := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  obtain ⟨δ, hns, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_four_derived hodd Q hQ hd hno
  have : Fact (¬ IsSquare (δ : K)) := ⟨hns⟩
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  letI : Fintype (extension (δ : K)) := Fintype.ofFinite _
  have hMeq := eq_commutator_of_isComponent hq hM
  have hcard := extension_card (δ : K)
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hE2 : Nat.card (extension (δ : K)) ≠ 2 := by
    rw [hcard]
    nlinarith
  have hE3 : Nat.card (extension (δ : K)) ≠ 3 := by
    rw [hcard]
    nlinarith
  have hE4 : 4 ≤ Fintype.card (extension (δ : K)) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    nlinarith
  have hchar : ringChar (extension (δ : K)) = ringChar K := ringChar_eq_of_algebra
  have hS : LieFactorData (ringChar K) (Matrix.SpecialLinearGroup (Fin 2) (extension (δ : K))) :=
    hchar ▸ slFactorFacts_holds (extension (δ : K)) 2 le_rfl (fun _ => hE4)
  refine cover_of_phi hL hS
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 (extension (δ : K)) le_rfl
      (Or.inr hE2) (Or.inr hE3))
    (orthFactorOver_sl (ℓ := ringChar K) (q := Nat.card K) (E := extension (δ : K)) (m := 2)
      (j := 2) le_rfl (by norm_num) hchar
      (by rw [← Nat.card_eq_fintype_card]; exact hcard) (fun _ => hE4) (MulEquiv.refl _))
    (fun ⟨e⟩ => ?_)
    (e'.symm.toMonoidHom.comp (specialRho (δ : K) h2')) ?_
  · obtain ⟨-, h9⟩ := slAltSixFacts_holds (extension (δ : K)) 2 le_rfl ⟨e⟩
    have hK : Fintype.card K = 3 := by
      rw [← Nat.card_eq_fintype_card]
      have : Nat.card K ^ 2 = 3 ^ 2 := by
        rw [← hcard, Nat.card_eq_fintype_card, h9]
        norm_num
      exact Nat.pow_left_injective two_ne_zero this
    exact ⟨ringChar_eq_of_card (by norm_num : Nat.Prime 3) (b := 1) (by rw [hK]; norm_num),
      by omega⟩
  · rw [range_comp_symm]
    exact (hMeq.trans hcomm).symm

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalFive CFSG.LocalAnalysis.ComponentInitial in
private theorem case_five (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 5) (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal)
    (hL : CFSG.IsQuasisimple ↥L) :
    OmegaAux.Cover (ringChar K) (Module.finrank K V) (Nat.card K) L := by
  have h2 : ringChar K ≠ 2 := ringChar_ne_two_of_finrank_odd hQ (by rw [hd]; decide)
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have h2' := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_five_derived hodd Q hQ hd
  have hMeq := eq_commutator_of_isComponent hq hM
  let eSp : (symplecticMultiplier (K := K)).ker ≃* ↥(CFSG.Open.StatedSp 2 K) :=
    symplecticKernelEquivFin.trans (CFSG.LieType.Universal.Symplectic.equivStatedSp 2 K)
  have hne : (2, Fintype.card K) ≠ (2, 2) := fun h => by
    have h' : Fintype.card K = 2 := (Prod.mk.inj h).2
    rw [← Nat.card_eq_fintype_card] at h'
    exact absurd (h' ▸ hodd) (by decide)
  have hSq : CFSG.IsQuasisimple ↥(CFSG.Open.StatedSp 2 K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eSp (symplecticKernel_quasisimple hodd)
  refine cover_of_phi hL (spFactorFacts_holds K 2 le_rfl hne) hSq
    (orthFactorOver_sp (ℓ := ringChar K) (q := Nat.card K) (K' := K) rfl rfl (s := 2) le_rfl
      (by simpa [Nat.card_eq_fintype_card] using hne) (MulEquiv.refl _))
    (fun ⟨e⟩ => ((spAltSixFacts_holds K 2 le_rfl hne).false e).elim)
    (e'.symm.toMonoidHom.comp ((selfAdjointSymplecticAction h2').comp eSp.symm.toMonoidHom)) ?_
  rw [range_comp_symm, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eSp.symm.surjective,
    ← MonoidHom.range_eq_map]
  exact (hMeq.trans hcomm).symm

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
  CFSG.ComponentClassification.CatalogueBOrthogonalSix CFSG.LocalAnalysis.ComponentInitial in
private theorem case_six_nonsplit_odd (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 6) (h2 : ringChar K ≠ 2)
    (hno : ¬ ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    OmegaAux.Cover (ringChar K) (Module.finrank K V) (Nat.card K) L := by
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have h2' := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  obtain ⟨δ, hfact, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_six_derived hodd Q hQ hd hno
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  letI : Fintype (extension (δ : K)) := Fintype.ofFinite _
  have hMeq := eq_commutator_of_isComponent hq hM
  obtain ⟨eU⟩ := exists_six_special_unitary_equiv (δ : K) h2'
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have he : 1 ≤ (n : ℕ) := n.pos
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hcardE : Nat.card (extension (δ : K)) = ringChar K ^ (2 * (n : ℕ)) := by
    rw [extension_card, hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData (ringChar K) (n : ℕ) (extension (δ : K)) := ⟨hp, he, hcardE⟩
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have : CharP (extension (δ : K)) (ringChar K) := hU.charP
  have hF : Nat.card (extension (δ : K)) = (ringChar K ^ (n : ℕ)) ^ 2 := by
    rw [hcardE, ← pow_mul, mul_comm]
  have hσ2 : (conjugation (δ : K)).toRingEquiv * (conjugation (δ : K)).toRingEquiv = 1 := by
    rw [← pow_two]
    exact conjugation_square (δ : K)
  have hconj : (conjugation (δ : K)).toRingEquiv =
      CFSG.LieType.BorelTits.unitaryInvolution (extension (δ : K)) (ringChar K) (n : ℕ) := by
    rcases UnitaryHigher.ringEquiv_eq_refl_or_bar hU hσ2 with h | h
    · exact absurd h (conjugation_ne_one (δ : K) h2')
    · exact RingEquiv.ext fun c =>
        (h c).trans (CFSG.LieType.BorelTits.unitaryInvolution_apply _ (ringChar K) (n : ℕ) c).symm
  have hSU : CFSG.LieType.Universal.Unitary.SUid (conjugation (δ : K)).toRingEquiv 4 =
      CFSG.Open.StatedSU 4 (ringChar K ^ (n : ℕ)) (extension (δ : K)) := by
    rw [hconj]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4
  have hq2 : 2 ≤ ringChar K ^ (n : ℕ) := hp.two_le.trans (Nat.le_self_pow (by omega) _)
  have hnq : ((4 : ℕ), ringChar K ^ (n : ℕ)) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  have hFc : Fintype.card (extension (δ : K)) = (ringChar K ^ (n : ℕ)) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  obtain ⟨hSq, -⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF
    (by norm_num) hnq
  let eSU := eU.trans (MulEquiv.subgroupCongr hSU)
  have hchar : ringChar (extension (δ : K)) = ringChar K := ringChar_eq_of_algebra
  have hS : LieFactorData (ringChar K)
      ↥(CFSG.Open.StatedSU 4 (ringChar K ^ (n : ℕ)) (extension (δ : K))) :=
    hchar ▸ suFactorFacts_holds (extension (δ : K)) 4 (ringChar K ^ (n : ℕ)) hFc
      (by norm_num) hnq
  refine cover_of_phi hL hS hSq
    (orthFactorOver_su (ℓ := ringChar K) (q := Nat.card K) (E := extension (δ : K)) (m := 4)
      (j := 1) (q' := ringChar K ^ (n : ℕ)) (by norm_num) le_rfl hchar
      (by rw [pow_one, ← hK]) hFc hnq (MulEquiv.refl _))
    (fun ⟨e⟩ => ((suAltSixFacts_holds (extension (δ : K)) 4 (ringChar K ^ (n : ℕ)) hFc
      (by norm_num)).false e).elim)
    (e'.symm.toMonoidHom.comp ((sixSpecialKappa (δ : K) h2').comp eSU.symm.toMonoidHom)) ?_
  rw [range_comp_symm, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eSU.symm.surjective,
    ← MonoidHom.range_eq_map]
  exact (hMeq.trans hcomm).symm

open CFSG.ComponentClassification.CatLeafProof.KleinSix CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin in
private theorem rhoGL_range_eq_orthDerived (h2 : (2 : K) ≠ 0) :
    (rhoGL (K := K)).range = orthDerived (quadPlus 3 K) := by
  rw [range_eq_elementaryGroup h2]
  show _ = ⁅_, _⁆
  rw [← Subgroup.map_subtype_commutator]
  exact (CFSG.ComponentClassification.CatalogueBOrthogonal.derived_map_eq_elementary _ h2
    quadPlus_nondegenerate finrank_singularT.ge singularT_singular).symm

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatLeafProof.KleinSix CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin in
private theorem case_six_split_odd (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 6) (h2 : ringChar K ≠ 2)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    OmegaAux.Cover (ringChar K) (Module.finrank K V) (Nat.card K) L := by
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have h2' := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hqs : CFSG.IsQuasisimple ↥(orthDerived Q) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hQ hT
  have hLtop : L = ⊤ := OmegaAux.eq_top_of_isQuasisimple hqs hLn hL
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.K159.Klein.exists_isometry_quadPlus_three Q hQ hd hT
  let e1 := CFSG.RankThree.PartOne.orthDerivedEquiv e
  have hrange := rhoGL_range_eq_orthDerived (K := K) h2'
  let ρ' : Matrix.SpecialLinearGroup (Fin 4) K →* ↥(orthDerived (quadPlus 3 K)) :=
    (rhoGL (K := K)).codRestrict _ (fun g => by rw [← hrange]; exact ⟨g, rfl⟩)
  have hρ' : Function.Surjective ρ' := by
    intro y
    have : (y : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) ∈ (rhoGL (K := K)).range := by
      rw [hrange]
      exact y.2
    obtain ⟨g, hg⟩ := this
    exact ⟨g, Subtype.ext hg⟩
  let ψ : Matrix.SpecialLinearGroup (Fin 4) K →* ↥(orthDerived Q) := e1.symm.toMonoidHom.comp ρ'
  have hψ : ψ.range = L := by
    rw [hLtop]
    exact MonoidHom.range_eq_top.mpr (e1.symm.surjective.comp hρ')
  have hS4 := CatalogueBGeneralLinear.specialLinear_quasisimple 4 K (by norm_num)
    (Or.inl (by norm_num)) (Or.inl (by norm_num))
  exact OmegaAux.cover_of_range hL
    (slFactorFacts_holds K 4 (by norm_num) (fun h => absurd h (by norm_num))) hS4
    (orthFactorOver_sl (ℓ := ringChar K) (q := Nat.card K) (E := K) (m := 4) (j := 1)
      (by norm_num) le_rfl rfl (by rw [pow_one, Nat.card_eq_fintype_card])
      (fun h => absurd h (by norm_num)) (MulEquiv.refl _))
    (fun ⟨e⟩ => absurd (slAltSixFacts_holds K 4 (by norm_num) ⟨e⟩).1 (by norm_num)) ψ hψ

end Cases


end A

end A

section B

open CFSG.RankThree.Classical2 CFSG.HardMathSupport.Solomon.Coordinator.LieComp

namespace B


open Matrix CFSG.LocalAnalysis CFSG.LieType.Universal.Spin CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.K159.Klein in
private theorem klein_commutator_orthogonal_six_of_charTwo {K : Type} [Field K] [Finite K]
    [CharP K 2]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Q : QuadraticForm K W) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K W = 6)
    (hts : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Nonempty (commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≃* CFSG.Open.StatedSL 4 K) := by
  obtain ⟨e⟩ := exists_isometry_quadPlus_three Q hQ hd hts
  obtain ⟨hs, hp⟩ := sl4_isSimpleGroup_and_perfect (K := K)
  have hρinj := transportHom_injective e
    (CFSG.RankThree.PartOne.K159.Klein.rho : SpecialLinearGroup (Fin 4) K →* _) rho_injective
  have hρmem := transportHom_mem e
    (CFSG.RankThree.PartOne.K159.Klein.rho : SpecialLinearGroup (Fin 4) K →* _) rho_mem
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set ρ := transportHom e
    (CFSG.RankThree.PartOne.K159.Klein.rho : SpecialLinearGroup (Fin 4) K →* _) with hρ
  have hle : ρ.range ≤ O := by
    rintro _ ⟨g, rfl⟩
    exact hρmem g
  have hcard : Nat.card O = 2 * Nat.card (SpecialLinearGroup (Fin 4) K) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e,
      card_orthogonalGroup_quadPlus_three]
  obtain ⟨-, -, -, -, -, -, hcomm, -⟩ := derived_of_index_two_model O ρ hρinj hle hcard
  have h1 : (commutator ↥O).map O.subtype = ρ.range := by
    rw [Subgroup.map_subtype_commutator, hcomm]
  let e1 : commutator ↥O ≃* ρ.range :=
    (Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr h1)
  let e2 : ρ.range ≃* SpecialLinearGroup (Fin 4) K := (MonoidHom.ofInjective hρinj).symm
  exact ⟨e1.trans (e2.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K))⟩

section Cases

variable {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem cover_of_orthDerived_mulEquiv {p d q : ℕ} {S : Type} [Group S] [Finite S]
    (e : S ≃* ↥(orthDerived Q)) (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal)
    (hL : CFSG.IsQuasisimple ↥L) (hS : LieFactorData p S) (hSq : CFSG.IsQuasisimple S)
    (hfac : OrthFactorOver p q S)
    (hA6 : Nonempty ((S ⧸ Subgroup.center S) ≃* alternatingGroup (Fin 6)) → p = 3 ∧ d ≤ 4) :
    Cover p d q L := by
  have hqs : CFSG.IsQuasisimple ↥(orthDerived Q) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hSq
  have hLtop : L = ⊤ := eq_top_of_isQuasisimple hqs hLn hL
  refine cover_of_range hL hS hSq hfac hA6 e.toMonoidHom ?_
  rw [hLtop]
  exact MonoidHom.range_eq_top.mpr e.surjective

private theorem case_four_nonsplit_even (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 4) (h2 : ringChar K = 2)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    Cover (ringChar K) (Module.finrank K V) (Nat.card K) L := by
  haveI : CharP K 2 := ringChar.of_eq h2
  have hts : ∀ U : Submodule K V, Module.finrank K U = 2 → ∃ u ∈ U, Q u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hno ⟨U, hU, hcon⟩
  obtain ⟨E, _, _, _, hE, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.K159.exists_orthDerived_four_sl2 Q hQ hd hts
  haveI : Fintype E := Fintype.ofFinite E
  have hK2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hE4 : 4 ≤ Nat.card E := by
    rw [hE]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hK2 2
  have hEc : Fintype.card E = Nat.card E := Nat.card_eq_fintype_card.symm
  have hchar : ringChar E = ringChar K := by
    rw [h2]
    exact ringChar.eq E 2
  have hS : LieFactorData (ringChar K) (Matrix.SpecialLinearGroup (Fin 2) E) := by
    rw [← hchar]
    exact slFactorFacts_holds E 2 le_rfl (fun _ => by omega)
  have hSq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) E) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 E le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  refine cover_of_orthDerived_mulEquiv e.symm L hLn hL hS hSq
    (orthFactorOver_sl (ℓ := ringChar K) (q := Nat.card K) (E := E) (m := 2) (j := 2)
      le_rfl (by norm_num) hchar (by rw [← Nat.card_eq_fintype_card]; exact hE)
      (fun _ => by rw [← Nat.card_eq_fintype_card]; exact hE4) (MulEquiv.refl _)) ?_
  rintro ⟨e6⟩
  obtain ⟨-, h9⟩ := slAltSixFacts_holds E 2 le_rfl ⟨e6⟩
  have hev : Fintype.card E % 2 = 0 := FiniteField.even_card_iff_char_two.1 (hchar.trans h2)
  rw [h9] at hev
  exact absurd hev (by decide)

private theorem case_six_split_even (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 6) (h2 : ringChar K = 2)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    Cover (ringChar K) (Module.finrank K V) (Nat.card K) L := by
  haveI : CharP K 2 := ringChar.of_eq h2
  obtain ⟨κ⟩ := klein_commutator_orthogonal_six_of_charTwo Q hQ hd hT
  let e : ↥(orthDerived Q) ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
    ((CFSG.RankThree.PartOne.orthDerivedEquivCommutator Q).symm.trans κ).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).symm
  have hS : LieFactorData (ringChar K) (Matrix.SpecialLinearGroup (Fin 4) K) :=
    slFactorFacts_holds K 4 (by norm_num) (fun h => absurd h (by norm_num))
  have hSq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 4) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 4 K
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  refine cover_of_orthDerived_mulEquiv e.symm L hLn hL hS hSq
    (orthFactorOver_sl (ℓ := ringChar K) (q := Nat.card K) (E := K) (m := 4) (j := 1)
      (by norm_num) le_rfl rfl (by rw [pow_one, Nat.card_eq_fintype_card])
      (fun h => absurd h (by norm_num)) (MulEquiv.refl _)) ?_
  rintro ⟨e6⟩
  obtain ⟨h4, -⟩ := slAltSixFacts_holds K 4 (by norm_num) ⟨e6⟩
  exact absurd h4 (by norm_num)

private theorem case_six_nonsplit_even (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 6) (h2 : ringChar K = 2)
    (hno : ¬ ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    Cover (ringChar K) (Module.finrank K V) (Nat.card K) L := by
  haveI : CharP K 2 := ringChar.of_eq h2
  have hts : ∀ U : Submodule K V, Module.finrank K U = 3 → ∃ u ∈ U, Q u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hno ⟨U, hU, hcon⟩
  obtain ⟨E, _, _, D, ψ, hψ⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.exists_evenMinus_model Q hQ (n := 3) (by norm_num)
      (by omega) hts
  haveI : CharP E 2 := CFSG.RankThree.PartOne.KCOrthogonal.charP_two_of_algebra (K := K)
  haveI := D.finite_E
  haveI : Fintype E := Fintype.ofFinite E
  let e1 : Q.IsometryEquiv (CFSG.RankThree.PartOne.KCOrthogonal.evenNormTailForm D.N 2) :=
    { toLinearEquiv := ψ
      map_app' := fun w => hψ w }
  let e2 : Q.IsometryEquiv D.sixForm := e1.trans D.sixIsometry
  obtain ⟨-, -, -, -, -, -, -, -, hinj, -, -, -, -, -, -, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_unitary_derived_model D
  have hrange : orthDerived D.sixForm = D.sixRho.range := hcomm
  let e3 : D.sixSU ≃* ↥(orthDerived D.sixForm) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
  obtain ⟨f, hU, hcard, hbar⟩ := D.exists_unitaryFieldData
  obtain ⟨e4⟩ := D.nonempty_sixSU_mulEquiv hU hbar
  let e5 : CFSG.Open.StatedSU 4 (2 ^ f) E ≃* ↥(orthDerived Q) :=
    e4.symm.trans (e3.trans (CFSG.RankThree.PartOne.orthDerivedEquiv e2).symm)
  haveI := finite_orthDerived Q
  haveI : Finite ↥(CFSG.Open.StatedSU 4 (2 ^ f) E) := Finite.of_equiv _ e5.toEquiv.symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNat : Nat.card E = (2 ^ f) ^ 2 := by rw [D.card_E, hcard]
  have hF : Fintype.card E = (2 ^ f) ^ 2 := by rw [Nat.card_eq_fintype_card] at hNat; exact hNat
  have hnq : ((4 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro hh
    have := congrArg Prod.fst hh
    simp at this
  have hchar : ringChar E = ringChar K := by
    rw [h2]
    exact ringChar.eq E 2
  have hS : LieFactorData (ringChar K) ↥(CFSG.Open.StatedSU 4 (2 ^ f) E) := by
    rw [← hchar]
    exact suFactorFacts_holds E 4 (2 ^ f) hF (by norm_num) hnq
  have hSq : CFSG.IsQuasisimple ↥(CFSG.Open.StatedSU 4 (2 ^ f) E) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hNat (by norm_num) hnq).1
  have hKf : Nat.card K = 2 ^ f := by
    have h1 : (2 ^ f) ^ 2 = Nat.card K ^ 2 := by rw [← hNat, D.card_E]
    exact (Nat.pow_left_injective (by norm_num) h1).symm
  refine cover_of_orthDerived_mulEquiv e5 L hLn hL hS hSq
    (orthFactorOver_su (ℓ := ringChar K) (q := Nat.card K) (E := E) (m := 4) (j := 1)
      (q' := 2 ^ f) (by norm_num) le_rfl hchar (by rw [pow_one, ← hKf]) hF hnq
      (MulEquiv.refl _)) ?_
  rintro ⟨e6⟩
  exact ((suAltSixFacts_holds E 4 (2 ^ f) hF (by norm_num)).false e6).elim

end Cases


end B

end B

section Assembly

variable {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem case_large (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : 7 ≤ Module.finrank K V) (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal)
    (hL : CFSG.IsQuasisimple ↥L) : Cover (ringChar K) (Module.finrank K V) (Nat.card K) L := by
  obtain ⟨T, hT3, hT⟩ := C.large_exists_singular hQ hd
  have hqs : CFSG.IsQuasisimple ↥(orthDerived Q) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hQ ⟨T, hT3, hT⟩
  have hLtop : L = ⊤ := eq_top_of_isQuasisimple hqs hLn hL
  haveI := finite_orthDerived Q
  have hfd : LieFactorData (ringChar K) ↥(orthDerived Q) :=
    ⟨hqs.1.commutator_eq_top, C.large_chev hQ hd, fun ⟨e⟩ =>
      ((M.large_no_a6 hQ hd).false e).elim⟩
  exact cover_of_range hL hfd hqs
    (orthFactorOver_orth (ℓ := ringChar K) (q := Nat.card K) (K' := K) rfl rfl hQ hd
      ⟨T, hT3, hT⟩ (MulEquiv.refl _))
    (fun ⟨e⟩ => ((M.large_no_a6 hQ hd).false e).elim)
    (MonoidHom.id _) (by rw [MonoidHom.range_eq_top.mpr Function.surjective_id]; exact hLtop.symm)

private theorem omega_cover (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    Cover (ringChar K) (Module.finrank K V) (Nat.card K) L := by
  by_cases h2 : Module.finrank K V ≤ 2
  · exact (M.case_le_two hQ h2 L hL).elim
  by_cases h3 : Module.finrank K V = 3
  · exact A.case_three hQ h3 L hLn hL
  by_cases h4 : Module.finrank K V = 4
  · by_cases hS : ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
    · exact A.case_four_split hQ h4 hS L hLn hL
    · by_cases h2 : ringChar K = 2
      · exact B.case_four_nonsplit_even hQ h4 h2 hS L hLn hL
      · exact A.case_four_nonsplit_odd hQ h4 h2 hS L hLn hL
  by_cases h5 : Module.finrank K V = 5
  · exact A.case_five hQ h5 L hLn hL
  by_cases h6 : Module.finrank K V = 6
  · by_cases hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
    · by_cases h2 : ringChar K = 2
      · exact B.case_six_split_even hQ h6 h2 hT L hLn hL
      · exact A.case_six_split_odd hQ h6 h2 hT L hLn hL
    · by_cases h2 : ringChar K = 2
      · exact B.case_six_nonsplit_even hQ h6 h2 hT L hLn hL
      · exact A.case_six_nonsplit_odd hQ h6 h2 hT L hLn hL
  exact case_large hQ (by omega) L hLn hL


end Assembly

end OmegaAux

theorem omegaAltSixFacts_holds : OmegaAltSixFacts :=
  fun _ _ _ _ _ _ _ _ hQ L hLn hL ⟨e⟩ => (OmegaAux.omega_cover hQ L hLn hL).a6 ⟨e⟩

theorem omegaFactorField_holds : OmegaFactorField := by
  intro K _ _ V _ _ _ Q hQ L hLn hL
  obtain ⟨X, hXg, hXf, hLie, hfac, f, hf, hk⟩ := (OmegaAux.omega_cover hQ L hLn hL).fact
  exact ⟨X, hXg, hXf, hLie, hfac, f, hf, hk⟩

theorem omegaFactorFacts_holds : OmegaFactorFacts := by
  intro K _ _ V _ _ _ Q hQ L hLn hL
  obtain ⟨X, hXg, hXf, hLie, -, f, hf, hk⟩ := (OmegaAux.omega_cover hQ L hLn hL).fact
  exact ⟨X, hXg, hXf, hLie, f, hf, hk⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
