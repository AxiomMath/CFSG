module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTools
public import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank

theorem outerCoreTrivAt_triality_field
    {ℓ a : ℕ} (hℓ : ℓ.Prime) (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ (3 * a * 2)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ (a * 2))
    (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ ℓ ^ (3 * a)) :
    OuterCoreTrivAt (fieldActor (t := TwistTag.D4) σ δ) := by
  obtain ⟨hord, -, -, -, -, hJC, hfixJ, hsimple, hnab, -, -, -, -, hker, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel
      hℓ ha (le_refl 2) (by norm_num : Nat.Coprime 2 3) K hK σ hσ δ hδ
  have hZ : center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hF : (fieldActor (t := TwistTag.D4) σ δ).toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
        (trialityFieldImage σ δ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [← Subgroup.comap_map_eq_self_of_injective
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective
      ((fieldActor (t := TwistTag.D4) σ δ).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))), hfixJ]
    rfl
  have hfix : ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      fieldActor (t := TwistTag.D4) σ δ s = s ↔
        s ∈ (trialityFieldImage σ δ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    fun s => by
      rw [← hF]
      exact Iff.rfl
  have eJ : (trialityFieldImage σ δ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃*
      trialityFieldImage σ δ := Subgroup.subgroupOfEquivOfLe hJC
  have hJs : IsSimpleGroup
      ((trialityFieldImage σ δ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    (MulEquiv.isSimpleGroup_congr eJ).2 hsimple
  have hJna : ∃ x y : (trialityFieldImage σ δ).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hnab
    intro x y
    apply eJ.symm.injective
    rw [map_mul, map_mul, hcon]
  have h2 : fieldActor (t := TwistTag.D4) σ δ ^ 2 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  intro R hRodd hRi hRc r hr
  have hr1 : r ∈ centralizer {fieldActor (t := TwistTag.D4) σ δ} :=
    mem_centralizer_singleton_iff.2 (hRi r hr)
  have hr2 : r ∈ centralizer (trialityFieldInner σ δ :
      Set (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    have hrj : r j = j := fix_of_fixed_simple hZ hRodd hRi hRc hfix hJs hJna hr hj
    have h1 := conj_apply_eq r j
    rw [hrj] at h1
    calc MulAut.conj j * r = r * MulAut.conj j * r⁻¹ * r := by rw [← h1]
      _ = r * MulAut.conj j := by group
  have hz : r ∈ zpowers (fieldActor (t := TwistTag.D4) σ δ) := by
    rw [← hker]
    exact mem_inf.2 ⟨hr1, hr2⟩
  exact eq_one_of_odd_of_mem_zpowers h2 hz (odd_orderOf_of_mem hRodd hr)

theorem outerCoreAt_triality
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hinn : ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, g ^ 2 = 1 → g ≠ 1 →
      OuterCoreAt (MulAut.conj g))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα : orderOf α = 2) :
    OuterCoreAt α := by
  classical
  have hα2 : α ^ 2 = 1 := sq_eq_one_of_orderOf hα
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, -, hinv⟩, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF α
  change α = MulAut.conj g * fieldActor σ δ at hgδ
  by_cases hδ : δ = 1
  ·
    subst hδ
    rw [fieldActor_one, mul_one] at hgδ
    subst hgδ
    have hg2 : g ^ 2 = 1 :=
      mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hα2, map_one])
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [map_one, orderOf_one] at hα
      exact absurd hα (by norm_num)
    exact hinn g hg2 hg1
  ·
    have hΘα : Θ α = δ := hΘ α g δ hgδ
    obtain ⟨⟨a, ha⟩, hδc⟩ := (hinv α hα2).resolve_left (by rw [hΘα]; exact hδ)
    rw [hΘα] at hδc
    have hodd : Odd (p ^ a) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    have hK6 : Nat.card K = (p ^ a) ^ 6 := by
      rw [hK, ha, ← pow_mul, ← pow_mul]
      ring_nf
    have hσr : ∀ c, σ c = c ^ ((p ^ a) ^ 2) := fun c => by
      rw [hσ, ha, ← pow_mul]
      ring_nf
    have hδr : ∀ c, δ c = c ^ ((p ^ a) ^ 3) := fun c => by
      rw [hδc, ha, ← pow_mul, show 3 * (a + a) / 2 = a * 3 by omega]
    subst hgδ
    obtain ⟨-, ⟨ψ, hψ⟩, -⟩ := odd_triality_field_coset_involution_fixed_p_components
      (hp.isPrimePow.pow (by omega)) hodd K hK6 σ hσr δ hδr g hα2
    have hK6' : Nat.card K = p ^ (3 * a * 2) := by
      rw [hK6, ← pow_mul]
      ring_nf
    have hσ' : ∀ c, σ c = c ^ p ^ (a * 2) := fun c => by rw [hσr, ← pow_mul]
    have hδ' : ∀ c, δ c = c ^ p ^ (3 * a) := fun c => by rw [hδr, ← pow_mul, mul_comm]
    exact outerCoreAt_of_conj hψ
      (outerCoreTrivAt_triality_field hp (by omega) hK6' σ hσ' δ hδ').outerCoreAt

@[expose] def TrialityInnerCoreInput :
    Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (p ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
      ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, g ^ 2 = 1 → g ≠ 1 →
        OuterCoreAt (MulAut.conj g)

theorem oddLieCoreFamilyInput_trialityD4
    (hinn : TrialityInnerCoreInput) : OddLieCoreFamilyInput .trialityD4 := by
  refine oddLieCoreFamilyInput_of_outerCoreAt fun S _ _ _ _ n p f hp hp2 _ hm i hi => ?_
  rcases hm with ⟨hcl, -⟩ | ⟨-, -, hY⟩ | ⟨-, hrt, -⟩ | ⟨-, hsz, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨⟨-, hf, -⟩, hm'⟩ := hY
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hm'
    refine outerCoreAt_of_congr e ?_
    exact outerCoreAt_triality hp hp2 hf hK σ hσ (hinn p f hp hp2 hf K hK σ hσ) _
      ((MulEquiv.orderOf_eq (MulAut.congr e) i).trans hi)
  · exact absurd hrt (by decide)
  · exact absurd hsz (by decide)

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
