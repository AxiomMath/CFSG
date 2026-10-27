module

public import CFSG.FeitThompson.Representations.OrientedSeparationFullCoreDadeSupports
public import CFSG.FeitThompson.Representations.BlockDifferencesSupportedOutsideCore
import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI
import CFSG.FeitThompson.Representations.CoherentJoiningOneBridge

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {L : Subgroup G} {A D : Set G} {R : G → Subgroup G}

section

variable {H U U₁ : Subgroup ↥L} [H.Normal] {η : (↥L → ℂ) → G → ℂ}

theorem existsUnique_dadeRoot [Finite G] (hD : IsDadeData L A R) (hodd : Odd (Nat.card ↥L))
    (hA : A = ambientCoreCentralizerSupport H) {χ : ↥L → ℂ}
    (hχ : χ ∈ irrDetect ℂ H) :
    ∃! ξ : G → ℂ, ξ ∈ Irr G ∧ star ξ ≠ ξ ∧ dadeMapFun L A R (χ - star χ) = ξ - star ξ := by
  subst hA
  have : Fintype G := Fintype.ofFinite G
  have : Fintype ↥L := Fintype.ofFinite ↥L
  exact (isAntirealIsometry_dadeMapFun hodd hD).existsUnique_root hχ

theorem dadeRoot_spec [Finite G] (hD : IsDadeData L A R) (hodd : Odd (Nat.card ↥L))
    (hA : A = ambientCoreCentralizerSupport H) {χ : ↥L → ℂ}
    (hχ : χ ∈ irrDetect ℂ H) :
    dadeRoot L A R χ ∈ Irr G ∧ star (dadeRoot L A R χ) ≠ dadeRoot L A R χ ∧
      dadeMapFun L A R (χ - star χ) = dadeRoot L A R χ - star (dadeRoot L A R χ) := by
  subst hA
  have : Fintype G := Fintype.ofFinite G
  have : Fintype ↥L := Fintype.ofFinite ↥L
  have hτ := isAntirealIsometry_dadeMapFun (H := H) hodd hD
  rw [dadeRoot_def]
  exact ⟨hτ.root_mem_Irr hχ, hτ.star_root_ne hχ, hτ.map_sub_star_eq hχ⟩

variable [Fintype G] [Fintype ↥L]

omit [Fintype G] in
theorem irrConstituentsFinset_eq_toFinset (θ : ↥L → ℂ) :
    irrConstituentsFinset θ = (finite_irrConstituents θ).toFinset := by
  ext χ
  simp [Set.Finite.mem_toFinset]

theorem isNormalInducedSignedFamily_dadeMapFun (hD : IsDadeData L A R)
    (hloc : IsFrobeniusTypeLocalData H U U₁) (hodd : Odd (Nat.card ↥L))
    (hA : A = ambientCoreCentralizerSupport H)
    (hη : ∀ χ ∈ irrDetect ℂ H, η χ ∈ Irr G ∧
      dadeMapFun L A R (χ - star χ) = η χ - star (η χ)) :
    IsNormalInducedSignedFamily H (dadeMapFun L A R) η where
  odd_natCard := hodd
  ne_bot := hloc.core_ne_bot
  isAntirealIsometry := by subst hA; exact isAntirealIsometry_dadeMapFun hodd hD
  eq_sum_irrConstituents := by
    intro θ hθ
    obtain ⟨lam, hlam, rfl⟩ := (mem_indFam H).1 hθ
    rw [irrConstituentsFinset_eq_toFinset]
    exact indClassFun_eq_sum_irrConstituents hloc hlam
  apply_one_eq := by
    intro θ hθ χ hχ ψ hψ
    obtain ⟨lam, hlam, rfl⟩ := (mem_indFam H).1 hθ
    rw [apply_one_of_mem_irrConstituents hloc hlam hχ,
      apply_one_of_mem_irrConstituents hloc hlam hψ]
  root_mem_Irr := fun _ hχ => (hη _ hχ).1
  map_sub_star_eq := fun _ hχ => (hη _ hχ).2

theorem dadeRoot_mem_Irr_and_map_sub_star_eq (hD : IsDadeData L A R) (hodd : Odd (Nat.card ↥L))
    (hA : A = ambientCoreCentralizerSupport H) :
    ∀ χ ∈ irrDetect ℂ H, dadeRoot L A R χ ∈ Irr G ∧
      dadeMapFun L A R (χ - star χ) = dadeRoot L A R χ - star (dadeRoot L A R χ) := by
  intro χ hχ
  obtain ⟨h1, -, h3⟩ := dadeRoot_spec hD hodd hA hχ
  exact ⟨h1, h3⟩

omit [Fintype G] in
theorem sub_mem_dadeDomain_of_mem_irrConstituents
    (hloc : IsFrobeniusTypeLocalData H U U₁)
    (hDdef : D = Subtype.val '' coreCentralizerSupportOutsideCore H)
    {θ : ↥L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr ↥H))
    {χ ψ : ↥L → ℂ} (hχ : χ ∈ irrConstituents θ) (hψ : ψ ∈ irrConstituents θ) :
    χ - ψ ∈ dadeDomain L D := by
  refine mem_dadeDomain.2 ⟨sub_mem (Irr_subset_classFun (mem_irrConstituents.1 hχ).1)
    (Irr_subset_classFun (mem_irrConstituents.1 hψ).1), fun x hx => ?_⟩
  rw [hDdef, Subtype.val_injective.mem_set_image] at hx
  by_contra hne
  exact hx (support_sub_subset_coreCentralizerSupportOutsideCore hloc hθ hχ hψ hne)

theorem cfInner_resClassFun_sub_eq_zero (hD : IsDadeData L A R)
    (hloc : IsFrobeniusTypeLocalData H U U₁) (hodd : Odd (Nat.card ↥L))
    (hA : A = ambientCoreCentralizerSupport H)
    (hDdef : D = Subtype.val '' coreCentralizerSupportOutsideCore H)
    (hstab : D.Nonempty → ∀ g : G, (fun x => g⁻¹ * x * g) '' D = D ↔ g ∈ L)
    (hdisj : D.Nonempty → ∀ g ∉ L, D ∩ (fun x => g⁻¹ * x * g) '' D = ∅)
    (hη : ∀ χ ∈ irrDetect ℂ H, η χ ∈ Irr G ∧
      dadeMapFun L A R (χ - star χ) = η χ - star (η χ))
    {Ψ : G → ℂ} (hΨ : Ψ ∈ classFun G)
    (horth : ∀ θ ∈ indFam H (nonprincipalIrr ↥H),
      ∀ ρ ∈ signedRootBlock η θ, IsOrthogonal Ψ ρ)
    {θ : ↥L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr ↥H))
    {χ ψ : ↥L → ℂ} (hχ : χ ∈ irrConstituents θ) (hψ : ψ ∈ irrConstituents θ) :
    cfInner (resClassFun L Ψ) (χ - ψ) = 0 := by
  by_cases hne : χ = ψ
  · rw [hne, sub_self, cfInner_zero_right]
  have hDne : D.Nonempty := by
    rw [hDdef]
    exact (coreCentralizerSupportOutsideCore_nonempty hloc hθ hχ hψ hne).image _
  have hDA : D ⊆ A := by
    rw [hDdef, hA]
    rintro x ⟨y, hy, rfl⟩
    exact mem_ambientCoreCentralizerSupport.2 (coreCentralizerSupportOutsideCore_subset H hy)
  have hmem : χ - ψ ∈ dadeDomain L D :=
    sub_mem_dadeDomain_of_mem_irrConstituents hloc hDdef hθ hχ hψ
  have hind : dadeMapFun L A R (χ - ψ) = indClassFun L (χ - ψ) := by
    rw [← coe_dadeMap hD ⟨χ - ψ, dadeDomain_mono hDA hmem⟩]
    exact dadeMap_eq_indClassFun_of_stabilizer_eq hD hDA hDne (hstab hDne)
      (fun g hg => hdisj hDne g hg) _ hmem
  have hspan := (isNormalInducedSignedFamily_dadeMapFun hD hloc hodd hA
    (U := U) (U₁ := U₁) hη).map_sub_mem_span_signedRootBlock hθ hχ hψ
  have h0 : cfInner Ψ (indClassFun L (χ - ψ)) = 0 := by
    rw [← hind]
    refine cfInner_eq_zero_of_mem_span_of_mem_span (A := {Ψ}) ?_
      (Submodule.mem_span_singleton_self _) hspan
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact isOrthogonal_iff.1 (horth θ hθ v (by simpa using hv))
  have h1 : cfInner (indClassFun L (χ - ψ)) Ψ = 0 := by
    rw [← conj_cfInner, h0, map_zero]
  rw [← conj_cfInner, ← cfInner_indClassFun L (χ - ψ) hΨ, h1, map_zero]

theorem apply_mul_eq_of_isOrthogonal_signedRootBlock (hD : IsDadeData L A R)
    (hloc : IsFrobeniusTypeLocalData H U U₁) (hodd : Odd (Nat.card ↥L))
    (hA : A = ambientCoreCentralizerSupport H)
    (hDdef : D = Subtype.val '' coreCentralizerSupportOutsideCore H)
    (hstab : D.Nonempty → ∀ g : G, (fun x => g⁻¹ * x * g) '' D = D ↔ g ∈ L)
    (hdisj : D.Nonempty → ∀ g ∉ L, D ∩ (fun x => g⁻¹ * x * g) '' D = ∅)
    (hη : ∀ χ ∈ irrDetect ℂ H, η χ ∈ Irr G ∧
      dadeMapFun L A R (χ - star χ) = η χ - star (η χ))
    {Ψ : G → ℂ} (hΨ : Ψ ∈ classFun G)
    (horth : ∀ θ ∈ indFam H (nonprincipalIrr ↥H),
      ∀ ρ ∈ signedRootBlock η θ, IsOrthogonal Ψ ρ)
    {x : ↥L} (hx : x ∉ H) {h : ↥L} (hh : h ∈ H) :
    Ψ ((x : G) * (h : G)) = Ψ (x : G) := by
  have hfam := isNormalInducedSignedFamily_dadeMapFun hD hloc hodd hA
    (U := U) (U₁ := U₁) hη
  have key := apply_mul_eq_of_cfInner_sub_eq_zero H hfam.eq_sum_irrConstituents
    (resClassFun_mem_classFun L hΨ)
    (fun θ hθ χ hχ ψ hψ => cfInner_resClassFun_sub_eq_zero hD hloc hodd hA hDdef hstab hdisj
      hη hΨ horth hθ hχ hψ) hx hh
  simpa [resClassFun_apply] using key

theorem apply_mul_eq_of_isOrthogonal_signedRootBlock_dadeRoot (hD : IsDadeData L A R)
    (hloc : IsFrobeniusTypeLocalData H U U₁) (hodd : Odd (Nat.card ↥L))
    (hA : A = ambientCoreCentralizerSupport H)
    (hDdef : D = Subtype.val '' coreCentralizerSupportOutsideCore H)
    (hstab : D.Nonempty → ∀ g : G, (fun x => g⁻¹ * x * g) '' D = D ↔ g ∈ L)
    (hdisj : D.Nonempty → ∀ g ∉ L, D ∩ (fun x => g⁻¹ * x * g) '' D = ∅)
    {Ψ : G → ℂ} (hΨ : Ψ ∈ classFun G)
    (horth : ∀ θ ∈ indFam H (nonprincipalIrr ↥H),
      ∀ ρ ∈ signedRootBlock (dadeRoot L A R) θ, IsOrthogonal Ψ ρ)
    {x : ↥L} (hx : x ∉ H) {h : ↥L} (hh : h ∈ H) :
    Ψ ((x : G) * (h : G)) = Ψ (x : G) :=
  apply_mul_eq_of_isOrthogonal_signedRootBlock hD hloc hodd hA hDdef hstab hdisj
    (dadeRoot_mem_Irr_and_map_sub_star_eq hD hodd hA) hΨ horth hx hh

end

end CFSG.FeitThompson

end
