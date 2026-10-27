module

public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
public import CFSG.FeitThompson.Representations.NormalSubgroupInduction
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexOrder ComplexConjugate

open NormalInduction (conjClassFun conjClassFun_apply)

section Constituents

variable {K : Type*} [Group K] (N : Subgroup K) [Fintype N] (χ : K → ℂ)

open scoped Classical in
noncomputable def resConstituents : Finset (N → ℂ) :=
  (irrFinset N).filter fun lam => 0 < cfInner (resClassFun N χ) lam

variable {N χ}

theorem mem_resConstituents {lam : N → ℂ} :
    lam ∈ resConstituents N χ ↔ lam ∈ Irr N ∧ 0 < cfInner (resClassFun N χ) lam := by
  classical
  rw [resConstituents, Finset.mem_filter, mem_irrFinset]

theorem resConstituents_subset_irrFinset : resConstituents N χ ⊆ irrFinset N :=
  fun _ h => mem_irrFinset.2 (mem_resConstituents.1 h).1

theorem resConstituents_subset_Irr : (resConstituents N χ : Set (N → ℂ)) ⊆ Irr N :=
  fun _ h => (mem_resConstituents.1 h).1

end Constituents

section Res

variable {K : Type*} [Group K] {N : Subgroup K} {χ : K → ℂ}

theorem resClassFun_fdRepCharacter (V : FDRep ℂ K) (N : Subgroup K) :
    resClassFun N (FDRep.character V) = Representation.character (V.ρ.comp N.subtype) := by
  funext n
  rw [resClassFun_apply, fdRepCharacter_eq]
  rfl

theorem resClassFun_sum {ι : Type*} (s : Finset ι) (F : ι → K → ℂ) :
    resClassFun N (∑ i ∈ s, F i) = ∑ i ∈ s, resClassFun N (F i) := by
  funext n
  simp only [resClassFun_apply, Finset.sum_apply]

theorem resClassFun_smul (c : ℂ) (f : K → ℂ) :
    resClassFun N (c • f) = c • resClassFun N f := by
  funext n
  simp only [resClassFun_apply, Pi.smul_apply]

theorem exists_multiplicities_resClassFun [Finite N] (hχ : χ ∈ Irr K) :
    ∃ m : irrFinset N → ℕ,
      resClassFun N χ = ∑ lam : irrFinset N, (m lam : ℂ) • (lam : N → ℂ) := by
  obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
  obtain ⟨m, hm⟩ := exists_character_eq_sum_nsmul (V.ρ.comp N.subtype)
  exact ⟨m, by rw [resClassFun_fdRepCharacter, hm]⟩

variable [Fintype N]

theorem exists_natCast_cfInner_resClassFun (hχ : χ ∈ Irr K) {lam : N → ℂ}
    (hlam : lam ∈ Irr N) : ∃ k : ℕ, cfInner (resClassFun N χ) lam = (k : ℂ) := by
  obtain ⟨m, hm⟩ := exists_multiplicities_resClassFun (N := N) hχ
  exact ⟨_, cfInner_eq_multiplicity hm ⟨lam, mem_irrFinset.2 hlam⟩⟩

theorem cfInner_resClassFun_nonneg (hχ : χ ∈ Irr K) {lam : N → ℂ} (hlam : lam ∈ Irr N) :
    0 ≤ cfInner (resClassFun N χ) lam := by
  obtain ⟨k, hk⟩ := exists_natCast_cfInner_resClassFun hχ hlam
  rw [hk]
  exact Nat.cast_nonneg k

theorem conj_cfInner_resClassFun (hχ : χ ∈ Irr K) {lam : N → ℂ} (hlam : lam ∈ Irr N) :
    conj (cfInner (resClassFun N χ) lam) = cfInner (resClassFun N χ) lam := by
  obtain ⟨k, hk⟩ := exists_natCast_cfInner_resClassFun hχ hlam
  rw [hk, Complex.conj_natCast]

theorem resClassFun_eq_sum_cfInner_smul (hχ : χ ∈ Irr K) :
    resClassFun N χ = ∑ lam ∈ irrFinset N, cfInner (resClassFun N χ) lam • lam := by
  obtain ⟨m, hm⟩ := exists_multiplicities_resClassFun (N := N) hχ
  calc resClassFun N χ = ∑ lam : irrFinset N, (m lam : ℂ) • (lam : N → ℂ) := hm
    _ = ∑ lam : irrFinset N, cfInner (resClassFun N χ) (lam : N → ℂ) • (lam : N → ℂ) :=
        Finset.sum_congr rfl fun lam _ => by rw [cfInner_eq_multiplicity hm lam]
    _ = ∑ lam ∈ irrFinset N, cfInner (resClassFun N χ) lam • lam :=
        Finset.sum_coe_sort (irrFinset N) fun lam => cfInner (resClassFun N χ) lam • lam

theorem cfInner_indClassFun_eq_cfInner_resClassFun [Fintype K] (hχ : χ ∈ Irr K) {lam : N → ℂ}
    (hlam : lam ∈ Irr N) :
    cfInner (indClassFun N lam) χ = cfInner (resClassFun N χ) lam := by
  rw [cfInner_indClassFun N lam (Irr_subset_classFun hχ), ← conj_cfInner,
    conj_cfInner_resClassFun hχ hlam]

end Res

theorem exists_multiplicities_indClassFun {K : Type*} [Group K] [Fintype K] {H : Subgroup K}
    {f : H → ℂ} (hf : f ∈ Irr H) :
    ∃ n : irrFinset K → ℕ, indClassFun H f = ∑ ψ : irrFinset K, (n ψ : ℂ) • (ψ : K → ℂ) := by
  obtain ⟨V, -, rfl⟩ := mem_Irr.1 hf
  obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_indClassFun H V
  obtain ⟨n, hn⟩ := exists_character_eq_sum_nsmul W.ρ
  exact ⟨n, by rw [← hW, fdRepCharacter_eq, hn]⟩

section Conj

variable {K : Type*} [Group K] {N : Subgroup K} {χ : K → ℂ}

theorem cfInner_conjClassFun_conjClassFun (N : Subgroup K) [N.Normal] [Fintype N] (t : K)
    (f h : N → ℂ) :
    cfInner (conjClassFun N t f) (conjClassFun N t h) = cfInner f h := by
  rw [cfInner_def, cfInner_def]
  congr 1
  exact Fintype.sum_equiv (MulAut.conjNormal (H := N) t⁻¹).toEquiv _ _ fun n => by
    simp only [conjClassFun_apply]
    rfl

theorem conjClassFun_resClassFun (N : Subgroup K) [N.Normal] (t : K) (hχ : χ ∈ classFun K) :
    conjClassFun N t (resClassFun N χ) = resClassFun N χ := by
  funext n
  rw [conjClassFun_apply, resClassFun_apply, resClassFun_apply,
    NormalInduction.coe_conjNormal_inv]
  simpa using classFun.apply_conj hχ (n : K) t⁻¹

theorem cfInner_resClassFun_conjClassFun [N.Normal] [Fintype N] (hχ : χ ∈ classFun K) (t : K)
    (lam : N → ℂ) :
    cfInner (resClassFun N χ) (conjClassFun N t lam) = cfInner (resClassFun N χ) lam := by
  have h := cfInner_conjClassFun_conjClassFun N t (resClassFun N χ) lam
  rwa [conjClassFun_resClassFun N t hχ] at h

end Conj

section Orbit

variable {K : Type*} [Group K] {N : Subgroup K} [Fintype N] {χ : K → ℂ}

theorem cfInner_resClassFun_indClassFun_eq_zero [Fintype K] [N.Normal] {lam mu : N → ℂ}
    (hlam : lam ∈ Irr N) (hmu : mu ∈ Irr N) (h : ∀ t : K, conjClassFun N t lam ≠ mu) :
    cfInner (resClassFun N (indClassFun N lam)) mu = 0 := by
  classical
  obtain ⟨S, hS, -⟩ := N.exists_isComplement_left 1
  have : Fintype S := Fintype.ofFinite S
  have hT : Subgroup.IsComplement (S.toFinset : Set K) (N : Set K) := by
    rwa [Set.coe_toFinset]
  rw [resClassFun_indClassFun_eq_sum N (Irr_subset_classFun hlam) hT, cfInner_sum_left]
  exact Finset.sum_eq_zero fun t _ =>
    cfInner_eq_zero_of_mem_Irr (conjClassFun_mem_Irr N t hlam) hmu (h t)

theorem cfInner_resClassFun_eq_zero_of_forall_conjClassFun_ne [Finite K] [N.Normal]
    {lam mu : N → ℂ} (hχ : χ ∈ Irr K) (hlam : lam ∈ Irr N) (hmu : mu ∈ Irr N)
    (hpos : 0 < cfInner (resClassFun N χ) lam) (h : ∀ t : K, conjClassFun N t lam ≠ mu) :
    cfInner (resClassFun N χ) mu = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hn⟩ := exists_multiplicities_indClassFun (H := N) hlam
  have hres : resClassFun N (indClassFun N lam)
      = ∑ ψ : irrFinset K, (n ψ : ℂ) • resClassFun N (ψ : K → ℂ) := by
    rw [hn, resClassFun_sum]
    exact Finset.sum_congr rfl fun ψ _ => resClassFun_smul _ _
  have hzero := cfInner_resClassFun_indClassFun_eq_zero hlam hmu h
  rw [hres, cfInner_sum_left] at hzero
  have hnonneg : ∀ ψ ∈ (Finset.univ : Finset (irrFinset K)),
      0 ≤ cfInner ((n ψ : ℂ) • resClassFun N (ψ : K → ℂ)) mu := by
    intro ψ _
    rw [cfInner_smul_left]
    exact mul_nonneg (Nat.cast_nonneg _)
      (cfInner_resClassFun_nonneg (mem_irrFinset.1 ψ.2) hmu)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hzero
  set ψχ : irrFinset K := ⟨χ, mem_irrFinset.2 hχ⟩ with hψχ
  have hterm := hall ψχ (Finset.mem_univ _)
  rw [cfInner_smul_left] at hterm
  have hnχ : (n ψχ : ℂ) ≠ 0 := by
    have hval : (n ψχ : ℂ) = cfInner (indClassFun N lam) χ := (cfInner_eq_multiplicity hn ψχ).symm
    rw [hval, cfInner_indClassFun_eq_cfInner_resClassFun hχ hlam]
    exact ne_of_gt hpos
  exact (mul_eq_zero.1 hterm).resolve_left hnχ

theorem resConstituents_nonempty (hχ : χ ∈ Irr K) : (resConstituents N χ).Nonempty := by
  classical
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  have hzero : ∀ lam ∈ irrFinset N, cfInner (resClassFun N χ) lam = 0 := by
    intro lam hlam
    have h1 : ¬ (0 < cfInner (resClassFun N χ) lam) := fun h =>
      Finset.notMem_empty lam (hemp ▸ mem_resConstituents.2 ⟨mem_irrFinset.1 hlam, h⟩)
    exact ((cfInner_resClassFun_nonneg hχ (mem_irrFinset.1 hlam)).lt_or_eq.resolve_left h1).symm
  have hres : resClassFun N χ = 0 := by
    rw [resClassFun_eq_sum_cfInner_smul hχ]
    exact Finset.sum_eq_zero fun lam hlam => by rw [hzero lam hlam, zero_smul]
  have h1 : χ 1 = 0 := by
    have h := congrFun hres 1
    rwa [resClassFun_apply, Subgroup.coe_one, Pi.zero_apply] at h
  exact apply_one_ne_zero_of_mem_Irr hχ h1

theorem mem_resConstituents_iff_exists_conjClassFun [Finite K] [N.Normal] (hχ : χ ∈ Irr K)
    {lam : N → ℂ} (hlam : lam ∈ resConstituents N χ) {mu : N → ℂ} :
    mu ∈ resConstituents N χ ↔ ∃ t : K, conjClassFun N t lam = mu := by
  obtain ⟨hlamIrr, hlampos⟩ := mem_resConstituents.1 hlam
  constructor
  · intro hmu
    obtain ⟨hmuIrr, hmupos⟩ := mem_resConstituents.1 hmu
    by_contra hcon
    push Not at hcon
    exact hmupos.ne'
      (cfInner_resClassFun_eq_zero_of_forall_conjClassFun_ne hχ hlamIrr hmuIrr hlampos hcon)
  · rintro ⟨t, rfl⟩
    refine mem_resConstituents.2 ⟨conjClassFun_mem_Irr N t hlamIrr, ?_⟩
    rwa [cfInner_resClassFun_conjClassFun (Irr_subset_classFun hχ)]

theorem cfInner_resClassFun_eq_of_mem_resConstituents [Finite K] [N.Normal] (hχ : χ ∈ Irr K)
    {lam mu : N → ℂ} (hlam : lam ∈ resConstituents N χ) (hmu : mu ∈ resConstituents N χ) :
    cfInner (resClassFun N χ) mu = cfInner (resClassFun N χ) lam := by
  obtain ⟨t, rfl⟩ := (mem_resConstituents_iff_exists_conjClassFun hχ hlam).1 hmu
  exact cfInner_resClassFun_conjClassFun (Irr_subset_classFun hχ) t lam

theorem exists_pos_resClassFun_eq_nsmul_sum [Finite K] [N.Normal] (hχ : χ ∈ Irr K) :
    ∃ e : ℕ, 0 < e ∧ (∀ lam ∈ resConstituents N χ, cfInner (resClassFun N χ) lam = (e : ℂ)) ∧
      resClassFun N χ = (e : ℂ) • ∑ lam ∈ resConstituents N χ, lam := by
  classical
  obtain ⟨lam₀, hlam₀⟩ := resConstituents_nonempty (N := N) hχ
  obtain ⟨hlam₀Irr, hlam₀pos⟩ := mem_resConstituents.1 hlam₀
  obtain ⟨e, he⟩ := exists_natCast_cfInner_resClassFun hχ hlam₀Irr
  have hepos : 0 < e := by
    rw [he] at hlam₀pos
    exact_mod_cast hlam₀pos
  have hconst : ∀ lam ∈ resConstituents N χ, cfInner (resClassFun N χ) lam = (e : ℂ) := by
    intro lam hlam
    rw [cfInner_resClassFun_eq_of_mem_resConstituents hχ hlam₀ hlam, he]
  refine ⟨e, hepos, hconst, ?_⟩
  rw [resClassFun_eq_sum_cfInner_smul hχ, Finset.smul_sum,
    ← Finset.sum_subset (resConstituents_subset_irrFinset (N := N) (χ := χ))]
  · exact Finset.sum_congr rfl fun lam hlam => by rw [hconst lam hlam]
  · intro lam hlam hnot
    have hzero : cfInner (resClassFun N χ) lam = 0 := by
      have h1 : ¬ (0 < cfInner (resClassFun N χ) lam) := fun h =>
        hnot (mem_resConstituents.2 ⟨mem_irrFinset.1 hlam, h⟩)
      exact ((cfInner_resClassFun_nonneg hχ (mem_irrFinset.1 hlam)).lt_or_eq.resolve_left h1).symm
    rw [hzero, zero_smul]

end Orbit

end CFSG.FeitThompson
