module

public import CFSG.FeitThompson.Representations.NormalRestrictionSingleConstituentOrbit
public import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate ComplexOrder

open NormalInduction (conjClassFun conjClassFun_apply)

section Constituents

variable {L : Type*} [Group L] [Fintype L]

noncomputable def irrConstituents (θ : L → ℂ) : Set (L → ℂ) := {χ ∈ Irr L | 0 < cfInner θ χ}

theorem mem_irrConstituents {θ χ : L → ℂ} :
    χ ∈ irrConstituents θ ↔ χ ∈ Irr L ∧ 0 < cfInner θ χ := Iff.rfl

theorem irrConstituents_subset_Irr (θ : L → ℂ) : irrConstituents θ ⊆ Irr L :=
  fun _ h => (mem_irrConstituents.1 h).1

theorem finite_irrConstituents (θ : L → ℂ) : (irrConstituents θ).Finite :=
  finite_Irr.subset (irrConstituents_subset_Irr θ)

@[simp] theorem irrConstituents_zero : irrConstituents (0 : L → ℂ) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun χ hχ => ?_
  have h := (mem_irrConstituents.1 hχ).2
  rw [show cfInner (0 : L → ℂ) χ = 0 by rw [← zero_smul ℂ (0 : L → ℂ), cfInner_smul_left, zero_mul]]
    at h
  exact absurd h (lt_irrefl 0)

theorem cfInner_eq_natCast_sum_mul {θ θ' : L → ℂ} {m n : irrFinset L → ℕ}
    (hm : θ = ∑ ψ : irrFinset L, (m ψ : ℂ) • (ψ : L → ℂ))
    (hn : θ' = ∑ ψ : irrFinset L, (n ψ : ℂ) • (ψ : L → ℂ)) :
    cfInner θ θ' = ((∑ ψ : irrFinset L, m ψ * n ψ : ℕ) : ℂ) := by
  rw [hm, cfInner_sum_left]
  push_cast
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [cfInner_smul_left, ← conj_cfInner θ' (ψ : L → ℂ), cfInner_eq_multiplicity hn ψ,
    Complex.conj_natCast]

theorem cfInner_ne_zero_of_mem_irrConstituents {θ θ' : L → ℂ} {m n : irrFinset L → ℕ}
    (hm : θ = ∑ ψ : irrFinset L, (m ψ : ℂ) • (ψ : L → ℂ))
    (hn : θ' = ∑ ψ : irrFinset L, (n ψ : ℂ) • (ψ : L → ℂ))
    {χ : L → ℂ} (hθ : χ ∈ irrConstituents θ) (hθ' : χ ∈ irrConstituents θ') :
    cfInner θ θ' ≠ 0 := by
  set ψχ : irrFinset L := ⟨χ, mem_irrFinset.2 (mem_irrConstituents.1 hθ).1⟩ with hψχ
  have hm0 : m ψχ ≠ 0 := by
    have h : (0 : ℂ) < (m ψχ : ℂ) := by
      rw [← cfInner_eq_multiplicity hm ψχ]; exact (mem_irrConstituents.1 hθ).2
    intro h0; rw [h0] at h; simp at h
  have hn0 : n ψχ ≠ 0 := by
    have h : (0 : ℂ) < (n ψχ : ℂ) := by
      rw [← cfInner_eq_multiplicity hn ψχ]; exact (mem_irrConstituents.1 hθ').2
    intro h0; rw [h0] at h; simp at h
  rw [cfInner_eq_natCast_sum_mul hm hn]
  have hle : m ψχ * n ψχ ≤ ∑ ψ : irrFinset L, m ψ * n ψ :=
    Finset.single_le_sum (f := fun ψ : irrFinset L => m ψ * n ψ)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ ψχ)
  have hne : (∑ ψ : irrFinset L, m ψ * n ψ) ≠ 0 := by
    have := Nat.mul_ne_zero hm0 hn0; omega
  exact_mod_cast hne

theorem mem_irrConstituents_indClassFun_iff {H : Subgroup L} [Fintype H] {lam : H → ℂ}
    (hlam : lam ∈ Irr H) {χ : L → ℂ} :
    χ ∈ irrConstituents (indClassFun H lam) ↔ χ ∈ Irr L ∧ lam ∈ resConstituents H χ := by
  rw [mem_irrConstituents]
  constructor
  · rintro ⟨hχ, hpos⟩
    rw [cfInner_indClassFun_eq_cfInner_resClassFun hχ hlam] at hpos
    exact ⟨hχ, mem_resConstituents.2 ⟨hlam, hpos⟩⟩
  · rintro ⟨hχ, hmem⟩
    refine ⟨hχ, ?_⟩
    rw [cfInner_indClassFun_eq_cfInner_resClassFun hχ hlam]
    exact (mem_resConstituents.1 hmem).2

theorem irrConstituents_indClassFun_nonempty (H : Subgroup L) {lam : H → ℂ}
    (hlam : lam ∈ Irr H) : (irrConstituents (indClassFun H lam)).Nonempty := by
  classical
  obtain ⟨n, hn⟩ := exists_multiplicities_indClassFun hlam
  have hne : indClassFun H lam ≠ 0 :=
    NormalInducedFamily.ne_zero_of_mem_indFam H (indClassFun_mem_indFam H hlam)
  by_contra hemp
  refine hne ?_
  rw [hn]
  refine Finset.sum_eq_zero fun ψ _ => ?_
  have h0 : n ψ = 0 := by
    by_contra hn0
    refine hemp ⟨(ψ : L → ℂ), mem_irrConstituents.2 ⟨mem_irrFinset.1 ψ.2, ?_⟩⟩
    rw [cfInner_eq_multiplicity hn ψ]
    exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [h0, Nat.cast_zero, zero_smul]

end Constituents

section Kernel

variable {L : Type*} [Group L]

theorem conjClassFun_one_eq_one (N : Subgroup L) [N.Normal] (t : L) :
    conjClassFun N t (1 : N → ℂ) = 1 := by
  funext n
  rw [conjClassFun_apply]
  rfl

theorem resClassFun_eq_smul_one_of_subset_charValueKernel {H : Subgroup L} {χ : L → ℂ}
    (hker : (H : Set L) ⊆ charValueKernel χ) :
    resClassFun H χ = χ 1 • (1 : H → ℂ) := by
  funext n
  rw [resClassFun_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  exact mem_charValueKernel.1 (hker n.2)

theorem one_notMem_resConstituents [Finite L] {H : Subgroup L} [H.Normal] [Fintype H] {χ : L → ℂ}
    (hχ : χ ∈ Irr L) (hker : ¬ (H : Set L) ⊆ charValueKernel χ) :
    (1 : H → ℂ) ∉ resConstituents H χ := by
  intro h1
  obtain ⟨e, -, -, hres⟩ := exists_pos_resClassFun_eq_nsmul_sum (N := H) hχ
  have hsing : resConstituents H χ = {1} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨h1, fun mu hmu => ?_⟩
    obtain ⟨t, ht⟩ := (mem_resConstituents_iff_exists_conjClassFun hχ h1).1 hmu
    rw [← ht, conjClassFun_one_eq_one]
  rw [hsing, Finset.sum_singleton] at hres
  refine hker fun x hx => ?_
  have hx' := congrFun hres ⟨x, hx⟩
  have h1' := congrFun hres (1 : H)
  rw [resClassFun_apply] at hx' h1'
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at hx' h1'
  rw [Subgroup.coe_one] at h1'
  exact mem_charValueKernel.2 (hx'.trans h1'.symm)

end Kernel

section Main

variable {L : Type*} [Group L] [Fintype L] (H : Subgroup L)

theorem irrConstituents_nonempty_of_mem_indFam {θ : L → ℂ}
    (hθ : θ ∈ indFam H (nonprincipalIrr H)) : (irrConstituents θ).Nonempty := by
  obtain ⟨lam, hlam, rfl⟩ := (mem_indFam H).1 hθ
  exact irrConstituents_indClassFun_nonempty H (mem_nonprincipalIrr.1 hlam).1

theorem pairwiseDisjoint_irrConstituents [H.Normal] :
    (indFam H (nonprincipalIrr H)).PairwiseDisjoint irrConstituents := by
  intro θ hθ θ' hθ' hne
  obtain ⟨lam, hlam, rfl⟩ := (mem_indFam H).1 hθ
  obtain ⟨mu, hmu, rfl⟩ := (mem_indFam H).1 hθ'
  obtain ⟨m, hm⟩ := exists_multiplicities_indClassFun (mem_nonprincipalIrr.1 hlam).1
  obtain ⟨n, hn⟩ := exists_multiplicities_indClassFun (mem_nonprincipalIrr.1 hmu).1
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro χ h1 h2
  refine cfInner_ne_zero_of_mem_irrConstituents hm hn h1 h2 ?_
  exact NormalInducedFamily.cfInner_eq_zero_of_mem_indFam H
    (indClassFun_mem_indFam H (mem_nonprincipalIrr.1 hlam).1)
    (indClassFun_mem_indFam H (mem_nonprincipalIrr.1 hmu).1) hne

theorem iUnion_irrConstituents [H.Normal] :
    ⋃ θ ∈ indFam H (nonprincipalIrr H), irrConstituents θ = irrDetect ℂ H := by
  have : Fintype H := Fintype.ofFinite H
  ext χ
  simp only [Set.mem_iUnion, exists_prop]
  rw [mem_irrDetect]
  constructor
  · rintro ⟨θ, hθ, hχ⟩
    obtain ⟨lam, hlam, rfl⟩ := (mem_indFam H).1 hθ
    obtain ⟨hlamIrr, hlamne⟩ := mem_nonprincipalIrr.1 hlam
    obtain ⟨hχIrr, hres⟩ := (mem_irrConstituents_indClassFun_iff hlamIrr).1 hχ
    refine ⟨(Irr_eq_irrChar L) ▸ hχIrr, fun hker => ?_⟩
    have hpos := (mem_resConstituents.1 hres).2
    rw [resClassFun_eq_smul_one_of_subset_charValueKernel hker, cfInner_smul_left,
      cfInner_eq_ite_of_mem_Irr one_mem_Irr hlamIrr, if_neg (Ne.symm hlamne), mul_zero] at hpos
    exact absurd hpos (lt_irrefl 0)
  · rintro ⟨hχ, hker⟩
    have hχIrr : χ ∈ Irr L := (Irr_eq_irrChar L).symm ▸ hχ
    obtain ⟨lam, hlam⟩ := resConstituents_nonempty (N := H) hχIrr
    have hlamIrr := (mem_resConstituents.1 hlam).1
    have hlamne : lam ≠ 1 := fun h => one_notMem_resConstituents hχIrr hker (h ▸ hlam)
    exact ⟨indClassFun H lam,
      indClassFun_mem_indFam H (mem_nonprincipalIrr.2 ⟨hlamIrr, hlamne⟩),
      (mem_irrConstituents_indClassFun_iff hlamIrr).2 ⟨hχIrr, hlam⟩⟩

theorem isPartition_irrConstituents [H.Normal] :
    (∀ θ ∈ indFam H (nonprincipalIrr H), (irrConstituents θ).Nonempty) ∧
      (indFam H (nonprincipalIrr H)).PairwiseDisjoint irrConstituents ∧
      ⋃ θ ∈ indFam H (nonprincipalIrr H), irrConstituents θ = irrDetect ℂ H :=
  ⟨fun _ hθ => irrConstituents_nonempty_of_mem_indFam H hθ,
    pairwiseDisjoint_irrConstituents H, iUnion_irrConstituents H⟩

end Main

end CFSG.FeitThompson
