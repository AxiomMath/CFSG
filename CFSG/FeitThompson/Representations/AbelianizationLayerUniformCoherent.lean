module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Representations.NormalKernelLayerWeightedDegreeSum
public import CFSG.FeitThompson.Representations.CoprimePowerInducedLinearFamily
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree
import CFSG.FeitThompson.Representations.EqualDegreeFamilyCoherence
public import CFSG.FeitThompson.Representations.DisjointConjugateFamiliesOrthogonalImages
import CFSG.FeitThompson.Representations.LinearIrreduciblesKillDerived
import CFSG.FeitThompson.Representations.SolvableGroupNonprincipalLinearCharacter
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open NormalInducedFamily NormalLinearInduced
open scoped Pointwise

namespace NormalInducedFamily

variable {L : Type*} [Group L]

theorem kerLayerIrr_anti_left {A B K : Subgroup L} (h : A ≤ B) :
    kerLayerIrr B K ⊆ kerLayerIrr A K := fun _ hθ =>
  have ⟨hirr, hker, hne⟩ := mem_kerLayerIrr.1 hθ
  mem_kerLayerIrr.2 ⟨hirr, fun n hn => hker n (h hn), hne⟩

theorem kerLayerIndFam_anti_left [Fintype L] {A B K : Subgroup L} (h : A ≤ B) :
    kerLayerIndFam B K ⊆ kerLayerIndFam A K := by
  intro f hf
  obtain ⟨θ, hθ, rfl⟩ := mem_kerLayerIndFam.1 hf
  exact mem_kerLayerIndFam.2 ⟨θ, kerLayerIrr_anti_left h hθ, rfl⟩

theorem kerLayerIrr_commutator_eq_nonprincipalLinearIrr [Finite L] (H : Subgroup L) :
    kerLayerIrr ⁅H, H⁆ H = nonprincipalLinearIrr ↥H := by
  ext θ
  rw [mem_kerLayerIrr, mem_nonprincipalLinearIrr]
  constructor
  · rintro ⟨hirr, hker, hne⟩
    refine ⟨hirr, Irr.apply_one_eq_one_of_commutator_subset_charValueKernel hirr ?_, hne⟩
    exact fun x hx => mem_charValueKernel.2 (hker x ((coe_mem_commutator_iff H).2 hx))
  · rintro ⟨hirr, h1, hne⟩
    refine ⟨hirr, fun n hn => ?_, hne⟩
    exact mem_charValueKernel.1
      (Irr.commutator_subset_charValueKernel hirr h1 ((coe_mem_commutator_iff H).1 hn))

theorem kerLayerIndFam_commutator_eq_indFamLinear [Fintype L] (H : Subgroup L) :
    kerLayerIndFam ⁅H, H⁆ H = indFamLinear H := by
  ext f
  rw [mem_kerLayerIndFam, mem_indFamLinear, kerLayerIrr_commutator_eq_nonprincipalLinearIrr]

theorem apply_one_of_mem_kerLayerIndFam_commutator [Fintype L] {H : Subgroup L} {f : L → ℂ}
    (hf : f ∈ kerLayerIndFam ⁅H, H⁆ H) : f 1 = (H.index : ℂ) := by
  rw [kerLayerIndFam_commutator_eq_indFamLinear] at hf
  exact apply_one_of_mem_indFamLinear H hf

end NormalInducedFamily

variable {L : Type*} [Group L] {H E : Subgroup L}

theorem commutator_lt_self_of_ne_bot [Group.IsSolvable ↥H] (hH : H ≠ ⊥) : ⁅H, H⁆ < H := by
  refine lt_of_le_of_ne (Subgroup.commutator_le_self H) fun heq => ?_
  have _ : Nontrivial ↥H := H.nontrivial_iff_ne_bot.2 hH
  exact commutator_ne_top_of_isSolvable ↥H
    (eq_top_iff.2 fun x _ => (coe_mem_commutator_iff H).1 (by rw [heq]; exact x.2))

theorem indClassFun_mem_Irr_of_frobenius [Fintype L] [H.Normal] (hH : H ≠ ⊥)
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    {θ : ↥H → ℂ} (hθ : θ ∈ Irr ↥H) (hθ1 : θ ≠ 1) : indClassFun H θ ∈ Irr L := by
  have _ : Nontrivial ↥H := H.nontrivial_iff_ne_bot.2 hH
  have _ : Fintype ↥H := Fintype.ofFinite _
  have _ : Fintype ↥E := Fintype.ofFinite _
  have hHE : H.IsComplement' E := isComplement'_of_mul_eq_univ_of_inf_eq_bot hmul hinf
  refine mem_Irr_of_comp_mulEquiv (frobeniusMulEquiv hHE) ?_
  rw [indClassFun_comp_frobeniusMulEquiv hHE θ]
  exact indClassFun_kernelClassFun_mem_Irr
    (fun v hv => fixedPointFree_frobeniusConjAut
      (hC (v : L) v.2 (fun h => hv (Subtype.ext h)))) hθ hθ1

theorem kerLayerIndFam_subset_Irr_of_frobenius [Fintype L] [H.Normal] (A : Subgroup L)
    (hH : H ≠ ⊥) (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) :
    kerLayerIndFam A H ⊆ Irr L := by
  intro f hf
  obtain ⟨θ, hθ, rfl⟩ := mem_kerLayerIndFam.1 hf
  obtain ⟨hirr, -, hne⟩ := mem_kerLayerIrr.1 hθ
  exact indClassFun_mem_Irr_of_frobenius (E := E) hH hmul hinf hC hirr hne

theorem apply_one_of_mem_kerLayerIndFam_commutator_eq_card [Fintype L] {f : L → ℂ}
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hf : f ∈ kerLayerIndFam ⁅H, H⁆ H) : f 1 = (Nat.card E : ℂ) := by
  rw [apply_one_of_mem_kerLayerIndFam_commutator hf,
    index_eq_card_of_isComplement' (isComplement'_of_mul_eq_univ_of_inf_eq_bot hmul hinf)]

theorem nonempty_kerLayerIndFam_commutator [Fintype L] [Group.IsNilpotent ↥H] (hH : H ≠ ⊥) :
    (kerLayerIndFam ⁅H, H⁆ H).Nonempty := by
  have _ : Nontrivial ↥H := H.nontrivial_iff_ne_bot.2 hH
  obtain ⟨θ, hθ, hθ1, hθne⟩ := exists_mem_Irr_apply_one_eq_one_and_ne_one ↥H
  rw [kerLayerIndFam_commutator_eq_indFamLinear]
  exact ⟨indClassFun H θ,
    indClassFun_mem_indFamLinear H (mem_nonprincipalLinearIrr.2 ⟨hθ, hθ1, hθne⟩)⟩

theorem two_le_ncard_kerLayerIndFam_commutator [Fintype L] [H.Normal] [Group.IsNilpotent ↥H]
    (hodd : Odd (Nat.card L)) (hH : H ≠ ⊥)
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) :
    2 ≤ (kerLayerIndFam ⁅H, H⁆ H).ncard := by
  have hne := nonempty_kerLayerIndFam_commutator (H := H) hH
  rw [kerLayerIndFam_commutator_eq_indFamLinear] at hne ⊢
  refine two_le_ncard_indFamLinear H hodd hne ?_
  rw [← kerLayerIndFam_commutator_eq_indFamLinear]
  exact kerLayerIndFam_subset_Irr_of_frobenius (E := E) _ hH hmul hinf hC

theorem isCoherent_kerLayerIndFam_commutator {G : Type*} [Group G] [Fintype G] [Fintype L]
    [H.Normal] [Group.IsNilpotent ↥H] (hH : H ≠ ⊥)
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (τ : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H) →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H), (τ f : G → ℂ) 1 = 0) :
    IsCoherent (kerLayerIndFam ⁅H, H⁆ H)
      (restrictBaseline (kerLayerIndFam_anti_left (K := H) bot_le) τ) := by
  refine isCoherent_of_forall_apply_one_eq (d := (H.index : ℂ)) finite_kerLayerIndFam
    (kerLayerIndFam_subset_Irr_of_frobenius (E := E) _ hH hmul hinf hC)
    (fun _ hχ => apply_one_of_mem_kerLayerIndFam_commutator hχ) _ ?_ ?_
  · intro f g
    rw [restrictBaseline_apply, restrictBaseline_apply, hτiso]
    rfl
  · intro f
    rw [restrictBaseline_apply]
    exact hτ1 _

end CFSG.FeitThompson
