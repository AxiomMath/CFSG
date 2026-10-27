module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Foundations.FittingContainsCentralizerSolvable
import CFSG.FeitThompson.Local.FittingMonoNormal
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X]

theorem isPiSubgroup_congr {π π' : Set ℕ} {N : Subgroup X}
    (h : ∀ p : ℕ, p.Prime → (p ∈ π ↔ p ∈ π')) : IsPiSubgroup π N ↔ IsPiSubgroup π' N := by
  rw [isPiSubgroup_iff, isPiSubgroup_iff]
  exact ⟨fun hN p hp => (h p (Nat.prime_of_mem_primeFactors hp)).1 (hN p hp),
    fun hN p hp => (h p (Nat.prime_of_mem_primeFactors hp)).2 (hN p hp)⟩

theorem piCore_congr [Finite X] {π π' : Set ℕ}
    (h : ∀ p : ℕ, p.Prime → (p ∈ π ↔ p ∈ π')) : piCore π X = piCore π' X :=
  le_antisymm (piCore_le fun _ hN hπ => le_piCore hN ((isPiSubgroup_congr h).1 hπ))
    (piCore_le fun _ hN hπ => le_piCore hN ((isPiSubgroup_congr fun p hp => (h p hp).symm).1 hπ))

theorem eq_bot_of_isPiSubgroup_of_isPiSubgroup [Finite X] {π π' : Set ℕ} {N : Subgroup X}
    (hd : ∀ p ∈ π, p ∉ π') (h : IsPiSubgroup π N) (h' : IsPiSubgroup π' N) : N = ⊥ := by
  have hpf : (Nat.card N).primeFactors = ∅ := by
    ext p
    simpa using fun hp => hd p (isPiSubgroup_iff.1 h p hp) (isPiSubgroup_iff.1 h' p hp)
  rcases Nat.primeFactors_eq_empty.1 hpf with hc | hc
  · exact absurd hc Nat.card_pos.ne'
  · exact Subgroup.card_eq_one.1 hc

theorem piCore_compl_eq_bot_of_isPiSubgroup_fittingRaw (π : Set ℕ) (X : Type*) [Group X]
    [Finite X] [Group.IsSolvable X] (hF : IsPiSubgroup π (fittingRaw X)) :
    piCore πᶜ X = ⊥ := by
  set D := piCore πᶜ X with hD
  have hDn : D.Normal := piCore_normal πᶜ X
  have hinf : (fittingRaw D).map D.subtype = fittingRaw X ⊓ D :=
    map_subtype_fittingRaw_eq_inf hDn
  have hbot : fittingRaw X ⊓ D = ⊥ :=
    eq_bot_of_isPiSubgroup_of_isPiSubgroup (π := π) (π' := πᶜ) (fun _ hp hp' => hp' hp)
      (hF.of_le inf_le_left) ((isPiSubgroup_piCore πᶜ X).of_le inf_le_right)
  have hFD : fittingRaw D = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).1 (hinf.trans hbot)
  have hctop : Subgroup.centralizer ((fittingRaw D : Subgroup D) : Set D) = ⊤ := by
    rw [hFD]; exact Subgroup.centralizer_eq_top_iff_subset.2 (by simp)
  have htop : (⊤ : Subgroup D) = ⊥ :=
    le_antisymm (hctop ▸ (centralizer_fittingRaw_le_fittingRaw D).trans hFD.le) bot_le
  refine (Subgroup.eq_bot_iff_forall D).2 fun x hx => ?_
  have hmem : (⟨x, hx⟩ : D) ∈ (⊥ : Subgroup D) := htop ▸ Subgroup.mem_top _
  simpa [Subgroup.mem_bot, Subtype.ext_iff] using hmem

theorem piCore_primesNotMem_eq_bot (π : Set ℕ) (X : Type*) [Group X] [Finite X]
    [Group.IsSolvable X] (hF : IsPiSubgroup π (fittingRaw X)) :
    piCore {q : ℕ | q.Prime ∧ q ∉ π} X = ⊥ := by
  rw [piCore_congr (π' := πᶜ) fun p hp => by simp [hp]]
  exact piCore_compl_eq_bot_of_isPiSubgroup_fittingRaw π X hF

theorem pComplCore_eq_bot_of_isPGroup_fittingRaw {p : ℕ} (hp : p.Prime) (X : Type*) [Group X]
    [Finite X] [Group.IsSolvable X] (hF : IsPGroup p (fittingRaw X)) : pComplCore p X = ⊥ := by
  rw [pComplCore_eq_piCore, piCore_congr (π' := ({p} : Set ℕ)ᶜ) fun q hq => by simp [hq]]
  exact piCore_compl_eq_bot_of_isPiSubgroup_fittingRaw _ X
    ((isPiSubgroup_singleton_iff hp _).2 hF)

theorem subsingleton_of_fittingRaw_eq_bot (X : Type*) [Group X] [Finite X] [Group.IsSolvable X]
    (hF : fittingRaw X = ⊥) : Subsingleton X := by
  have h : piCore (∅ : Set ℕ)ᶜ X = ⊥ :=
    piCore_compl_eq_bot_of_isPiSubgroup_fittingRaw ∅ X (hF ▸ isPiSubgroup_bot ∅)
  rw [Set.compl_empty, piCore_univ] at h
  exact subsingleton_of_forall_eq 1 fun x => (Subgroup.eq_bot_iff_forall _).1 h x (by simp)

end

end CFSG.FeitThompson
