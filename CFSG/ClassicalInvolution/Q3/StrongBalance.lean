module

public import CFSG.ClassicalInvolution.Q3.Exact
public import CFSG.ClassicalInvolution.Balance.BootstrapDelta
public import CFSG.ClassicalInvolution.Balance.BootstrapFunctor

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Generic.DeltaClosure
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_involutionOddCore {A : Subgroup G} (hA : IsElemAbelian 2 A) {a : G}
    (ha : a ∈ A) : A ≤ Subgroup.normalizer (involutionOddCore a : Set G) := fun e he =>
  normalizer_oddCoreIn (Subgroup.centralizer ({a} : Set G))
    (Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.is_comm.comm (⟨e, he⟩ : A) ⟨a, ha⟩)))

theorem stronglyBalanced_of_weakBalanced {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) (hW : WeakBalanced A)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥) : StronglyBalanced A := by
  intro a ha ha1
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two A (involutionOddCore a) hA (by simpa using h8)
    (le_normalizer_involutionOddCore hA ha)
    (Nat.coprime_two_left.mpr (odd_card_oddCoreIn (Subgroup.centralizer ({a} : Set G))))
  rw [← hgen]
  refine iSup₂_le fun F hF x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hcomm : ⁅x, g⁆ ∈ deltaCore F := by
    refine mem_deltaCore_iff.mpr fun d hd hd1 => ?_
    have hdA : d ∈ A := hF.1 hd
    have hxd : x ∈ involutionOddCore a ⊓ Subgroup.centralizer ({d} : Set G) :=
      ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hx.2 d hd).symm)⟩
    exact hW a ha ha1 d hdA hd1 (Subgroup.commutator_mem_commutator hxd hg)
  rw [hΔ F hF, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcomm
  exact hcomm.symm

theorem involutionOddCore_le_oddCoreIn_centralizer {A : Subgroup G} (hSB : StronglyBalanced A)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    involutionOddCore a ≤ oddCoreIn (Subgroup.centralizer (A : Set G)) := by
  refine le_oddCoreIn_of_normalizes (hSB a ha ha1) (fun g hg => ?_)
    (odd_card_oddCoreIn (Subgroup.centralizer ({a} : Set G)))
  exact normalizer_oddCoreIn (Subgroup.centralizer ({a} : Set G))
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha) hg)

@[expose] def ClassicalBalanced (A : Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
    involutionOddCore a ⊓ Subgroup.centralizer ({b} : Set G) ≤ involutionOddCore b

theorem involutionOddCore_eq_bot_of_classicalBalanced {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) (hCB : ClassicalBalanced A)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥) {x : G} (hx : x ∈ A) (hx1 : x ≠ 1) :
    involutionOddCore x = ⊥ := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two A (involutionOddCore x) hA (by simpa using h8)
    (le_normalizer_involutionOddCore hA hx)
    (Nat.coprime_two_left.mpr (odd_card_oddCoreIn (Subgroup.centralizer ({x} : Set G))))
  rw [eq_bot_iff, ← hgen]
  refine iSup₂_le fun F hF => ?_
  have hle : involutionOddCore x ⊓ Subgroup.centralizer (F : Set G) ≤ deltaCore F := by
    refine le_deltaCore fun d hd hd1 y hy => ?_
    have hyd : y ∈ involutionOddCore x ⊓ Subgroup.centralizer ({d} : Set G) :=
      ⟨hy.1, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd) hy.2⟩
    exact hCB x hx hx1 d (hF.1 hd) hd1 hyd
  rw [hΔ F hF] at hle
  exact hle

theorem localOddCentral3_of_members_centralize {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {x : G}
    (h : ∀ L ∈ Ω, L ≤ Subgroup.centralizer ({x} : Set G) →
      L ≤ Subgroup.centralizer (involutionOddCore x : Set G)) :
    LocalOddCentral Ω {x} := by
  have hY : centralizingLayer Ω {x} ≤ Subgroup.centralizer (involutionOddCore x : Set G) :=
    iSup₂_le fun L hL => h L hL.1 hL.2
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro w
  have hO : (y : G) ∈ involutionOddCore x :=
    oddCoreIn_centralizingLayer_le hΩ x ⟨y, hy, rfl⟩
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hY w.2) y hO).symm

theorem localOddCentral3_of_involutionOddCore_eq_bot {Ω : Set (Subgroup G)}
    (hΩ : ConjInvariant Ω) {x : G} (hx : involutionOddCore x = ⊥) : LocalOddCentral Ω {x} :=
  localOddCentral3_of_members_centralize hΩ fun L _ _ => by
    rw [hx]
    intro l _
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hn
    rw [hn]
    simp

end CFSG.ClassicalInvolution.Q3
