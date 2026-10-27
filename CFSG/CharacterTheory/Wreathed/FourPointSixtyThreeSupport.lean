module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.PrincipalNonvanishing

public section

namespace CFSG.Wreathed.FourPointSixtyThree

open CFSG.TwoRankLowerBound.Helpers

theorem exists_faithful_plane {R K V : Type} [Group R] [Group K] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ K V) (f : R →* K)
    (P : Submodule ℂ V) (hinv : ∀ r : R, ∀ v ∈ P, ρ (f r) v ∈ P)
    (hfaith : ∀ r : R, (∀ v ∈ P, ρ (f r) v = v) → r = 1) (hdim : Module.finrank ℂ P = 2) :
    ∃ ρR : FiniteComplexRepresentation.{0, 0} R, Module.finrank ℂ ρR.vector = 2 ∧
      MonoidHom.ker ρR.representation = ⊥ := by
  let sub : Subrepresentation (ρ.comp f) := ⟨P, fun r v hv => hinv r v hv⟩
  refine ⟨⟨P, sub.toRepresentation⟩, hdim, ?_⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro r hr
  rw [MonoidHom.mem_ker] at hr
  apply hfaith r
  intro v hv
  have h := congrArg (fun T : Module.End ℂ P => (T ⟨v, hv⟩ : V)) hr
  exact h

theorem card_involutions_of_two_classes {N : Type*} [Group N] [Finite N] (x y : N) (k : ℕ)
    (hinv : ∀ t : N, orderOf t = 2 ↔ t = x ∨ IsConj y t) (hnc : ¬ IsConj x y)
    (hcard : Nat.card (ConjClasses.mk y).carrier = k) :
    Nat.card {t : N // orderOf t = 2} = k + 1 := by
  have hset : {t : N | orderOf t = 2} = insert x (ConjClasses.mk y).carrier := by
    ext t
    rw [Set.mem_ofPred_eq, hinv, Set.mem_insert_iff, ConjClasses.mem_carrier_iff_mk_eq,
      ConjClasses.mk_eq_mk_iff_isConj, isConj_comm]
  have hnot : x ∉ (ConjClasses.mk y).carrier := by
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    exact hnc
  change Nat.card ({t : N | orderOf t = 2} : Set N) = k + 1
  rw [hset, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hnot, ← Nat.card_coe_set_eq,
    hcard]

theorem card_involutions_of_one_class {G : Type*} [Group G] [Fintype G] (x : G)
    (hx : orderOf x = 2) (hall : ∀ g : G, orderOf g = 2 → IsConj x g) :
    Nat.card {g : G // orderOf g = 2} = (Subgroup.centralizer ({x} : Set G)).index := by
  have hset : {g : G | orderOf g = 2} = (ConjClasses.mk x).carrier := by
    ext g
    rw [Set.mem_ofPred_eq, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    constructor
    · intro hg
      exact (hall g hg).symm
    · intro hg
      obtain ⟨c, hc⟩ := isConj_iff.mp hg.symm
      rw [← hc, ← hx]
      exact ((MulAut.conj c).orderOf_eq x)
  change Nat.card ({g : G | orderOf g = 2} : Set G) = _
  rw [hset]
  exact CFSG.LyonsUnitaryFour.card_conjClass_eq_index x

end CFSG.Wreathed.FourPointSixtyThree
