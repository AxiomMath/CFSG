module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
public import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.TripleCommutatorsCentralProductCollection
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem disjoint_of_disjoint_subgroupOf {S X Y : Subgroup G} (hX : X ≤ S)
    (h : Disjoint (X.subgroupOf S) (Y.subgroupOf S)) : Disjoint X Y := by
  rw [disjoint_iff] at h ⊢
  have h1 : (X ⊓ Y).subgroupOf S = ⊥ := by
    rw [Subgroup.subgroupOf, Subgroup.comap_inf]; exact h
  rw [Subgroup.subgroupOf_eq_bot, disjoint_iff] at h1
  have h2 : X ⊓ Y ≤ S := le_trans inf_le_left hX
  rw [← h1, inf_eq_left.2 h2]

section Transfer

variable {E : Subgroup G}

theorem subgroupOf_map_subtype (X : Subgroup E) : (X.map E.subtype).subgroupOf E = X := by
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective E.subtype_injective]

theorem map_subtype_eq_bot_iff {X : Subgroup E} : X.map E.subtype = ⊥ ↔ X = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective X E.subtype_injective

theorem disjoint_map_subtype {X Y : Subgroup E} (h : Disjoint X Y) :
    Disjoint (X.map E.subtype) (Y.map E.subtype) := by
  rw [disjoint_iff, ← Subgroup.map_inf _ _ _ E.subtype_injective, disjoint_iff.1 h,
    Subgroup.map_bot]

theorem isCyclic_map_subtype {X : Subgroup E} (h : IsCyclic X) : IsCyclic (X.map E.subtype) :=
  (X.equivMapOfInjective E.subtype E.subtype_injective).isCyclic.1 h

@[simp]
theorem map_subtype_top : (⊤ : Subgroup E).map E.subtype = E := by
  simp [← MonoidHom.range_eq_map]

theorem le_normalizer_map_subtype {X Y : Subgroup E} (h : X ≤ normalizer (Y : Set E)) :
    X.map E.subtype ≤ normalizer ((Y.map E.subtype : Subgroup G) : Set G) := by
  rintro x ⟨n, hn, rfl⟩
  exact mem_normalizer_map_subtype (h hn)

theorem isNilpotent_commutator_subtype (E : Subgroup G)
    (h : Group.IsNilpotent ↥(⁅E, E⁆ : Subgroup G)) :
    Group.IsNilpotent ↥(_root_.commutator ↥E) := by
  have e := (_root_.commutator ↥E).equivMapOfInjective E.subtype E.subtype_injective
  rw [Subgroup.map_subtype_commutator] at e
  exact Group.nilpotent_of_mulEquiv e.symm

end Transfer

theorem piOnePrimes_eq (X : Type*) [Group X] [Finite X] :
    CFSG.FeitThompson.piOnePrimes X = CFSG.FeitThompson.piOnePrimes' X := by
  ext q
  simp only [CFSG.FeitThompson.mem_piOnePrimes_iff, CFSG.FeitThompson.piOnePrimes',
    Set.mem_ofPred_eq, CFSG.FeitThompson.mem_primeDivisorsOf, Nat.mem_primeFactors]
  exact ⟨fun h => ⟨⟨h.1.1, h.1.2.1⟩, h.2⟩, fun h => ⟨⟨h.1.1, h.1.2, Nat.card_pos.ne'⟩, h.2⟩⟩

theorem piTwoPrimes_eq (X : Type*) [Group X] [Finite X] :
    CFSG.FeitThompson.piTwoPrimes X = CFSG.FeitThompson.piTwoPrimes' X := by
  ext q
  simp only [CFSG.FeitThompson.mem_piTwoPrimes_iff, CFSG.FeitThompson.piTwoPrimes',
    Set.mem_ofPred_eq, CFSG.FeitThompson.mem_primeDivisorsOf, Nat.mem_primeFactors]
  exact ⟨fun h => ⟨⟨h.1.1, h.1.2.1⟩, h.2⟩, fun h => ⟨⟨h.1.1, h.1.2, Nat.card_pos.ne'⟩, h.2⟩⟩

theorem piThreePrimes_eq (X : Type*) [Group X] [Finite X] :
    CFSG.FeitThompson.piThreePrimes X = CFSG.FeitThompson.piThreePrimes' X := by
  ext q
  simp only [CFSG.FeitThompson.mem_piThreePrimes_iff, CFSG.FeitThompson.piThreePrimes',
    Set.mem_ofPred_eq, CFSG.FeitThompson.mem_primeDivisorsOf, Nat.mem_primeFactors]
  exact ⟨fun h => ⟨⟨h.1.1, h.1.2.1⟩, h.2⟩, fun h => ⟨⟨h.1.1, h.1.2, Nat.card_pos.ne'⟩, h.2⟩⟩

theorem FNI_sigma_complement_three_factors
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u}) :
    Statements.FNI_sigma_complement_three_factors.{u} := by
  intro G _ _ hG M E hME
  obtain ⟨-, -, -, -, hnil, hπ₁, hπ₂, hπ₃⟩ := FNI_sigma_complement_prime_data h₁ G hG M E hME
  obtain ⟨hM, hsd⟩ := hME
  have hEM : E ≤ M := hsd.right_le
  have hEne : E ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hEM))
  have hEsolv : Group.IsSolvable ↥E := hG.isSolvable_of_ne_top E hEne
  obtain ⟨X₁, X₂, X₃, hX⟩ :=
    exists_isThreePrimeDecomposition ↥E (isNilpotent_commutator_subtype E hnil)
  have hτ₁ : tau1Primes M = CFSG.FeitThompson.piOnePrimes ↥E := by
    rw [piOnePrimes_eq, hπ₁]
  have hτ₂ : tauTwoPrimes M = CFSG.FeitThompson.piTwoPrimes ↥E := by
    rw [piTwoPrimes_eq, hπ₂]
  have hτ₃ : tau3Primes M = CFSG.FeitThompson.piThreePrimes ↥E := by
    rw [piThreePrimes_eq, hπ₃]
  refine ⟨X₁.map E.subtype, X₂.map E.subtype, X₃.map E.subtype,
    ⟨⟨Subgroup.map_subtype_le _, Subgroup.map_subtype_le _, Subgroup.map_subtype_le _, ?_, ?_, ?_,
      ?_, ?_⟩, isCyclic_map_subtype hX.isCyclicOne, isCyclic_map_subtype hX.isCyclicThree, ?_, ?_,
      ?_⟩, ?_⟩
  · rw [subgroupOf_map_subtype, hτ₁, ← isHallSubgroup_iff_isHallPiSubgroup]; exact hX.hallOne
  · rw [subgroupOf_map_subtype, hτ₂, ← isHallSubgroup_iff_isHallPiSubgroup]; exact hX.hallTwo
  · rw [subgroupOf_map_subtype, hτ₃, ← isHallSubgroup_iff_isHallPiSubgroup]; exact hX.hallThree
  · refine ⟨?_, ?_, ?_⟩
    · rw [← Subgroup.map_sup, ← Subgroup.map_sup, hX.isComplementThree.sup_eq_top, map_subtype_top]
    · exact le_normalizer_map_subtype_of_normal hX.normalThree
    · rw [← Subgroup.map_sup]
      exact disjoint_map_subtype hX.isComplementThree.disjoint
  · refine ⟨rfl, ?_, ?_⟩
    · rw [← Subgroup.map_sup]
      exact le_normalizer_map_subtype
        (le_normalizer_of_normal_subgroupOf le_sup_left hX.normalTwo)
    · exact disjoint_map_subtype
        (disjoint_of_disjoint_subgroupOf le_sup_left hX.isComplementTwo.disjoint)
  · rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.map_mono hX.threeLeCommutator
  · rw [← Subgroup.map_sup]
    exact le_normalizer_map_subtype_of_normal hX.normalTwoSupThree
  · have h1 : X₃.map E.subtype ⊓ centralizer (E : Set G)
        = X₃.map E.subtype ⊓ (E ⊓ centralizer (E : Set G)) := by
      rw [← inf_assoc, inf_eq_left.2 (Subgroup.map_subtype_le X₃)]
    rw [h1, inf_centralizer_eq_map_center, ← Subgroup.map_inf _ _ _ E.subtype_injective,
      hX.infCenterThree, Subgroup.map_bot]
  · intro hEbot hX₂bot
    have : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).2 hEbot
    rw [map_subtype_eq_bot_iff] at hX₂bot
    rw [Ne, map_subtype_eq_bot_iff]
    exact hX.ne_bot_one hX₂bot

end

end CFSG.FeitThompson.Proofs
