module

public import CFSG.Alternating.Multipliers.Carmichael
public import CFSG.RankThree.PerfectCover.HopfFormula
public meta import CFSG.Alternating.Multipliers.Carmichael
public meta import CFSG.Certificates.CosetTableOrders
public meta import CFSG.LieType.Multipliers.CoverWords
public import Certificates.Certificate2326
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.Alternating.Multipliers

open Subgroup CFSG.LieType.Multipliers CFSG.LocalAnalysis.ComponentInitial CFSG.CosetTable
  CFSG.RankThree.PerfectCover

theorem card_le_of_orderCheck_nil {m : ℕ} {ws : List (List (Fin m × Bool))} {k cap n fuel : ℕ}
    {words : List (List (Fin m × Bool) × ℕ)} (h : orderCheck ws [] k cap n words fuel = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  have hS : subsetOf m [] = [] := by simp [subsetOf]
  have : Finite (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) := by
    rw [hS]
    exact (inferInstance : Finite (PG 0 _))
  have hc : Nat.card (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) = 1 := by
    rw [hS]
    exact card_PG_zero _
  have := card_le_of_subsetCheckShortC ws [] (subsetCheckShortC_of_orderCheck h)
  rwa [hc, mul_one] at this

theorem multiplier_cyclic_of_bounds {m : ℕ} {X : Type} [Group X] {g : Fin m → X}
    {R : List (List (Fin m × Bool))} (hP : IsPresentation g (wordSet R))
    (c : Fin m → List (List (Fin m × Bool) × List (Fin m × Bool)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (c i))) = g i) {N : ℕ}
    {u : List (Fin m × Bool)} (hu : FreeGroup.lift g (FreeGroup.mk u) = 1) {n : ℕ}
    (hfin : Finite (PG m (coverWords R fun i => commWords (c i))))
    (hle : Nat.card (PG m (coverWords R fun i => commWords (c i))) ≤ n)
    (hord : N ∣ orderOf (PresentedGroup.mk
      {r : FreeGroup (Fin m) | r ∈ (coverWords R fun i => commWords (c i)).map FreeGroup.mk}
      (FreeGroup.mk u)))
    (hn : n ≤ N * Nat.card X) :
    IsCyclic (hopfMultiplier X) ∧ Nat.card (hopfMultiplier X) = N := by
  have hw : ∀ i, (fun i => FreeGroup.mk (commWords (c i))) i ∈ commutator (FreeGroup (Fin m)) :=
    fun i => mk_commWords_mem_commutator _
  have hset : wordSet (coverWords R fun i => commWords (c i)) =
      coverRelators (wordSet R) (fun i => FreeGroup.mk (commWords (c i))) :=
    (coverRelators_wordSet R _).symm
  have key : ∀ S : Set (FreeGroup (Fin m)), wordSet (coverWords R fun i => commWords (c i)) = S →
      Finite (PresentedGroup S) ∧ Nat.card (PresentedGroup S) ≤ n ∧
        N ∣ orderOf (PresentedGroup.mk S (FreeGroup.mk u)) := by
    rintro S rfl
    exact ⟨hfin, hle, hord⟩
  obtain ⟨hfin', hle', hord'⟩ := key _ hset
  have : Finite (PresentedCover (wordSet R) (fun i => FreeGroup.mk (commWords (c i)))) := hfin'
  have hX : Finite X := Finite.of_surjective _ (coverMap_surjective hP hwg)
  have eK := hopfMultiplierEquivKer hP hw hwg
  have hcard : Nat.card (PresentedCover (wordSet R) (fun i => FreeGroup.mk (commWords (c i)))) =
      Nat.card X * Nat.card (coverMap hP hwg).ker := by
    rw [(coverMap hP hwg).ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        (coverMap_surjective hP hwg)).toEquiv]
  have hKle : Nat.card (coverMap hP hwg).ker ≤ N := by
    have h1 : Nat.card X * Nat.card (coverMap hP hwg).ker ≤ Nat.card X * N := by
      rw [← hcard, mul_comm (Nat.card X)]
      exact hle'.trans hn
    exact Nat.le_of_mul_le_mul_left h1 Nat.card_pos
  set z := PresentedGroup.mk (coverRelators (wordSet R) (fun i => FreeGroup.mk (commWords (c i))))
    (FreeGroup.mk u)
  have hz : z ∈ (coverMap hP hwg).ker := by
    rw [MonoidHom.mem_ker, coverMap_mk]
    exact hu
  have hdvd : orderOf z ∣ Nat.card (coverMap hP hwg).ker := Subgroup.orderOf_dvd_natCard _ hz
  have hKpos : 0 < Nat.card (coverMap hP hwg).ker := Nat.card_pos
  have hNo : N ≤ orderOf z :=
    Nat.le_of_dvd (orderOf_pos_iff.mpr (isOfFinOrder_of_finite z)) hord'
  have hle2 := Nat.le_of_dvd hKpos hdvd
  have hoK : orderOf z = Nat.card (coverMap hP hwg).ker := by omega
  have hcyc : IsCyclic (coverMap hP hwg).ker :=
    isCyclic_of_orderOf_eq_card ⟨z, hz⟩ (by rw [Subgroup.orderOf_mk]; exact hoK)
  refine ⟨isCyclic_of_surjective eK.symm.toMonoidHom eK.symm.surjective, ?_⟩
  rw [Nat.card_congr eK.toEquiv]
  omega

theorem multiplier_cyclic_of_orderCheck {m : ℕ} {X : Type} [Group X] {g : Fin m → X}
    {R : List (List (Fin m × Bool))} (hP : IsPresentation g (wordSet R))
    (c : Fin m → List (List (Fin m × Bool) × List (Fin m × Bool)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (c i))) = g i) {N : ℕ} (hN : 0 < N)
    {u : List (Fin m × Bool)} (hu : FreeGroup.lift g (FreeGroup.mk u) = 1) {k cap n fuel : ℕ}
    (h : orderCheck (coverWords R fun i => commWords (c i)) [] k cap n [(u, N)] fuel = true)
    (hn : n ≤ N * Nat.card X) :
    IsCyclic (hopfMultiplier X) ∧ Nat.card (hopfMultiplier X) = N :=
  multiplier_cyclic_of_bounds hP c hwg hu (card_le_of_orderCheck_nil h).1
    (card_le_of_orderCheck_nil h).2 (dvd_orderOf_of_orderCheck h (List.mem_singleton_self _) hN) hn

theorem lift_carmichaelRel01 (m : ℕ) :
    FreeGroup.lift (altThreeCycle (n := m + 2)) (FreeGroup.mk (carmichaelRel01 m)) = 1 :=
  (mk_sq _ 0 1).trans (altThreeCycle_mul_sq (by simp))

theorem carmichaelPairs_eval_three :
    ∀ i, FreeGroup.lift altThreeCycle (FreeGroup.mk (commWords (carmichaelPairs 3 i))) =
      altThreeCycle (n := 3) i := by
  intro i
  rw [FreeGroup.lift_mk]
  revert i
  decide

theorem carmichaelPairs_eval_four :
    ∀ i, FreeGroup.lift altThreeCycle (FreeGroup.mk (commWords (carmichaelPairs 4 i))) =
      altThreeCycle (n := 4) i := by
  intro i
  rw [FreeGroup.lift_mk]
  revert i
  decide

theorem carmichaelPairs_eval_five :
    ∀ i, FreeGroup.lift altThreeCycle (FreeGroup.mk (commWords (carmichaelPairs 5 i))) =
      altThreeCycle (n := 5) i := by
  intro i
  rw [FreeGroup.lift_mk]
  revert i
  decide

theorem cover_bounds_five :
    Finite (PG 3 (coverWords (carmichaelWords 3) fun i => commWords (carmichaelPairs 3 i))) ∧
      Nat.card (PG 3 (coverWords (carmichaelWords 3) fun i => commWords (carmichaelPairs 3 i))) ≤
        120 ∧
      2 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ (coverWords (carmichaelWords 3)
        fun i => commWords (carmichaelPairs 3 i)).map FreeGroup.mk}
        (FreeGroup.mk (carmichaelRel01 1))) :=
  Certificates.certificate2326.1

theorem cover_bounds_six :
    Finite (PG 4 (coverWords (carmichaelWords 4) fun i => commWords (carmichaelPairs 4 i))) ∧
      Nat.card (PG 4 (coverWords (carmichaelWords 4) fun i => commWords (carmichaelPairs 4 i))) ≤
        2160 ∧
      6 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ (coverWords (carmichaelWords 4)
        fun i => commWords (carmichaelPairs 4 i)).map FreeGroup.mk}
        (FreeGroup.mk (carmichaelRel01 2))) :=
  Certificates.certificate2326.2.1

theorem cover_bounds_seven :
    Finite (PG 5 (coverWords (carmichaelWords 5) fun i => commWords (carmichaelPairs 5 i))) ∧
      Nat.card (PG 5 (coverWords (carmichaelWords 5) fun i => commWords (carmichaelPairs 5 i))) ≤
        15120 ∧
      6 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 5) | r ∈ (coverWords (carmichaelWords 5)
        fun i => commWords (carmichaelPairs 5 i)).map FreeGroup.mk}
        (FreeGroup.mk (carmichaelRel01 3))) :=
  Certificates.certificate2326.2.2

theorem nat_card_alternatingGroup_fin (k : ℕ) :
    Nat.card (alternatingGroup (Fin (k + 2))) = (k + 2).factorial / 2 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin (k + 2)), Fintype.card_fin]

theorem hopfMultiplier_alternatingGroup_five :
    IsCyclic (hopfMultiplier (alternatingGroup (Fin 5))) ∧
      Nat.card (hopfMultiplier (alternatingGroup (Fin 5))) = 2 :=
  multiplier_cyclic_of_bounds (isPresentation_carmichael 3) (carmichaelPairs 3)
    carmichaelPairs_eval_three (lift_carmichaelRel01 1) cover_bounds_five.1
    cover_bounds_five.2.1 cover_bounds_five.2.2
    (by rw [nat_card_alternatingGroup_fin]; decide)

theorem hopfMultiplier_alternatingGroup_six :
    IsCyclic (hopfMultiplier (alternatingGroup (Fin 6))) ∧
      Nat.card (hopfMultiplier (alternatingGroup (Fin 6))) = 6 :=
  multiplier_cyclic_of_bounds (isPresentation_carmichael 4) (carmichaelPairs 4)
    carmichaelPairs_eval_four (lift_carmichaelRel01 2) cover_bounds_six.1
    cover_bounds_six.2.1 cover_bounds_six.2.2
    (by rw [nat_card_alternatingGroup_fin]; decide)

theorem hopfMultiplier_alternatingGroup_seven :
    IsCyclic (hopfMultiplier (alternatingGroup (Fin 7))) ∧
      Nat.card (hopfMultiplier (alternatingGroup (Fin 7))) = 6 :=
  multiplier_cyclic_of_bounds (isPresentation_carmichael 5) (carmichaelPairs 5)
    carmichaelPairs_eval_five (lift_carmichaelRel01 3) cover_bounds_seven.1
    cover_bounds_seven.2.1 cover_bounds_seven.2.2
    (by rw [nat_card_alternatingGroup_fin]; decide)

end CFSG.Alternating.Multipliers
