module

public import CFSG.LieType.Multipliers.CoverWords

public section

namespace CFSG.LieType.Multipliers

open Subgroup CFSG.CosetTable CFSG.Open

variable {m : ℕ}

theorem IsPresentation.of_wordProd_of_card {G : Type*} [Group G] {x y : G}
    (hgen : closure ({x, y} : Set G) = ⊤) {R : List (List (Fin 2 × Bool))}
    (hrel : ∀ v ∈ R.map (List.map fun l => (l.1.val, l.2)),
      CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 x y) v = 1) {N : ℕ}
    (hb : Finite (PG 2 R) ∧ Nat.card (PG 2 R) ≤ N) (hcard : N ≤ Nat.card G) :
    IsPresentation (fun i : Fin 2 => CFSG.Sporadic.Bridge.TwoGen.img2 x y i.val) (wordSet R) := by
  obtain ⟨hfin, hle⟩ := hb
  refine IsPresentation.of_card_le ?_ ?_ (hle.trans hcard)
  · intro r hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    rw [lift_mk_eq_wordProd]
    exact hrel _ (List.mem_map_of_mem hv)
  · rw [← hgen]
    congr 1
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [CFSG.Sporadic.Bridge.TwoGen.img2]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [CFSG.Sporadic.Bridge.TwoGen.img2]⟩
      · exact ⟨1, by simp [CFSG.Sporadic.Bridge.TwoGen.img2]⟩

theorem multiplier_eq_zmod_of_bounds {X : Type} [Group X] {g : Fin m → X}
    {R : List (List (Fin m × Bool))} (hP : IsPresentation g (wordSet R))
    (c : Fin m → List (List (Fin m × Bool) × List (Fin m × Bool)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (c i))) = g i) {p : ℕ}
    [hp : Fact p.Prime] {r : List (Fin m × Bool)} (hr : r ∈ R) {n : ℕ}
    (hfin : Finite (PG m (coverWords R fun i => commWords (c i))))
    (hle : Nat.card (PG m (coverWords R fun i => commWords (c i))) ≤ n)
    (hord : p ∣ orderOf (PresentedGroup.mk
      {r : FreeGroup (Fin m) | r ∈ (coverWords R fun i => commWords (c i)).map FreeGroup.mk}
      (FreeGroup.mk r)))
    (hn : n ≤ p * Nat.card X) :
    Group.IsPerfect X ∧ Nonempty (griessHopfMultiplier X ≃* Multiplicative (ZMod p)) := by
  have hw : ∀ i, FreeGroup.mk (commWords (c i)) ∈ commutator (FreeGroup (Fin m)) :=
    fun i => mk_commWords_mem_commutator _
  refine ⟨isPerfect_of_isPresentation hP hw hwg, ?_⟩
  have hset := coverRelators_wordSet R fun i => commWords (c i)
  set w : Fin m → FreeGroup (Fin m) := fun i => FreeGroup.mk (commWords (c i))
  have key : ∀ S : Set (FreeGroup (Fin m)), wordSet (coverWords R fun i => commWords (c i)) = S →
      S = coverRelators (wordSet R) w →
      Nonempty (griessHopfMultiplier X ≃* Multiplicative (ZMod p)) := by
    rintro S rfl hS
    have : Finite (PresentedCover (wordSet R) w) := by
      rw [PresentedCover, ← hS]; exact hfin
    set π := coverMap hP hwg
    have : Finite X := Finite.of_surjective _ (coverMap_surjective hP hwg)
    have hP' := card_presentedCover hP hw hwg
    have hcard : Nat.card (PresentedCover (wordSet R) w) ≤ p * Nat.card X := by
      rw [PresentedCover, ← hS]; exact hle.trans hn
    have hM : Nat.card (griessHopfMultiplier X) ≤ p := by
      rw [hP', mul_comm] at hcard
      exact Nat.le_of_mul_le_mul_right hcard Nat.card_pos
    have heK := griessHopfMultiplierEquivKer hP hw hwg
    have hord' : p ∣ orderOf (PresentedGroup.mk (coverRelators (wordSet R) w) (FreeGroup.mk r)) := by
      rw [← hS]; exact hord
    set z := PresentedGroup.mk (coverRelators (wordSet R) w) (FreeGroup.mk r)
    have hz : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, coverMap_mk]
      exact hP.lift_eq_one (List.mem_map_of_mem hr)
    have hdvd : p ∣ Nat.card π.ker := by
      refine hord'.trans ?_
      rw [← Subgroup.orderOf_mk z hz]
      exact orderOf_dvd_natCard _
    have hK : Nat.card (griessHopfMultiplier X) = p := by
      rw [Nat.card_congr heK.toEquiv] at hM ⊢
      exact le_antisymm hM (Nat.le_of_dvd Nat.card_pos hdvd)
    exact ⟨mulEquivOfPrimeCardEq hK (by simp [Nat.card_eq_fintype_card])⟩
  exact key _ rfl hset.symm

end CFSG.LieType.Multipliers
