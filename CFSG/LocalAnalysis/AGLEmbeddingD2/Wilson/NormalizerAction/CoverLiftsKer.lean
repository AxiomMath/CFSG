module

public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestCover

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open scoped commutatorElement

theorem exists_lifts_closure {X S : Type*} [Group X] [Group S] [Finite X]
    [Group.IsPerfect X] {π : X →* S} (hπ : Function.Surjective π) (hker : π.ker ≤ center X)
    (hp : IsPGroup 3 π.ker) {m : ℕ} (h : Fin m → S) (e : Fin m → ℕ)
    (cw : Fin m → List (Fin m × Bool) × List (Fin m × Bool))
    (he : ∀ i, e i ≠ 0 → h i ^ e i = 1 ∧ Nat.Coprime 3 (e i))
    (hc : ∀ i, e i = 0 → h i = ⁅evalW h (cw i).1, evalW h (cw i).2⁆)
    (rels : List (List (Fin m × Bool))) (hrels : ∀ w ∈ rels, evalW h w = 1)
    (hidx : ¬ 3 ∣ (closure (Set.range h)).index)
    (hfin : Finite (PG m (gammaWords e cw rels))) :
    ∃ k : Fin m → X, (∀ i, π (k i) = h i) ∧
      (∀ w ∈ gammaWords e cw rels, evalW k w = 1) ∧
      π.ker ≤ closure (Set.range k) ∧
      (closure (Set.range k)).map π = closure (Set.range h) ∧
      Nat.card (closure (Set.range k)) =
        Nat.card (closure (Set.range h)) * Nat.card π.ker ∧
      Nat.card (closure (Set.range k)) ≤ Nat.card (PG m (gammaWords e cw rels)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ĥ := lifts hπ hker hp h e cw he
  set H := closure (Set.range h)
  set Ĥ := closure (Set.range ĥ)
  have hmap : ∀ i, π (ĥ i) = h i := map_lifts hπ hker hp h e cw he hc
  let φ : PG m (gammaWords e cw rels) →* X :=
    PresentedGroup.toGroup (lifts_rels hπ hker hp h e cw he hc rels hrels)
  have hφ : φ.range = Ĥ := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 2
    funext i
    exact PresentedGroup.toGroup.of _
  have hcardĤ : Nat.card Ĥ ≤ Nat.card (PG m (gammaWords e cw rels)) := by
    rw [← hφ]
    exact Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  have hmapĤ : Ĥ.map π = H := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    congr 2
    funext i
    exact hmap i
  have hkerĤ : π.ker ≤ Ĥ := by
    set H' := H.comap π
    have hidx' : ¬ 3 ∣ H'.index := by rw [H.index_comap_of_surjective hπ]; exact hidx
    obtain ⟨Q⟩ : Nonempty (Sylow 3 H') := inferInstance
    have hQp : IsPGroup 3 ((Q : Subgroup H').map H'.subtype) :=
      Q.isPGroup'.map H'.subtype
    have hQi : ¬ 3 ∣ ((Q : Subgroup H').map H'.subtype).index := by
      rw [Subgroup.index_map_subtype, Nat.Prime.dvd_mul Fact.out]
      exact not_or.mpr ⟨Q.not_dvd_index, hidx'⟩
    set P : Sylow 3 X := hQp.toSylow hQi
    have hPH' : (P : Subgroup X) ≤ H' := by
      rw [IsPGroup.toSylow_coe]
      exact Subgroup.map_subtype_le _
    refine (CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P π.ker hker
      hp).trans ?_
    rw [map_le_iff_le_comap, _root_.commutator_def, commutator_le]
    intro a _ b _
    rw [mem_comap, map_commutatorElement, coe_subtype]
    have hdecomp : ∀ x : X, x ∈ H' → ∃ y ∈ Ĥ, ∃ z ∈ center X, x = y * z := by
      intro x hx
      have hx' : π x ∈ Ĥ.map π := by rw [hmapĤ]; exact hx
      obtain ⟨y, hy, hyx⟩ := mem_map.mp hx'
      refine ⟨y, hy, y⁻¹ * x, hker ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    obtain ⟨ya, hya, za, hza, ha⟩ := hdecomp a (hPH' a.2)
    obtain ⟨yb, hyb, zb, hzb, hb⟩ := hdecomp b (hPH' b.2)
    rw [ha, hb, commutatorElement_mul_center_left hza, commutatorElement_mul_center_right hzb,
      commutatorElement_def]
    exact Ĥ.mul_mem (Ĥ.mul_mem (Ĥ.mul_mem hya hyb) (Ĥ.inv_mem hya)) (Ĥ.inv_mem hyb)
  have hsurj : Function.Surjective (π.subgroupMap Ĥ) := π.subgroupMap_surjective Ĥ
  have hk : (π.subgroupMap Ĥ).ker = π.ker.subgroupOf Ĥ := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      exact Subtype.ext hx
  have hcard : Nat.card Ĥ = Nat.card (Ĥ.map π) * Nat.card (π.subgroupMap Ĥ).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (π.subgroupMap Ĥ).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv]
  rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerĤ).toEquiv, hmapĤ] at hcard
  refine ⟨ĥ, hmap, ?_, hkerĤ, hmapĤ, hcard, hcardĤ⟩
  intro w hw
  have := lifts_rels hπ hker hp h e cw he hc rels hrels
    (FreeGroup.mk w) (List.mem_map_of_mem hw)
  rwa [lift_mk_eq_evalW] at this

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
