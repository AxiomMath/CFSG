module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldCTGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2SwapMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalGroups.Orthogonal (eichler)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived
  matrixDerived matrixProjectiveProjection)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus plusIndexEquiv minusIndexEquiv regular_coordinateQuadMinus)
open CFSG.SeitzReduction.SymplecticPilot (planeCoords planeOf suppGL)

section Transport

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem iSup_perfectCore_centralizer_eq_top_of_mulEquiv {M : Type*} [Group M] {n f : ℕ}
    (hn : 4 ≤ n) (hFf : Nat.card F = 2 ^ f) (hF : 4 ≤ Nat.card F)
    (e : M ≃* matrixProjectiveDerived (coordinateQuadPlus n F)) {ι' : Type*}
    (H : ι' → Subgroup M)
    (hH : ∀ j : Fin n, ∃ y, rationalNode (K := F) (by omega : 1 ≤ n) j ≤
      centralizer (((H y).map e.toMonoidHom : Subgroup _) :
        Set (matrixProjectiveDerived (coordinateQuadPlus n F)))) :
    ⨆ y, perfectCore (centralizer (H y : Set M)) = ⊤ := by
  refine eq_top_iff.2 ?_
  have htop : (⊤ : Subgroup M) =
      (⨆ j, rationalNode (K := F) (by omega : 1 ≤ n) j).map e.symm.toMonoidHom := by
    rw [iSup_rationalNode (K := F) hn hFf hF, Subgroup.map_top_of_surjective _ e.symm.surjective]
  rw [htop, Subgroup.map_iSup]
  refine iSup_le fun j => ?_
  obtain ⟨y, hy⟩ := hH j
  refine (le_perfectCore_of_perfect ?_ ?_).trans
    (le_iSup (fun y => perfectCore (centralizer (H y : Set M))) y)
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    intro h hh
    have hc := mem_centralizer_iff.1 (hy hx) (e h) ⟨h, hh, rfl⟩
    apply e.injective
    simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
    exact hc
  · rw [← Subgroup.map_commutator, commutator_rationalNode (by omega) hF j]

end Transport

section Coords

variable {K : Type} [Field K] {r : ℕ}

@[expose] def minusPlaneCoords (hn : 1 ≤ r + 1) (P : Finset (Fin r)) : Set (Fin (2 * (r + 1))) :=
  {i | ∃ l ∈ P, i = minusIndexEquiv (r + 1) hn (.inl l) ∨
    i = minusIndexEquiv (r + 1) hn (.inr (.inl l))}

@[expose] def anisoCoordSet (hn : 1 ≤ r + 1) : Set (Fin (2 * (r + 1))) :=
  {anisoCoordLeft (n := r + 1) hn, anisoCoordRight (n := r + 1) hn}

theorem dual_coordinateQuadMinus [CharP K 2] (hn : 1 ≤ r + 1) {b c : K} (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {C : Set (Fin (2 * (r + 1)))}
    (hC : ∀ l : Fin r, minusIndexEquiv (r + 1) hn (.inl l) ∈ C ↔
      minusIndexEquiv (r + 1) hn (.inr (.inl l)) ∈ C)
    (hCa : anisoCoordLeft (n := r + 1) hn ∈ C ↔ anisoCoordRight (n := r + 1) hn ∈ C) :
    ∀ a, a ∉ C → ∃ a', a' ∉ C ∧ ∃ β : K, β ≠ 0 ∧
      ∀ v, polar (coordinateQuadMinus (r + 1) K hn b c) (Pi.single a' 1) v = β * v a := by
  intro a ha
  obtain ⟨s, rfl⟩ := (minusIndexEquiv (r + 1) hn).surjective a
  have hA := isAnisoCoord_coordinateQuadMinus (K := K) hn hirr
  rcases s with l | l | l
  · exact ⟨_, fun h => ha ((hC l).2 h), 1, one_ne_zero,
      (isHypCoord_coordinateQuadMinus hn b c l).dual_left⟩
  · exact ⟨_, fun h => ha ((hC l).1 h), 1, one_ne_zero,
      (isHypCoord_coordinateQuadMinus hn b c l).dual_right⟩
  · obtain rfl | rfl : l = 0 ∨ l = 1 := by fin_cases l <;> simp
    · exact ⟨anisoCoordRight (n := r + 1) hn, fun h => ha (hCa.2 h), b, hb, hA.polar_right⟩
    · exact ⟨anisoCoordLeft (n := r + 1) hn, fun h => ha (hCa.1 h), b, hb, hA.polar_left⟩

end Coords

section MinusK

variable {K : Type} [Field K] [CharP K 2] {r : ℕ}

theorem anisoTorus_le_suppBar (hn : 1 ≤ r + 1) {b c : K} (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    anisoTorus (K := K) hn b c ≤
      suppBar (coordinateQuadMinus (r + 1) K hn b c) (anisoCoordSet hn) := by
  refine (anisoTorusOf_le_fixVecBar (Q := coordinateQuadMinus (r + 1) K hn b c)
    (anisoCoord_ne hn) b c).trans (fixVecBar_le_suppBar (fun x hx => ⟨?_, ?_⟩)
      (dual_coordinateQuadMinus hn hb hirr (fun l => ?_) ?_))
  · exact Pi.single_eq_of_ne (M := fun _ => K) (fun h => hx (Or.inl h.symm)) 1
  · exact Pi.single_eq_of_ne (M := fun _ => K) (fun h => hx (Or.inr h.symm)) 1
  · have h1 : minusIndexEquiv (r + 1) hn (.inl l) ∉ anisoCoordSet hn := by
      rintro (h | h) <;> have := (minusIndexEquiv (r + 1) hn).injective h <;> simp at this
    have h2 : minusIndexEquiv (r + 1) hn (.inr (.inl l)) ∉ anisoCoordSet hn := by
      rintro (h | h) <;> have := (minusIndexEquiv (r + 1) hn).injective h <;> simp at this
    exact iff_of_false h1 h2
  · exact iff_of_true (Or.inl rfl) (Or.inr rfl)

variable (r) in
@[expose] def lowSplit : Finset (Fin r) := Finset.univ.filter fun x => x.val < 2

theorem mem_lowSplit {x : Fin r} : x ∈ lowSplit r ↔ x.val < 2 := by simp [lowSplit]

@[expose] noncomputable def minusSwapVec (hn : 1 ≤ r + 1) (hr : 2 ≤ r) (c : K) :
    Bool → Fin (2 * (r + 1)) → K
  | false => Pi.single (minusIndexEquiv (r + 1) hn (.inl ⟨0, by omega⟩)) 1 +
      Pi.single (minusIndexEquiv (r + 1) hn (.inr (.inl ⟨0, by omega⟩))) 1
  | true => Pi.single (minusIndexEquiv (r + 1) hn (.inr (.inl ⟨0, by omega⟩))) 1 +
      Pi.single (minusIndexEquiv (r + 1) hn (.inl ⟨1, by omega⟩)) 1 +
      c • Pi.single (minusIndexEquiv (r + 1) hn (.inr (.inl ⟨1, by omega⟩))) 1

theorem minusPlaneSwap_data (hn : 1 ≤ r + 1) (hr : 2 ≤ r) {c : K}
    (hirr : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0) :
    PlaneSwapData (coordinateQuadMinus (r + 1) K hn 1 c)
      (Pi.single (anisoCoordLeft (n := r + 1) hn) 1) (Pi.single (anisoCoordRight (n := r + 1) hn) 1)
      (minusSwapVec hn hr c false) (minusSwapVec hn hr c true) := by
  have hA := isAnisoCoord_coordinateQuadMinus (K := K) hn hirr
  have hi := isHypCoord_coordinateQuadMinus (K := K) hn 1 c ⟨0, by omega⟩
  have hj := isHypCoord_coordinateQuadMinus (K := K) hn 1 c ⟨1, by omega⟩
  have hd : PairDisjoint (minusIndexEquiv (r + 1) hn (.inl ⟨0, by omega⟩))
      (minusIndexEquiv (r + 1) hn (.inr (.inl ⟨0, by omega⟩)))
      (minusIndexEquiv (r + 1) hn (.inl ⟨1, by omega⟩))
      (minusIndexEquiv (r + 1) hn (.inr (.inl ⟨1, by omega⟩))) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> have := (minusIndexEquiv (r + 1) hn).injective h <;>
      simp at this
  obtain ⟨t1, t2, -, -, t5, -, -, -, -, -⟩ := triPlanes_data hi hj hd c
  have e : ∀ (x : Fin r ⊕ Fin r) (y : Fin 2),
      (Pi.single (minusIndexEquiv (r + 1) hn (Sum.elim Sum.inl (fun l => Sum.inr (Sum.inl l)) x))
        (1 : K) : Fin (2 * (r + 1)) → K) (minusIndexEquiv (r + 1) hn (.inr (.inr y))) = 0 := by
    intro x y
    refine Pi.single_eq_of_ne (fun h => ?_) 1
    have := (minusIndexEquiv (r + 1) hn).injective h
    rcases x with x | x <;> simp at this
  have eL : ∀ k : Fin r, (Pi.single (minusIndexEquiv (r + 1) hn (.inl k)) (1 : K) :
      Fin (2 * (r + 1)) → K) (anisoCoordLeft (n := r + 1) hn) = 0 := fun k => e (.inl k) 0
  have eL' : ∀ k : Fin r, (Pi.single (minusIndexEquiv (r + 1) hn (.inr (.inl k))) (1 : K) :
      Fin (2 * (r + 1)) → K) (anisoCoordLeft (n := r + 1) hn) = 0 := fun k => e (.inr k) 0
  have eR : ∀ k : Fin r, (Pi.single (minusIndexEquiv (r + 1) hn (.inl k)) (1 : K) :
      Fin (2 * (r + 1)) → K) (anisoCoordRight (n := r + 1) hn) = 0 := fun k => e (.inl k) 1
  have eR' : ∀ k : Fin r, (Pi.single (minusIndexEquiv (r + 1) hn (.inr (.inl k))) (1 : K) :
      Fin (2 * (r + 1)) → K) (anisoCoordRight (n := r + 1) hn) = 0 := fun k => e (.inr k) 1
  have hRR : (Pi.single (anisoCoordRight (n := r + 1) hn) (1 : K) : Fin (2 * (r + 1)) → K)
      (anisoCoordRight (n := r + 1) hn) = 1 := Pi.single_eq_same _ _
  refine ⟨?_, ?_, ?_, t5, ?_, ?_, ?_, ?_⟩
  · rw [hA.map_left]; exact t1.symm
  · rw [hA.map_right]; exact t2.symm
  · rw [hA.polar_left, hRR, one_mul]
  · rw [hA.polar_left, minusSwapVec, Pi.add_apply, eR, eR', add_zero, mul_zero]
  · rw [hA.polar_left, minusSwapVec, Pi.add_apply, Pi.add_apply, Pi.smul_apply, eR', eR, eR',
      smul_zero, add_zero, add_zero, mul_zero]
  · rw [hA.polar_right, minusSwapVec, Pi.add_apply, eL, eL', add_zero, mul_zero]
  · rw [hA.polar_right, minusSwapVec, Pi.add_apply, Pi.add_apply, Pi.smul_apply, eL', eL, eL',
      smul_zero, add_zero, add_zero, mul_zero]

end MinusK

section MinusConj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}

@[expose] noncomputable def minusSwapLin (hn : 1 ≤ r + 1) (hr : 2 ≤ r) (c : K) :
    (Fin (2 * (r + 1)) → K) ≃ₗ[K] (Fin (2 * (r + 1)) → K) :=
  eichler (coordinateQuadMinus (r + 1) K hn 1 c)
    (Pi.single (anisoCoordLeft (n := r + 1) hn) 1 + minusSwapVec hn hr c false)
    (Pi.single (anisoCoordRight (n := r + 1) hn) 1 + minusSwapVec hn hr c true)

theorem minusSwapLin_mem_orthDerived (hn : 1 ≤ r + 1) (hr : 3 ≤ r) {c : K}
    (hirr : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0) :
    minusSwapLin hn (by omega) c ∈ orthDerived (coordinateQuadMinus (r + 1) K hn 1 c) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus (r + 1) K 1 c (by omega) hirr
  exact eichler_mem_orthDerived hQ hT _ _

theorem map_conj_anisoTorus_le_suppBar (hn : 1 ≤ r + 1) (hr : 3 ≤ r) {c : K}
    (hirr : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0) :
    (anisoTorus (K := K) hn 1 c).map (MulAut.conj (projHom (coordinateQuadMinus (r + 1) K hn 1 c)
        ⟨minusSwapLin hn (by omega) c, minusSwapLin_mem_orthDerived hn hr hirr⟩)).toMonoidHom ≤
      suppBar (coordinateQuadMinus (r + 1) K hn 1 c) (minusPlaneCoords hn (lowSplit r)) := by
  have hD := minusPlaneSwap_data (K := K) hn (by omega) hirr
  refine (map_mono (anisoTorusOf_le_fixVecBar (Q := coordinateQuadMinus (r + 1) K hn 1 c)
    (anisoCoord_ne hn) 1 c)).trans ?_
  rw [map_conj_fixVecBar]
  have hmem : ∀ l : Fin r, minusIndexEquiv (r + 1) hn (.inl l) ∈ minusPlaneCoords hn (lowSplit r) ↔
      l.val < 2 := by
    intro l
    constructor
    · rintro ⟨l', hl', h | h⟩ <;> have := (minusIndexEquiv (r + 1) hn).injective h <;>
        simp at this
      · rw [this]; exact mem_lowSplit.1 hl'
    · intro h
      exact ⟨l, mem_lowSplit.2 h, Or.inl rfl⟩
  have hmem' : ∀ l : Fin r, minusIndexEquiv (r + 1) hn (.inr (.inl l)) ∈
      minusPlaneCoords hn (lowSplit r) ↔ l.val < 2 := by
    intro l
    constructor
    · rintro ⟨l', hl', h | h⟩ <;> have := (minusIndexEquiv (r + 1) hn).injective h <;>
        simp at this
      · rw [this]; exact mem_lowSplit.1 hl'
    · intro h
      exact ⟨l, mem_lowSplit.2 h, Or.inr rfl⟩
  have hnu : anisoCoordLeft (n := r + 1) hn ∉ minusPlaneCoords hn (lowSplit r) := by
    rintro ⟨l', -, h | h⟩ <;> have := (minusIndexEquiv (r + 1) hn).injective h <;> simp at this
  have hnw : anisoCoordRight (n := r + 1) hn ∉ minusPlaneCoords hn (lowSplit r) := by
    rintro ⟨l', -, h | h⟩ <;> have := (minusIndexEquiv (r + 1) hn).injective h <;> simp at this
  refine fixVecBar_le_suppBar (fun x hx => ?_) (dual_coordinateQuadMinus hn one_ne_zero hirr
    (fun l => by rw [hmem, hmem']) (iff_of_false hnu hnw))
  have ev : ∀ (s t : Fin r ⊕ Fin r ⊕ Fin 2), s ≠ t →
      (Pi.single (minusIndexEquiv (r + 1) hn s) (1 : K) : Fin (2 * (r + 1)) → K)
        (minusIndexEquiv (r + 1) hn t) = 0 :=
    fun s t hst =>
      Pi.single_eq_of_ne (fun h => hst ((minusIndexEquiv (r + 1) hn).injective h).symm) 1
  obtain ⟨s, rfl⟩ := (minusIndexEquiv (r + 1) hn).surjective x
  set i0 : Fin r := ⟨0, by omega⟩
  set i1 : Fin r := ⟨1, by omega⟩
  have hU : anisoCoordLeft (n := r + 1) hn = minusIndexEquiv (r + 1) hn (.inr (.inr 0)) := rfl
  have hW : anisoCoordRight (n := r + 1) hn = minusIndexEquiv (r + 1) hn (.inr (.inr 1)) := rfl
  rcases s with l | l | l
  · have hl : ¬ l.val < 2 := fun h => hx ((hmem l).2 h)
    have h0 : l ≠ i0 := fun h => hl (by rw [h]; simp [i0])
    have h1 : l ≠ i1 := fun h => hl (by rw [h]; simp [i1])
    have hpl := (isHypCoord_coordinateQuadMinus (K := K) hn 1 c l).polar_left
    have hfix : minusSwapLin hn (by omega) c (Pi.single (minusIndexEquiv (r + 1) hn (.inl l)) 1) =
        Pi.single (minusIndexEquiv (r + 1) hn (.inl l)) 1 := by
      refine PlaneSwapData.eichler_of_perp ?_ ?_ ?_ ?_
      · rw [hpl, hU]; exact ev (.inr (.inr 0)) (.inr (.inl l)) (by simp)
      · rw [hpl, hW]; exact ev (.inr (.inr 1)) (.inr (.inl l)) (by simp)
      · rw [hpl, minusSwapVec, Pi.add_apply, ev (.inl i0) (.inr (.inl l)) (by simp),
          ev (.inr (.inl i0)) (.inr (.inl l)) (by simp [Ne.symm h0]), add_zero]
      · rw [hpl, minusSwapVec, Pi.add_apply, Pi.add_apply, Pi.smul_apply,
          ev (.inr (.inl i0)) (.inr (.inl l)) (by simp [Ne.symm h0]),
          ev (.inl i1) (.inr (.inl l)) (by simp),
          ev (.inr (.inl i1)) (.inr (.inl l)) (by simp [Ne.symm h1]), smul_zero, add_zero,
          add_zero]
    refine ⟨_, ⟨?_, ?_⟩, hfix⟩
    · rw [hU]; exact ev (.inl l) (.inr (.inr 0)) (by simp)
    · rw [hW]; exact ev (.inl l) (.inr (.inr 1)) (by simp)
  · have hl : ¬ l.val < 2 := fun h => hx ((hmem' l).2 h)
    have h0 : l ≠ i0 := fun h => hl (by rw [h]; simp [i0])
    have h1 : l ≠ i1 := fun h => hl (by rw [h]; simp [i1])
    have hpr := (isHypCoord_coordinateQuadMinus (K := K) hn 1 c l).polar_right
    have hfix : minusSwapLin hn (by omega) c
        (Pi.single (minusIndexEquiv (r + 1) hn (.inr (.inl l))) 1) =
        Pi.single (minusIndexEquiv (r + 1) hn (.inr (.inl l))) 1 := by
      refine PlaneSwapData.eichler_of_perp ?_ ?_ ?_ ?_
      · rw [hpr, hU]; exact ev (.inr (.inr 0)) (.inl l) (by simp)
      · rw [hpr, hW]; exact ev (.inr (.inr 1)) (.inl l) (by simp)
      · rw [hpr, minusSwapVec, Pi.add_apply, ev (.inl i0) (.inl l) (by simp [Ne.symm h0]),
          ev (.inr (.inl i0)) (.inl l) (by simp), add_zero]
      · rw [hpr, minusSwapVec, Pi.add_apply, Pi.add_apply, Pi.smul_apply,
          ev (.inr (.inl i0)) (.inl l) (by simp), ev (.inl i1) (.inl l) (by simp [Ne.symm h1]),
          ev (.inr (.inl i1)) (.inl l) (by simp), smul_zero, add_zero, add_zero]
    refine ⟨_, ⟨?_, ?_⟩, hfix⟩
    · rw [hU]; exact ev (.inr (.inl l)) (.inr (.inr 0)) (by simp)
    · rw [hW]; exact ev (.inr (.inl l)) (.inr (.inr 1)) (by simp)
  · obtain rfl | rfl : l = 0 ∨ l = 1 := by fin_cases l <;> simp
    · refine ⟨_, ⟨?_, ?_⟩, hD.eichler_right⟩
      · change minusSwapVec hn (by omega) c false (anisoCoordLeft (n := r + 1) hn) = 0
        rw [minusSwapVec, Pi.add_apply, hU, ev (.inl i0) (.inr (.inr 0)) (by simp),
          ev (.inr (.inl i0)) (.inr (.inr 0)) (by simp), add_zero]
      · change minusSwapVec hn (by omega) c false (anisoCoordRight (n := r + 1) hn) = 0
        rw [minusSwapVec, Pi.add_apply, hW, ev (.inl i0) (.inr (.inr 1)) (by simp),
          ev (.inr (.inl i0)) (.inr (.inr 1)) (by simp), add_zero]
    · refine ⟨_, ⟨?_, ?_⟩, hD.eichler_right'⟩
      · change minusSwapVec hn (by omega) c true (anisoCoordLeft (n := r + 1) hn) = 0
        rw [minusSwapVec, Pi.add_apply, Pi.add_apply, Pi.smul_apply, hU,
          ev (.inr (.inl i0)) (.inr (.inr 0)) (by simp), ev (.inl i1) (.inr (.inr 0)) (by simp),
          ev (.inr (.inl i1)) (.inr (.inr 0)) (by simp), smul_zero, add_zero, add_zero]
      · change minusSwapVec hn (by omega) c true (anisoCoordRight (n := r + 1) hn) = 0
        rw [minusSwapVec, Pi.add_apply, Pi.add_apply, Pi.smul_apply, hW,
          ev (.inr (.inl i0)) (.inr (.inr 1)) (by simp), ev (.inl i1) (.inr (.inr 1)) (by simp),
          ev (.inr (.inl i1)) (.inr (.inr 1)) (by simp), smul_zero, add_zero, add_zero]

end MinusConj

section MinusEmbed

open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl inclHom inclHom_val glIncl_val)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)
open CFSG.SeitzReduction.TwistedE6Pilot (isExtension_coordinateQuadMinus)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem minusEqEquiv_mem_suppBar {n : ℕ} (hn : 1 ≤ n) {β β' γ γ' : F} (hβ : β = β')
    (hγ : γ = γ') {C : Set (Fin (2 * n))}
    {x : matrixProjectiveDerived (coordinateQuadMinus n F hn β γ)}
    (hx : x ∈ suppBar (coordinateQuadMinus n F hn β γ) C) :
    minusEqEquiv hn hβ hγ x ∈ suppBar (coordinateQuadMinus n F hn β' γ') C := by
  subst hβ hγ
  exact hx

theorem map_minusFieldEmbed_suppBar_le (ι : K →+* F) {n : ℕ} (hn : 1 ≤ n) (b c : K)
    (C : Set (Fin (2 * n))) :
    (suppBar (coordinateQuadMinus n K hn b c) C).map (minusFieldEmbed ι hn b c) ≤
      suppBar (coordinateQuadMinus n F hn (ι b) (ι c)) C := by
  rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, mem_comap] at hA
  have hQ := coordinateQuadMinus_comp_ringEquiv ι.rangeRestrictFieldEquiv hn b c
  have hB : glCongr ι.rangeRestrictFieldEquiv (A : GL (Fin (2 * n)) K) ∈
      matrixDerived (coordinateQuadMinus n ι.fieldRange hn (ι.rangeRestrictFieldEquiv b)
        (ι.rangeRestrictFieldEquiv c)) := by
    rw [← map_matrixDerived_glCongr ι.rangeRestrictFieldEquiv hQ]
    exact ⟨A, A.2, rfl⟩
  have h1 : minusCongr ι.rangeRestrictFieldEquiv hn b c (matrixProjectiveProjection _ A) =
      matrixProjectiveProjection _ ⟨_, hB⟩ :=
    matrixProjectiveCongr_mk ι.rangeRestrictFieldEquiv hQ A ⟨_, hB⟩ rfl
  have hsupp : ((inclHom ι.fieldRange (isExtension_coordinateQuadMinus ι.fieldRange hn
      (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c)) ⟨_, hB⟩ : matrixDerived _) :
        GL (Fin (2 * n)) F) ∈ suppGL F C := by
    intro a a' haa
    rw [inclHom_val, glIncl_val, Matrix.map_apply]
    change ((ι.rangeRestrictFieldEquiv ((A : GL (Fin (2 * n)) K).val a a') : ι.fieldRange) : F) = _
    have h2 : (A : GL (Fin (2 * n)) K).val a a' =
        (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) K) a a' := hA a a' haa
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have he : minusFieldEmbed ι hn b c (matrixProjectiveProjection _ A) =
      minusEqEquiv hn (RingHom.rangeRestrictFieldEquiv_apply_coe ι b)
        (RingHom.rangeRestrictFieldEquiv_apply_coe ι c)
        (matrixProjectiveProjection _ (inclHom ι.fieldRange (isExtension_coordinateQuadMinus
          ι.fieldRange hn (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c))
          ⟨_, hB⟩)) := by
    rw [minusFieldEmbed, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, h1]
    rfl
  rw [he]
  exact minusEqEquiv_mem_suppBar _ _ _ ⟨_, hsupp, rfl⟩

variable {r : ℕ}

theorem minusPlusProjEquiv_mk (hn : 1 ≤ r + 1) {α β γ : F} (hα : α ^ 2 + β * α + γ = 0)
    (hαα : α ≠ -β - α) (A : matrixDerived (coordinateQuadMinus (r + 1) F hn β γ)) :
    minusPlusProjEquiv hn hα hαα (matrixProjectiveProjection _ A) =
      projHom _ (orthDerivedCongr (minusPlusIsometry hn hα hαα) (derivedEquiv _ A)) := by
  rw [← projHom_derivedEquiv, minusPlusProjEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply]
  erw [MulEquiv.symm_apply_apply]
  rfl

theorem minusPlusProjEquiv_mem_suppBar (hn : 1 ≤ r + 1) {α β γ : F}
    (hα : α ^ 2 + β * α + γ = 0) (hαα : α ≠ -β - α) {C : Set (Fin (2 * (r + 1)))}
    {P : Finset (Fin (r + 1))}
    (hM : ∀ z : Fin (2 * (r + 1)) → F, (∀ i ∈ plusIndexEquiv (r + 1) '' planeCoords P,
      minusPlusLin hn α (-β - α) z i = 0) → ∀ i ∈ C, z i = 0)
    {x : matrixProjectiveDerived (coordinateQuadMinus (r + 1) F hn β γ)}
    (hx : x ∈ suppBar (coordinateQuadMinus (r + 1) F hn β γ) C) :
    minusPlusProjEquiv hn hα hαα x ∈
      suppBar (coordinateQuadPlus (r + 1) F) (plusIndexEquiv (r + 1) '' planeCoords P) := by
  obtain ⟨A, hA, rfl⟩ := hx
  rw [minusPlusProjEquiv_mk]
  exact projHom_orthDerivedCongr_mem_suppBar _ hM (dual_coordinateQuadPlus P) hA

theorem minusPlusLin_hM_aniso (hn : 1 ≤ r + 1) {α α' : F} (hαα : α ≠ α') (z : Fin (2 * (r + 1)) → F)
    (hz : ∀ i ∈ plusIndexEquiv (r + 1) '' planeCoords (Finset.univ.filter fun x : Fin (r + 1) =>
      x.val = r), minusPlusLin hn α α' z i = 0) :
    ∀ i ∈ anisoCoordSet hn, z i = 0 := by
  have hu := hz _ ⟨.inl (Fin.last r), by simp [SymplecticPilot.mem_planeCoords], rfl⟩
  have hw := hz _ ⟨.inr (Fin.last r), by simp [SymplecticPilot.mem_planeCoords], rfl⟩
  rw [minusPlusLin_inl_last] at hu
  rw [minusPlusLin_inr_last] at hw
  have hw0 : z (minusIndexEquiv (r + 1) hn (.inr (.inr 1))) = 0 := by
    have h1 : (α' - α) * z (minusIndexEquiv (r + 1) hn (.inr (.inr 1))) = 0 := by
      linear_combination hu - hw
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hαα
    · exact h
  have hu0 : z (minusIndexEquiv (r + 1) hn (.inr (.inr 0))) = 0 := by
    rw [hw0, mul_zero, sub_zero] at hu
    exact hu
  rintro i (rfl | rfl)
  · exact hu0
  · exact hw0

theorem minusPlusLin_hM_low (hn : 1 ≤ r + 1) (α α' : F) (z : Fin (2 * (r + 1)) → F)
    (hz : ∀ i ∈ plusIndexEquiv (r + 1) '' planeCoords (Finset.univ.filter fun x : Fin (r + 1) =>
      x.val < 2), minusPlusLin hn α α' z i = 0) :
    ∀ i ∈ minusPlaneCoords hn (lowSplit r), z i = 0 := by
  rintro i ⟨l, hl, rfl | rfl⟩
  · have hl' := mem_lowSplit.1 hl
    have h := hz _ ⟨.inl l.castSucc, by
      rw [SymplecticPilot.mem_planeCoords, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa using hl'⟩, rfl⟩
    rwa [minusPlusLin_inl_castSucc] at h
  · have hl' := mem_lowSplit.1 hl
    have h := hz _ ⟨.inr l.castSucc, by
      rw [SymplecticPilot.mem_planeCoords, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa using hl'⟩, rfl⟩
    rwa [minusPlusLin_inr_castSucc] at h

end MinusEmbed

section MinusGen

variable {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem iSup_perfectCore_centralizer_anisoTorus_eq_top {r f : ℕ} (hr : 5 ≤ r) {c : K}
    (hirr : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0) (ι : K →+* F) {α : F}
    (hα : α ^ 2 + ι 1 * α + ι c = 0) (hαα : α ≠ -ι 1 - α) (hFf : Nat.card F = 2 ^ f)
    (hF : 4 ≤ Nat.card F) :
    ⨆ y : matrixProjectiveDerived (coordinateQuadMinus (r + 1) K (by omega) 1 c),
      perfectCore (centralizer ((((anisoTorus (K := K) (by omega) 1 c).map
        (MulAut.conj y).toMonoidHom).map (minusFieldEmbed ι (by omega) 1 c) :
          Subgroup (matrixProjectiveDerived
            (coordinateQuadMinus (r + 1) F (by omega) (ι 1) (ι c)))) :
        Set (matrixProjectiveDerived (coordinateQuadMinus (r + 1) F (by omega) (ι 1) (ι c))))) =
      ⊤ := by
  have hn : 1 ≤ r + 1 := by omega
  refine iSup_perfectCore_centralizer_eq_top_of_mulEquiv (by omega) hFf hF
    (minusPlusProjEquiv hn hα hαα) _ fun j => ?_
  by_cases hj : j.val + 2 ≤ r
  · refine ⟨1, rationalNode_le_centralizer_of_le_suppBar _ j
      (P := Finset.univ.filter fun x : Fin (r + 1) => x.val = r) ?_ ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_plusNodeSet] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
      omega
    · rintro _ ⟨x, hx, rfl⟩
      rw [map_conj_one_eq] at hx
      exact minusPlusProjEquiv_mem_suppBar hn hα hαα (minusPlusLin_hM_aniso hn hαα)
        (map_minusFieldEmbed_suppBar_le ι hn 1 c _
          (map_mono (anisoTorus_le_suppBar hn one_ne_zero hirr) hx))
  · refine ⟨projHom _ ⟨minusSwapLin hn (by omega) c,
        minusSwapLin_mem_orthDerived hn (by omega) hirr⟩,
      rationalNode_le_centralizer_of_le_suppBar _ j
        (P := Finset.univ.filter fun x : Fin (r + 1) => x.val < 2) ?_ ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_plusNodeSet] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
      omega
    · rintro _ ⟨x, hx, rfl⟩
      exact minusPlusProjEquiv_mem_suppBar hn hα hαα (minusPlusLin_hM_low hn _ _)
        (map_minusFieldEmbed_suppBar_le ι hn 1 c _
          (map_mono (map_conj_anisoTorus_le_suppBar hn (by omega) hirr) hx))

theorem omegaMinusTwoFieldGenInput_holds : OmegaMinusTwoFieldGenInput := by
  intro n hn K _ _ _ b c hirr hK2 F _ _ _ ι hF4
  obtain rfl : b = 1 := eq_one_of_ne_zero_of_card_two hK2 (coeff_ne_zero_of_irreducible' hirr)
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  obtain ⟨α, hα⟩ := exists_root_of_card_eq_sq ι (by rw [hF4, hK2]; norm_num) hirr
  have hb0 : ι 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
  exact iSup_perfectCore_centralizer_anisoTorus_eq_top (f := 2) (by omega) hirr ι hα
    (root_ne_other_of_ne_zero hb0) (by rw [hF4]; norm_num) (by omega)

end MinusGen

end CFSG.SeitzReduction.OmegaPilot
