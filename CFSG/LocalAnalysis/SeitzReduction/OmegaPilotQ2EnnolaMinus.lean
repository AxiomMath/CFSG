module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaBlock
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAniso

public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateQuadPlus minusIndexEquiv plusIndexEquiv regular_coordinateQuadMinus)
open CFSG.Quasithin (perfectCore)

section Param

theorem exists_ennolaParam {K F : Type} [Field K] [Finite K] [CharP K 2] (hK2 : Nat.card K = 2)
    [Field F] [Finite F] (hF : Nat.card F = 4) {σ : F ≃+* F} (hσ : orderOf σ = 2)
    {k₀ : Subfield F} (hσk : ∀ x, x ∈ k₀ ↔ σ x = x) (φ : K ≃+* k₀) :
    ∃ E : EnnolaParam K F, ∀ p, E.ι p = ((φ p : k₀) : F) := by
  set ι : K →+* F := k₀.subtype.comp φ.toRingHom with hι
  have hιp : ∀ p, ι p = ((φ p : k₀) : F) := fun _ => rfl
  have two : ∀ p : K, p = 0 ∨ p = 1 := fun p => by
    by_cases hp : p = 0
    · exact Or.inl hp
    · refine Or.inr ?_
      have := Fintype.ofFinite K
      have h := FiniteField.pow_card p
      rw [Fintype.card_eq_nat_card, hK2, _root_.sq] at h
      exact mul_left_cancel₀ hp (by rw [h, mul_one])
  obtain ⟨ω, hω⟩ : ∃ ω, σ ω ≠ ω := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h1 : σ = 1 := RingEquiv.ext h
    rw [h1, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hωι : ∀ p, ι p ≠ ω := fun p hp => hω ((hσk ω).1 (hp ▸ (φ p).2))
  have hinj : Function.Injective fun z : K × K => ι z.1 + ι z.2 * ω := by
    rintro ⟨p, s⟩ ⟨p', s'⟩ h
    simp only at h
    by_cases hs : s = s'
    · subst hs
      have : ι p = ι p' := by linear_combination h
      exact Prod.ext (ι.injective this) rfl
    · exfalso
      have hs' : ι s - ι s' ≠ 0 := by
        rw [sub_ne_zero]
        exact fun h' => hs (ι.injective h')
      apply hωι ((p' - p) / (s - s'))
      rw [map_div₀, map_sub, map_sub, div_eq_iff hs']
      linear_combination -h
  have hbij : Function.Bijective fun z : K × K => ι z.1 + ι z.2 * ω :=
    hinj.bijective_of_nat_card_le (by rw [hF, Nat.card_prod, hK2])
  have h2F : (2 : F) = 0 := by rw [← map_ofNat ι 2, CharTwo.two_eq_zero, map_zero]
  have hsq : ω * ω = ω + 1 := by
    obtain ⟨⟨p, s⟩, hps⟩ := hbij.2 (ω * ω)
    simp only at hps
    have hω0 : ω ≠ 0 := fun h0 => hωι 0 (by rw [map_zero, h0])
    have hω1 : ω ≠ 1 := fun h1 => hωι 1 (by rw [map_one, h1])
    rcases two p with rfl | rfl <;> rcases two s with rfl | rfl <;>
      simp only [map_zero, map_one, zero_mul, one_mul, add_zero, zero_add] at hps
    · exact absurd (mul_self_eq_zero.mp hps.symm) hω0
    · exfalso
      exact hω0 (by
        have : ω * (ω - 1) = 0 := by linear_combination -hps
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h) hω1)
    · exfalso
      have : (ω + 1) * (ω + 1) = 0 := by linear_combination -hps + (ω + 1) * h2F
      exact hω1 (by linear_combination mul_self_eq_zero.mp this - h2F)
    · linear_combination -hps
  have hcube : ∀ x : Fˣ, x ^ 3 = 1 := fun x => by
    have h := pow_card_eq_one' (x := x)
    rwa [Nat.card_units, hF] at h
  exact ⟨⟨ι, ω, hsq, hbij, two, hcube⟩, hιp⟩

end Param

section Minus

variable {K : Type} [Field K] [CharP K 2] {r : ℕ}

@[expose] noncomputable def minusHypE (hn : 1 ≤ r + 2) (l : ℕ) : Fin (2 * (r + 2)) → K :=
  if h : l < r + 1 then Pi.single (minusIndexEquiv (r + 2) hn (.inl ⟨l, by omega⟩)) 1 else 0

@[expose] noncomputable def minusHypF (hn : 1 ≤ r + 2) (l : ℕ) : Fin (2 * (r + 2)) → K :=
  if h : l < r + 1 then Pi.single (minusIndexEquiv (r + 2) hn (.inr (.inl ⟨l, by omega⟩))) 1
  else 0

theorem minusHypE_of_lt (hn : 1 ≤ r + 2) {l : ℕ} (h : l < r + 1) :
    minusHypE (K := K) hn l = Pi.single (minusIndexEquiv (r + 2) hn (.inl ⟨l, by omega⟩)) 1 := by
  rw [minusHypE, dite_eq_left_of_eq_true (eq_true h)]

theorem minusHypF_of_lt (hn : 1 ≤ r + 2) {l : ℕ} (h : l < r + 1) :
    minusHypF (K := K) hn l =
      Pi.single (minusIndexEquiv (r + 2) hn (.inr (.inl ⟨l, by omega⟩))) 1 := by
  rw [minusHypF, dite_eq_left_of_eq_true (eq_true h)]

theorem minusHypE_of_not_lt (hn : 1 ≤ r + 2) {l : ℕ} (h : ¬l < r + 1) :
    minusHypE (K := K) hn l = 0 := by
  rw [minusHypE, dite_eq_right_of_eq_false (eq_false h)]

theorem minusHypF_of_not_lt (hn : 1 ≤ r + 2) {l : ℕ} (h : ¬l < r + 1) :
    minusHypF (K := K) hn l = 0 := by
  rw [minusHypF, dite_eq_right_of_eq_false (eq_false h)]

theorem isHypSystem_minus (hn : 1 ≤ r + 2) (b c : K) :
    IsHypSystem (coordinateQuadMinus (r + 2) K hn b c) (r + 1) (minusHypE hn) (minusHypF hn) where
  map_e l := by
    by_cases h : l < r + 1
    · rw [minusHypE_of_lt hn h]
      exact (isHypCoord_coordinateQuadMinus hn b c _).map_left
    · rw [minusHypE_of_not_lt hn h, QuadraticMap.map_zero]
  map_f l := by
    by_cases h : l < r + 1
    · rw [minusHypF_of_lt hn h]
      exact (isHypCoord_coordinateQuadMinus hn b c _).map_right
    · rw [minusHypF_of_not_lt hn h, QuadraticMap.map_zero]
  ee l m := by
    by_cases h : l < r + 1
    · by_cases h' : m < r + 1
      · rw [minusHypE_of_lt hn h, minusHypE_of_lt hn h',
          (isHypCoord_coordinateQuadMinus hn b c _).polar_left]
        exact Pi.single_eq_of_ne (fun h'' => by simpa using (minusIndexEquiv _ hn).injective h'') _
      · rw [minusHypE_of_not_lt hn h', polar_zero_right]
    · rw [minusHypE_of_not_lt hn h, polar_zero_left]
  ff l m := by
    by_cases h : l < r + 1
    · by_cases h' : m < r + 1
      · rw [minusHypF_of_lt hn h, minusHypF_of_lt hn h',
          (isHypCoord_coordinateQuadMinus hn b c _).polar_right]
        exact Pi.single_eq_of_ne (fun h'' => by simpa using (minusIndexEquiv _ hn).injective h'') _
      · rw [minusHypF_of_not_lt hn h', polar_zero_right]
    · rw [minusHypF_of_not_lt hn h, polar_zero_left]
  ef l m hlm := by
    by_cases h : l < r + 1
    · by_cases h' : m < r + 1
      · rw [minusHypE_of_lt hn h, minusHypF_of_lt hn h',
          (isHypCoord_coordinateQuadMinus hn b c _).polar_left]
        refine Pi.single_eq_of_ne (fun h'' => hlm ?_) _
        have := (minusIndexEquiv _ hn).injective h''
        simp only [Sum.inr.injEq, Sum.inl.injEq, Fin.mk.injEq] at this
        exact this
      · rw [minusHypF_of_not_lt hn h', polar_zero_right]
    · rw [minusHypE_of_not_lt hn h, polar_zero_left]
  ef_self l h := by
    rw [minusHypE_of_lt hn h, minusHypF_of_lt hn h,
      (isHypCoord_coordinateQuadMinus hn b c _).polar_left, Pi.single_eq_same]

theorem polar_aniso_minusHyp (hn : 1 ≤ r + 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (l : ℕ) :
    polar (coordinateQuadMinus (r + 2) K hn b c) (Pi.single (anisoCoordLeft hn) 1)
        (minusHypE hn l) = 0 ∧
      polar (coordinateQuadMinus (r + 2) K hn b c) (Pi.single (anisoCoordLeft hn) 1)
        (minusHypF hn l) = 0 ∧
      polar (coordinateQuadMinus (r + 2) K hn b c) (Pi.single (anisoCoordRight hn) 1)
        (minusHypE hn l) = 0 ∧
      polar (coordinateQuadMinus (r + 2) K hn b c) (Pi.single (anisoCoordRight hn) 1)
        (minusHypF hn l) = 0 := by
  have hA := isAnisoCoord_coordinateQuadMinus (K := K) hn hirr
  by_cases h : l < r + 1
  · rw [minusHypE_of_lt hn h, minusHypF_of_lt hn h, hA.polar_left, hA.polar_left, hA.polar_right,
      hA.polar_right]
    have e1 : ∀ s : Fin (r + 2 - 1) ⊕ Fin (r + 2 - 1) ⊕ Fin 2, (∀ t, s ≠ .inr (.inr t)) →
        (Pi.single (minusIndexEquiv (r + 2) hn s) (1 : K) : Fin (2 * (r + 2)) → K)
          (anisoCoordLeft hn) = 0 ∧
        (Pi.single (minusIndexEquiv (r + 2) hn s) (1 : K) : Fin (2 * (r + 2)) → K)
          (anisoCoordRight hn) = 0 := fun s hs =>
      ⟨Pi.single_eq_of_ne (fun h' => hs 0 ((minusIndexEquiv _ hn).injective h').symm) _,
        Pi.single_eq_of_ne (fun h' => hs 1 ((minusIndexEquiv _ hn).injective h').symm) _⟩
    obtain ⟨x1, x2⟩ := e1 (.inl ⟨l, by omega⟩) (fun t => by simp)
    obtain ⟨y1, y2⟩ := e1 (.inr (.inl ⟨l, by omega⟩)) (fun t => by simp)
    rw [x1, x2, y1, y2, mul_zero]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [minusHypE_of_not_lt hn h, minusHypF_of_not_lt hn h, polar_zero_right, polar_zero_right]
    exact ⟨rfl, rfl, rfl, rfl⟩

@[expose] noncomputable def minusFrameA (hn : 1 ≤ r + 2) : Fin (r + 1) → Fin (2 * (r + 2)) → K :=
  Fin.cons (Pi.single (anisoCoordLeft hn) 1) fun i : Fin r =>
    blockVec (minusHypE (K := K) hn) (minusHypF hn) i

@[expose] noncomputable def minusFrameA' (hn : 1 ≤ r + 2) : Fin (r + 1) → Fin (2 * (r + 2)) → K :=
  Fin.cons (Pi.single (anisoCoordRight hn) 1) fun i : Fin r =>
    blockVec' (minusHypE (K := K) hn) (minusHypF hn) i

theorem minusFrameA_zero (hn : 1 ≤ r + 2) :
    minusFrameA (K := K) hn 0 = Pi.single (anisoCoordLeft hn) 1 := Fin.cons_zero _ _

theorem minusFrameA'_zero (hn : 1 ≤ r + 2) :
    minusFrameA' (K := K) hn 0 = Pi.single (anisoCoordRight hn) 1 := Fin.cons_zero _ _

theorem minusFrameA_succ (hn : 1 ≤ r + 2) (i : Fin r) :
    minusFrameA (K := K) hn i.succ = blockVec (minusHypE hn) (minusHypF hn) i :=
  Fin.cons_succ _ _ _

theorem minusFrameA'_succ (hn : 1 ≤ r + 2) (i : Fin r) :
    minusFrameA' (K := K) hn i.succ = blockVec' (minusHypE hn) (minusHypF hn) i :=
  Fin.cons_succ _ _ _

theorem isUnitPlane_aniso (hn : 1 ≤ r + 2) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) :
    IsUnitPlane (coordinateQuadMinus (r + 2) K hn 1 1) (Pi.single (anisoCoordLeft hn) 1)
      (Pi.single (anisoCoordRight hn) 1) := by
  have hA := isAnisoCoord_coordinateQuadMinus (K := K) hn hirr
  exact ⟨hA.map_left, hA.map_right, by rw [hA.polar_left, Pi.single_eq_same, one_mul]⟩

theorem isOrthUnitFamily_minusFrame (hn : 1 ≤ r + 2) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) :
    IsOrthUnitFamily (coordinateQuadMinus (r + 2) K hn 1 1) (minusFrameA hn) (minusFrameA' hn) := by
  have hS := isHypSystem_minus (K := K) hn 1 1
  have hB := hS.isOrthUnitFamily_blocks (n := r) fun i hi => by omega
  have hp : ∀ (w : Fin (2 * (r + 2)) → K), (∀ l, polar (coordinateQuadMinus (r + 2) K hn 1 1) w
      (minusHypE hn l) = 0 ∧ polar (coordinateQuadMinus (r + 2) K hn 1 1) w (minusHypF hn l) = 0) →
      ∀ i : Fin r, polar (coordinateQuadMinus (r + 2) K hn 1 1) w
        (blockVec (minusHypE hn) (minusHypF hn) i) = 0 ∧
        polar (coordinateQuadMinus (r + 2) K hn 1 1) w
          (blockVec' (minusHypE hn) (minusHypF hn) i) = 0 :=
    fun w hw i => hS.polar_blockVec_of_perp i fun l _ => hw l
  have hU := hp _ fun l => ⟨(polar_aniso_minusHyp hn hirr l).1, (polar_aniso_minusHyp hn hirr l).2.1⟩
  have hV := hp _ fun l =>
    ⟨(polar_aniso_minusHyp hn hirr l).2.2.1, (polar_aniso_minusHyp hn hirr l).2.2.2⟩
  exact hB.cons (isUnitPlane_aniso hn hirr) (fun k => (hU k).1) (fun k => (hU k).2)
    (fun k => (hV k).1) (fun k => (hV k).2)

variable [Finite K]

theorem isEnnolaFrame_minus (hr : 2 ≤ r) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) :
    IsEnnolaFrame (coordinateQuadMinus (r + 2) K (by omega) 1 1) (minusFrameA (by omega))
      (minusFrameA' (by omega)) :=
  (isOrthUnitFamily_minusFrame _ hirr).isEnnolaFrame
    (regular_coordinateQuadMinus (r + 2) K 1 1 (by omega) hirr).1
    (regular_coordinateQuadMinus (r + 2) K 1 1 (by omega) hirr).2

variable {F : Type} [Field F] (E : EnnolaParam K F)

theorem map_rootParam_minusTorus (hr : 2 ≤ r) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) :
    (rootParam (K := F) 0).map ((isEnnolaFrame_minus hr hirr).torus E) =
      anisoTorus (K := K) (by omega) 1 1 :=
  (isEnnolaFrame_minus hr hirr).map_rootParam_torus_eq_anisoTorusOf E
    (isAnisoCoord_coordinateQuadMinus (K := K) (by omega) hirr) (minusFrameA_zero _)
    (minusFrameA'_zero _)

theorem top_le_iSup_minusTorus (hr : 4 ≤ r) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) :
    ⊤ ≤ ⨆ k, perfectCore (centralizer ((rootParam (K := F) k).map
      ((isEnnolaFrame_minus (by omega : 2 ≤ r) hirr).torus E) :
        Set (matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) 1 1)))) := by
  refine (isEnnolaFrame_minus (by omega : 2 ≤ r) hirr).top_le_iSup_perfectCore E hr ?_
  rw [minusFrameA_zero, minusFrameA'_zero, ← pairPerpOf_eq_fixVecBar]
  exact Subgroup.isPerfect_iff.mp (isQuasisimple_anisoPerp (n := r + 2) (by omega) hirr).1

end Minus

end CFSG.SeitzReduction.OmegaPilot
