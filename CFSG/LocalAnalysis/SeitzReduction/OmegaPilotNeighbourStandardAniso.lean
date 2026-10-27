module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAnisoAut
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLift
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAnisoPerp

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.Open (standardComponentIsStandard)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (reindexQuadraticForm reindexQuadraticForm_apply plusIndexEquiv minusIndexEquiv
    coordinateQuadPlus coordinateQuadMinus coordinateQuadPlus_apply coordinateQuadMinus_apply
    regular_coordinateQuadPlus regular_coordinateQuadMinus)
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Coordinates

variable {K : Type*} [Field K]

theorem IsAnisoCoord.reindex {ι : Type*} [DecidableEq ι] {d : ℕ} {Q₀ : QuadraticForm K (ι → K)}
    {a a' : ι} {b c : K} (h : IsAnisoCoord Q₀ a a' b c) (e : ι ≃ Fin d) :
    IsAnisoCoord (reindexQuadraticForm e Q₀) (e a) (e a') b c where
  ne := e.injective.ne h.ne
  map_left := by rw [reindexQuadraticForm_apply, pi_single_comp_equiv]; exact h.map_left
  map_right := by rw [reindexQuadraticForm_apply, pi_single_comp_equiv]; exact h.map_right
  polar_left v := by
    have hp : polar (reindexQuadraticForm e Q₀) (Pi.single (e a) 1) v =
        polar Q₀ (fun i => (Pi.single (e a) (1 : K) : Fin d → K) (e i)) (fun i => v (e i)) := rfl
    rw [hp, pi_single_comp_equiv, h.polar_left]
  polar_right v := by
    have hp : polar (reindexQuadraticForm e Q₀) (Pi.single (e a') 1) v =
        polar Q₀ (fun i => (Pi.single (e a') (1 : K) : Fin d → K) (e i)) (fun i => v (e i)) := rfl
    rw [hp, pi_single_comp_equiv, h.polar_right]
  irr := h.irr

theorem isAnisoCoord_quadMinus [CharP K 2] {n : ℕ} {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsAnisoCoord (quadMinus n K b c) (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) b c where
  ne := by simp
  map_left := by
    rw [quadMinus_apply]
    simp
  map_right := by
    rw [quadMinus_apply]
    simp
  polar_left v := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [polar_comm, CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_zero, h2, zero_mul,
      zero_add]
  polar_right v := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [polar_comm, CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_one, h2, zero_mul,
      zero_mul, add_zero]
  irr := hirr

variable {n : ℕ}

@[expose] noncomputable def anisoCoordLeft (hn : 1 ≤ n) : Fin (2 * n) :=
  minusIndexEquiv n hn (.inr (.inr 0))

@[expose] noncomputable def anisoCoordRight (hn : 1 ≤ n) : Fin (2 * n) :=
  minusIndexEquiv n hn (.inr (.inr 1))

theorem anisoCoord_ne (hn : 1 ≤ n) : anisoCoordLeft hn ≠ anisoCoordRight hn := by
  intro h
  have := (minusIndexEquiv n hn).injective h
  simp at this

theorem isAnisoCoord_coordinateQuadMinus [CharP K 2] (hn : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsAnisoCoord (coordinateQuadMinus n K hn b c) (anisoCoordLeft hn) (anisoCoordRight hn) b c :=
  (isAnisoCoord_quadMinus hirr).reindex (minusIndexEquiv n hn)

theorem pairDisjoint_aniso (hn : 1 ≤ n) (k : Fin (n - 1)) :
    PairDisjoint (anisoCoordLeft hn) (anisoCoordRight hn) (minusIndexEquiv n hn (.inl k))
      (minusIndexEquiv n hn (.inr (.inl k))) where
  left_ne_left h := by have := (minusIndexEquiv n hn).injective h; simp at this
  left_ne_right h := by have := (minusIndexEquiv n hn).injective h; simp at this
  right_ne_left h := by have := (minusIndexEquiv n hn).injective h; simp at this
  right_ne_right h := by have := (minusIndexEquiv n hn).injective h; simp at this

@[expose] noncomputable def anisoPerpCoord (hn : 1 ≤ n) (x : Fin (2 * (n - 1))) : Fin (2 * n) :=
  minusIndexEquiv n hn (Sum.map id Sum.inl ((plusIndexEquiv (n - 1)).symm x))

theorem anisoPerpCoord_injective (hn : 1 ≤ n) : Function.Injective (anisoPerpCoord hn) := by
  intro x y hxy
  have h1 := (minusIndexEquiv n hn).injective hxy
  have h2 := (Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩) h1
  exact (plusIndexEquiv (n - 1)).symm.injective h2

theorem anisoPerpCoord_ne_left (hn : 1 ≤ n) (x : Fin (2 * (n - 1))) :
    anisoPerpCoord hn x ≠ anisoCoordLeft hn := by
  intro h
  have h1 := (minusIndexEquiv n hn).injective h
  rcases hy : (plusIndexEquiv (n - 1)).symm x with y | y <;> simp [hy] at h1

theorem anisoPerpCoord_ne_right (hn : 1 ≤ n) (x : Fin (2 * (n - 1))) :
    anisoPerpCoord hn x ≠ anisoCoordRight hn := by
  intro h
  have h1 := (minusIndexEquiv n hn).injective h
  rcases hy : (plusIndexEquiv (n - 1)).symm x with y | y <;> simp [hy] at h1

theorem exists_anisoPerpCoord_eq (hn : 1 ≤ n) {i : Fin (2 * n)} (hia : i ≠ anisoCoordLeft hn)
    (hib : i ≠ anisoCoordRight hn) : ∃ x, anisoPerpCoord hn x = i := by
  rcases hs : (minusIndexEquiv n hn).symm i with k | k | t
  · refine ⟨plusIndexEquiv (n - 1) (.inl k), ?_⟩
    simp only [anisoPerpCoord, Equiv.symm_apply_apply, Sum.map_inl, id_eq, ← hs,
      Equiv.apply_symm_apply]
  · refine ⟨plusIndexEquiv (n - 1) (.inr k), ?_⟩
    simp only [anisoPerpCoord, Equiv.symm_apply_apply, Sum.map_inr, ← hs, Equiv.apply_symm_apply]
  · exfalso
    have hi : i = minusIndexEquiv n hn (.inr (.inr t)) := by
      rw [← hs, Equiv.apply_symm_apply]
    fin_cases t
    · exact hia hi
    · exact hib hi

theorem coordinateQuadMinus_extend_aniso (hn : 1 ≤ n) (b c : K) (w : Fin (2 * (n - 1)) → K) :
    coordinateQuadMinus n K hn b c (Function.extend (anisoPerpCoord hn) w 0) =
      coordinateQuadPlus (n - 1) K w := by
  have hinj := anisoPerpCoord_injective hn
  have hval : ∀ s : Fin (n - 1) ⊕ Fin (n - 1),
      Function.extend (anisoPerpCoord hn) w 0 (minusIndexEquiv n hn (Sum.map id Sum.inl s)) =
        w (plusIndexEquiv (n - 1) s) := by
    intro s
    have : minusIndexEquiv n hn (Sum.map id Sum.inl s) =
        anisoPerpCoord hn (plusIndexEquiv (n - 1) s) := by
      simp [anisoPerpCoord]
    rw [this, hinj.extend_apply]
  have hzl : Function.extend (anisoPerpCoord hn) w 0 (anisoCoordLeft hn) = 0 :=
    Function.extend_apply' _ _ _ fun ⟨x, hx⟩ => anisoPerpCoord_ne_left hn x hx
  have hzr : Function.extend (anisoPerpCoord hn) w 0 (anisoCoordRight hn) = 0 :=
    Function.extend_apply' _ _ _ fun ⟨x, hx⟩ => anisoPerpCoord_ne_right hn x hx
  rw [coordinateQuadMinus_apply, coordinateQuadPlus_apply]
  have hzl' : Function.extend (anisoPerpCoord hn) w 0 (minusIndexEquiv n hn (.inr (.inr 0))) = 0 :=
    hzl
  have hzr' : Function.extend (anisoPerpCoord hn) w 0 (minusIndexEquiv n hn (.inr (.inr 1))) = 0 :=
    hzr
  rw [hzl', hzr']
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 := hval (.inl x)
  have h2 := hval (.inr x)
  simp only [Sum.map_inl, Sum.map_inr, id_eq] at h1 h2
  rw [h1, h2]

@[expose] noncomputable def anisoPerpIsometry (hn : 1 ≤ n) (b c : K) :
    ((coordinateQuadMinus n K hn b c).comp
      (perpSub K (anisoCoordLeft hn) (anisoCoordRight hn)).subtype).IsometryEquiv
      (coordinateQuadPlus (n - 1) K) :=
  perpIsometry (anisoPerpCoord hn) (anisoPerpCoord_injective hn) (anisoPerpCoord_ne_left hn)
    (anisoPerpCoord_ne_right hn) (fun _ hia hib => exists_anisoPerpCoord_eq hn hia hib)
    (coordinateQuadMinus_extend_aniso hn b c)

end Coordinates

section Defs

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def anisoTorus [CharP K 2] (hn : 1 ≤ n) (b c : K) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  anisoTorusOf (coordinateQuadMinus n K hn b c) (anisoCoord_ne hn) b c

@[expose] noncomputable def anisoPerp (hn : 1 ≤ n) (b c : K) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  pairPerpOf (coordinateQuadMinus n K hn b c) (anisoCoordLeft hn) (anisoCoordRight hn)

end Defs

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem regular_anisoPerp (hn : 4 ≤ n) (b c : K) :
    (polarBilin ((coordinateQuadMinus n K (by omega) b c).comp
      (perpSub K (anisoCoordLeft (by omega : 1 ≤ n))
        (anisoCoordRight (by omega : 1 ≤ n))).subtype)).Nondegenerate ∧
    ∃ T : Submodule K (perpSub K (anisoCoordLeft (by omega : 1 ≤ n))
        (anisoCoordRight (by omega : 1 ≤ n))),
      finrank K T = 3 ∧ ∀ x ∈ T, (coordinateQuadMinus n K (by omega) b c).comp
        (perpSub K (anisoCoordLeft (by omega : 1 ≤ n))
          (anisoCoordRight (by omega : 1 ≤ n))).subtype x = 0 := by
  have hreg := regular_coordinateQuadPlus (n - 1) K (by omega)
  have e := anisoPerpIsometry (K := K) (by omega : 1 ≤ n) b c
  exact ⟨nondegenerate_of_isometryEquiv e hreg.1, exists_threeSingular_of_isometryEquiv e hreg.2⟩

theorem centralizer_anisoTorus (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    centralizer (anisoTorus (K := K) (by omega : 1 ≤ n) b c :
      Set (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))) =
      anisoTorus (by omega) b c ⊔ anisoPerp (by omega) b c := by
  have hreg := regular_coordinateQuadMinus n K b c hn hirr
  exact (isAnisoCoord_coordinateQuadMinus (by omega) hirr).centralizer_anisoTorusOf hreg.1 hreg.2

theorem anisoTorus_le_centralizer_anisoPerp (hn : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    anisoTorus (K := K) hn b c ≤ centralizer (anisoPerp (K := K) hn b c :
      Set (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))) :=
  (isAnisoCoord_coordinateQuadMinus hn hirr).anisoTorusOf_le_centralizer_pairPerpOf

omit [Finite K] in
theorem anisoTorus_le_centralizer_self (hn : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    anisoTorus (K := K) hn b c ≤ centralizer (anisoTorus (K := K) hn b c :
      Set (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))) :=
  (isAnisoCoord_coordinateQuadMinus hn hirr).anisoTorusOf_le_centralizer_self

theorem odd_card_anisoTorus (hn : 1 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Odd (Nat.card (anisoTorus (K := K) hn b c)) :=
  (isAnisoCoord_coordinateQuadMinus hn hirr).odd_card_anisoTorusOf

@[expose] noncomputable def anisoPerpEquiv (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    anisoPerp (K := K) (by omega : 1 ≤ n) b c ≃* orthDerived (coordinateQuadPlus (n - 1) K) :=
  ((isAnisoCoord_coordinateQuadMinus (by omega) hirr).pairPerpOfEquiv
    (regular_coordinateQuadMinus n K b c hn hirr).1 (regular_anisoPerp hn b c).1
    (regular_anisoPerp hn b c).2).trans (orthDerivedCongr (anisoPerpIsometry (by omega) b c))

theorem isQuasisimple_anisoPerp (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.IsQuasisimple (anisoPerp (K := K) (by omega : 1 ≤ n) b c) :=
  (isAnisoCoord_coordinateQuadMinus (by omega) hirr).isQuasisimple_pairPerpOf
    (regular_coordinateQuadMinus n K b c hn hirr).1 (regular_anisoPerp hn b c).1
    (regular_anisoPerp hn b c).2

theorem center_anisoPerp (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    center (anisoPerp (K := K) (by omega : 1 ≤ n) b c) = ⊥ := by
  have hreg := regular_coordinateQuadPlus (n - 1) K (by omega)
  rw [eq_bot_iff]
  intro x hx
  have hx' : anisoPerpEquiv hn hirr x ∈ center (orthDerived (coordinateQuadPlus (n - 1) K)) := by
    rw [← map_center_eq (anisoPerpEquiv hn hirr)]
    exact ⟨x, hx, rfl⟩
  rw [center_orthDerived_eq_bot' hreg.1 hreg.2
    (isHypCoord_coordinateQuadPlus (K := K) (⟨0, by omega⟩ : Fin (n - 1))).exists_ne_zero,
    mem_bot] at hx'
  rw [mem_bot, ← (anisoPerpEquiv hn hirr).symm_apply_apply x, hx', map_one]

theorem lieModel_anisoPerp {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.Blueprint.LieModel (anisoPerp (K := K) (by omega : 1 ≤ n) b c) .POmegaPlus (n - 1) 2 f :=
  lieModel_of_mulEquiv_orthDerived_plus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hK) hK
    (anisoPerpEquiv (by omega) hirr)

theorem exists_mem_anisoTorus_eq_conj (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))}
    (hX : ∀ x ∈ anisoTorus (K := K) (one_le_of_four_le hn) b c, β x = x)
    (hD : ∀ x ∈ anisoPerp (K := K) (one_le_of_four_le hn) b c, β x = x) :
    ∃ x ∈ anisoTorus (K := K) (one_le_of_four_le hn) b c, β = MulAut.conj x := by
  have hreg := regular_coordinateQuadMinus n K b c hn hirr
  have hn1 : 1 ≤ n := by omega
  set k₂ : Fin (n - 1) := ⟨0, by omega⟩
  set k₃ : Fin (n - 1) := ⟨1, by omega⟩
  have h23 : k₂ ≠ k₃ := by simp [k₂, k₃, Fin.ext_iff]
  refine (isAnisoCoord_coordinateQuadMinus hn1 hirr).exists_mem_anisoTorusOf_eq_conj hreg.1
    hreg.2 (isHypCoord_coordinateQuadMinus hn1 b c k₂) (isHypCoord_coordinateQuadMinus hn1 b c k₃)
    (pairDisjoint_aniso hn1 k₂) (pairDisjoint_aniso hn1 k₃) (pairDisjoint_minus hn1 h23) ?_ hX hD
  rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr]
  exact Subgroup.mem_top β

theorem eq_one_of_two_pow_fix_anisoTorus (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))} {m : ℕ}
    (hβ : β ^ 2 ^ m = 1) (hX : ∀ x ∈ anisoTorus (K := K) (one_le_of_four_le hn) b c, β x = x)
    (hD : ∀ x ∈ anisoPerp (K := K) (one_le_of_four_le hn) b c, β x = x) : β = 1 :=
  eq_one_of_two_pow_of_forall_fix_eq_conj (odd_card_anisoTorus _ hirr)
    (fun _ hX hD => exists_mem_anisoTorus_eq_conj hn hirr hX hD) β hX hD m hβ

end Main

section Group

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {n : ℕ}

theorem neighbour_data_anisoTorus (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) {X : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ X ≤ centralizer (X : Set G) ∧ Odd (Nat.card X) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧ CFSG.IsQuasisimple D ∧
      center D = ⊥ := by
  subst hX hDe
  have hDq := isQuasisimple_anisoPerp hn hirr
  set ψ := LinearPilot.mapSymmMulEquiv e (anisoPerp (K := K) (by omega : 1 ≤ n) b c) with hψ
  refine ⟨map_subtype_le _, LinearPilot.mem_centralizer_map_symm e _ htC,
    LinearPilot.map_symm_le_centralizer_map_symm e (anisoTorus_le_centralizer_self _ hirr),
    (LinearPilot.card_map_symm e _).symm ▸ odd_card_anisoTorus _ hirr,
    (F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e (centralizer_anisoTorus hn hirr)
      (anisoTorus_le_centralizer_anisoPerp _ hirr) (anisoTorus_le_centralizer_self _ hirr)
      hDq).symm,
    le_inf (LinearPilot.map_symm_le_centralizer_map_symm e
      (le_centralizer_iff.mp (anisoTorus_le_centralizer_anisoPerp _ hirr)))
      (LinearPilot.map_symm_le_centralizer_singleton e _ htC),
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm hDq, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have hx' : ψ x ∈ center (anisoPerp (K := K) (one_le_of_four_le hn) b c) := by
    rw [← map_center_eq ψ]
    exact ⟨x, hx, rfl⟩
  rw [center_anisoPerp hn hirr, mem_bot] at hx'
  rw [mem_bot, ← ψ.symm_apply_apply x, hx', map_one]

theorem lieModel_map_anisoPerp {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Blueprint.LieModel D .POmegaPlus (n - 1) 2 f ∧ Group.IsSolvable (Outer D) := by
  subst hDe
  set ψ := LinearPilot.mapSymmMulEquiv e (anisoPerp (K := K) (by omega : 1 ≤ n) b c) with hψ
  exact ⟨lieModel_of_mulEquiv ψ.symm (lieModel_anisoPerp hKc hn hirr),
    isSolvable_outer_of_mulEquiv_plus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc
      ((ψ.trans (anisoPerpEquiv (by omega) hirr)).trans (MulEquiv.ofBijective (projHom _)
        ⟨projHom_injective (isHypCoord_coordinateQuadPlus (K := K)
          (⟨0, by omega⟩ : Fin (n - 1))).exists_ne_zero, projHom_surjective _⟩))⟩

variable [Finite G]

theorem neighbour_standard_anisoTorus (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {X : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
  neighbour_standard_of_mulEquiv_of_eq_conj hL htC ht hK e (centralizer_anisoTorus hn hirr)
    (anisoTorus_le_centralizer_anisoPerp _ hirr) (anisoTorus_le_centralizer_self _ hirr)
    (isQuasisimple_anisoPerp hn hirr) (odd_card_anisoTorus _ hirr)
    (fun _ hX hD => exists_mem_anisoTorus_eq_conj hn hirr hX hD) hX htX hDe

theorem bLift_inputs_anisoTorus (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {X : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧ CFSG.IsQuasisimple D ∧
      ∀ x ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
        Odd (orderOf x) → x ∈ X :=
  bLift_inputs_of_mulEquiv hL htC ht hK e (centralizer_anisoTorus hn hirr)
    (anisoTorus_le_centralizer_anisoPerp _ hirr) (anisoTorus_le_centralizer_self _ hirr)
    (isQuasisimple_anisoPerp hn hirr) (odd_card_anisoTorus _ hirr)
    (fun _ hX hD => exists_mem_anisoTorus_eq_conj hn hirr hX hD) hX hDe

theorem mem_anisoTorus_of_odd_of_commute (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    {x : G} (hx : x ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G))
    (hxo : Odd (orderOf x)) : x ∈ X :=
  (bLift_inputs_anisoTorus hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_minus hset hn hKc hirr e htC ht) hn hirr e hX hDe).2.2.2 x hx hxo

theorem neighbour_standard_anisoTorus_of_seitzSetting (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
  neighbour_standard_anisoTorus hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_minus hset hn hKc hirr e htC ht) hn hirr e hX htX hDe

end Group

end CFSG.SeitzReduction.OmegaPilot
