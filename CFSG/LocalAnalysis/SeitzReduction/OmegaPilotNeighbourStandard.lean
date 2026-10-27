module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHsyl
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadPlus regular_coordinateQuadMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.Classical2 (orthDerived)

section Transport

private theorem center_eq_bot_of_mulEquiv_aux {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (h : center B = ⊥) : center A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : φ x ∈ center B := by
    rw [← map_center_eq φ]
    exact ⟨x, hx, rfl⟩
  rw [h, mem_bot] at hx'
  rw [mem_bot, ← φ.symm_apply_apply x, hx', map_one]

end Transport

section Generic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {C : Type*} [Group C]

theorem neighbour_standard_of_mulEquiv (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* C) {XC DC : Subgroup C}
    (hA : centralizer (XC : Set C) = XC ⊔ DC) (hXD : XC ≤ centralizer (DC : Set C))
    (hXc : XC ≤ centralizer (XC : Set C)) (hDq : CFSG.IsQuasisimple DC)
    (hAut : ∀ β : MulAut C, (∀ x ∈ XC, β x = x) → (∀ x ∈ DC, β x = x) →
      ∀ m : ℕ, β ^ 2 ^ m = 1 → β = 1)
    {X : Subgroup G} (hX : X = (XC.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = (DC.map e.symm.toMonoidHom).map L.subtype) :
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
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)) := by
    rw [hX, F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hA hXD hXc hDq, hDe]
  have hDq' : CFSG.IsQuasisimple D :=
    hDe ▸ CFSG.LocalCores.isQuasisimple_of_mulEquiv (LinearPilot.mapSymmMulEquiv e DC).symm hDq
  refine F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hK htX hD
    ⟨hDq'.1.commutator_eq_top, hDq'.2.1⟩ ?_
  rw [hX, hDe]
  exact eq_one_of_fix_map_of_mulEquiv e hAut

omit [Finite G] in
theorem eq_one_of_two_pow_of_forall_fix_eq_conj {XC DC : Subgroup C} (hodd : Odd (Nat.card XC))
    (hC : ∀ β : MulAut C, (∀ x ∈ XC, β x = x) → (∀ x ∈ DC, β x = x) →
      ∃ x ∈ XC, β = MulAut.conj x) :
    ∀ β : MulAut C, (∀ x ∈ XC, β x = x) → (∀ x ∈ DC, β x = x) →
      ∀ m : ℕ, β ^ 2 ^ m = 1 → β = 1 := by
  intro β hX hD m hβ
  have : Finite XC := Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero (by
    rintro h
    rw [h] at hodd
    exact Nat.not_odd_zero hodd)).ne'
  obtain ⟨x, hx, rfl⟩ := hC β hX hD
  have hx1 : x ^ Nat.card XC = 1 := by
    have h1 := pow_card_eq_one' (G := XC) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val h1
  have h1 : MulAut.conj x ^ Nat.card XC = 1 := by rw [← map_pow, hx1, map_one]
  have hcop : Nat.Coprime (2 ^ m) (Nat.card XC) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hβ)
    (orderOf_dvd_of_pow_eq_one h1))

theorem neighbour_standard_of_mulEquiv_of_eq_conj (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* C) {XC DC : Subgroup C}
    (hA : centralizer (XC : Set C) = XC ⊔ DC) (hXD : XC ≤ centralizer (DC : Set C))
    (hXc : XC ≤ centralizer (XC : Set C)) (hDq : CFSG.IsQuasisimple DC)
    (hodd : Odd (Nat.card XC))
    (hC : ∀ β : MulAut C, (∀ x ∈ XC, β x = x) → (∀ x ∈ DC, β x = x) →
      ∃ x ∈ XC, β = MulAut.conj x)
    {X : Subgroup G} (hX : X = (XC.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = (DC.map e.symm.toMonoidHom).map L.subtype) :
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
  neighbour_standard_of_mulEquiv hL htC ht hK e hA hXD hXc hDq
    (eq_one_of_two_pow_of_forall_fix_eq_conj hodd hC) hX htX hDe

end Generic

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem isQuasisimple_pairPerp (hn : 4 ≤ n) (k : Fin n) :
    CFSG.IsQuasisimple (pairPerp (K := K) k) := by
  obtain ⟨hR, hT⟩ := regular_plusPerp (K := K) hn k
  exact (isHypCoord_coordinateQuadPlus k).isQuasisimple_pairPerpOf
    (regular_coordinateQuadPlus n K (by omega)).1 hR hT

noncomputable def pairPerpProjEquiv (hn : 4 ≤ n) (k : Fin n) :
    pairPerp (K := K) k ≃* matrixProjectiveDerived (coordinateQuadPlus (n - 1) K) :=
  (pairPerpEquiv hn k).trans (MulEquiv.ofBijective (projHom _)
    ⟨projHom_injective (isHypCoord_coordinateQuadPlus (K := K)
      (⟨0, by omega⟩ : Fin (n - 1))).exists_ne_zero, projHom_surjective _⟩)

theorem center_pairPerp (hn : 4 ≤ n) (k : Fin n) : center (pairPerp (K := K) k) = ⊥ := by
  have hreg := regular_coordinateQuadPlus (n - 1) K (by omega)
  exact center_eq_bot_of_mulEquiv_aux (pairPerpEquiv hn k)
    (center_orthDerived_eq_bot' hreg.1 hreg.2
      (isHypCoord_coordinateQuadPlus (K := K) (⟨0, by omega⟩ : Fin (n - 1))).exists_ne_zero)

variable {G : Type} [Group G] {L : Subgroup G}

theorem neighbour_data_pairTorus {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hn : 5 ≤ n) (k : Fin n) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G))
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ IsCyclic X ∧ Nat.card X = Nat.card K - 1 ∧
      Odd (Nat.card X) ∧ D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧ CFSG.IsQuasisimple D ∧
      center D = ⊥ ∧ CFSG.Blueprint.LieModel D .POmegaPlus (n - 1) 2 f ∧
      Group.IsSolvable (Outer D) := by
  subst hX hDe
  have hDk := isQuasisimple_pairPerp (K := K) (by omega) k
  set ψ := LinearPilot.mapSymmMulEquiv e (pairPerp (K := K) k) with hψ
  refine ⟨map_subtype_le _, LinearPilot.mem_centralizer_map_symm e _ htC,
    LinearPilot.isCyclic_map_symm e (isCyclic_pairTorus k),
    (LinearPilot.card_map_symm e _).trans (card_pairTorus k),
    (LinearPilot.card_map_symm e _).symm ▸ odd_card_pairTorus hKc k,
    (F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e (centralizer_pairTorus hq k)
      (isHypCoord_coordinateQuadPlus k).pairTorusOf_le_centralizer_pairPerpOf
      (F4Pilot.le_centralizer_self_of_isCyclic (isCyclic_pairTorus k)) hDk).symm,
    le_inf (LinearPilot.map_symm_le_centralizer_map_symm e
      ((isHypCoord_coordinateQuadPlus k).pairPerpOf_le_centralizer hq))
      (LinearPilot.map_symm_le_centralizer_singleton e _ htC),
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm hDk,
    center_eq_bot_of_mulEquiv_aux ψ (center_pairPerp (by omega) k),
    lieModel_of_mulEquiv ψ.symm (lieModel_pairPerp hKc hn k),
    isSolvable_outer_of_mulEquiv_plus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc
      (ψ.trans (pairPerpProjEquiv (by omega) k))⟩

variable [Finite G]

theorem neighbour_standard_pairTorus (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (k : Fin n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K))
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
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
  neighbour_standard_of_mulEquiv hL htC ht hK e (centralizer_pairTorus hq k)
    (isHypCoord_coordinateQuadPlus k).pairTorusOf_le_centralizer_pairPerpOf
    (F4Pilot.le_centralizer_self_of_isCyclic (isCyclic_pairTorus k))
    (isQuasisimple_pairPerp (by omega) k)
    (fun _ hX hD _ hβ => eq_one_of_two_pow_fix_pairTorus hq hn k hβ hX hD) hX htX hDe

end Plus

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem isQuasisimple_minusPairPerp (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    CFSG.IsQuasisimple (minusPairPerp (K := K) (by omega : 1 ≤ n) b c k) := by
  obtain ⟨hR, hT⟩ := regular_minusPerp hn hirr k
  exact (isHypCoord_coordinateQuadMinus _ b c k).isQuasisimple_pairPerpOf
    (regular_coordinateQuadMinus n K b c (by omega) hirr).1 hR hT

noncomputable def minusPairPerpProjEquiv (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    minusPairPerp (K := K) (by omega : 1 ≤ n) b c k ≃*
      matrixProjectiveDerived (coordinateQuadMinus (n - 1) K (by omega) b c) :=
  (minusPairPerpEquiv hn hirr k).trans (MulEquiv.ofBijective (projHom _)
    ⟨projHom_injective (isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n - 1) b c
      (⟨0, by omega⟩ : Fin (n - 1 - 1))).exists_ne_zero, projHom_surjective _⟩)

theorem center_minusPairPerp (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : Fin (n - 1)) : center (minusPairPerp (K := K) (by omega : 1 ≤ n) b c k) = ⊥ := by
  have hreg := regular_coordinateQuadMinus (n - 1) K b c (by omega) hirr
  exact center_eq_bot_of_mulEquiv_aux (minusPairPerpEquiv hn hirr k)
    (center_orthDerived_eq_bot' hreg.1 hreg.2
      (isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n - 1) b c
        (⟨0, by omega⟩ : Fin (n - 1 - 1))).exists_ne_zero)

variable {G : Type} [Group G] {L : Subgroup G}

theorem neighbour_data_minusPairTorus {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G))
    {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ IsCyclic X ∧ Nat.card X = Nat.card K - 1 ∧
      Odd (Nat.card X) ∧ D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧ CFSG.IsQuasisimple D ∧
      center D = ⊥ ∧ CFSG.Blueprint.LieModel D .POmegaMinus (n - 1) 2 f ∧
      Group.IsSolvable (Outer D) := by
  subst hX hDe
  have hDk := isQuasisimple_minusPairPerp hn hirr k
  set ψ := LinearPilot.mapSymmMulEquiv e (minusPairPerp (K := K) (by omega : 1 ≤ n) b c k)
    with hψ
  refine ⟨map_subtype_le _, LinearPilot.mem_centralizer_map_symm e _ htC,
    LinearPilot.isCyclic_map_symm e (isCyclic_minusPairTorus _ b c k),
    (LinearPilot.card_map_symm e _).trans (card_minusPairTorus _ b c k),
    (LinearPilot.card_map_symm e _).symm ▸ odd_card_minusPairTorus hKc _ b c k,
    (F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e (centralizer_minusPairTorus hq _ b c k)
      (isHypCoord_coordinateQuadMinus _ b c k).pairTorusOf_le_centralizer_pairPerpOf
      (F4Pilot.le_centralizer_self_of_isCyclic (isCyclic_minusPairTorus _ b c k)) hDk).symm,
    le_inf (LinearPilot.map_symm_le_centralizer_map_symm e
      ((isHypCoord_coordinateQuadMinus _ b c k).pairPerpOf_le_centralizer hq))
      (LinearPilot.map_symm_le_centralizer_singleton e _ htC),
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm hDk,
    center_eq_bot_of_mulEquiv_aux ψ (center_minusPairPerp hn hirr k),
    lieModel_of_mulEquiv ψ.symm (lieModel_minusPairPerp hKc hn hirr k),
    isSolvable_outer_of_mulEquiv_minus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc
      hirr (ψ.trans (minusPairPerpProjEquiv hn hirr k))⟩

variable [Finite G]

theorem neighbour_standard_minusPairTorus (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : Fin (n - 1)) (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
    {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype) :
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
  neighbour_standard_of_mulEquiv hL htC ht hK e (centralizer_minusPairTorus hq _ b c k)
    (isHypCoord_coordinateQuadMinus _ b c k).pairTorusOf_le_centralizer_pairPerpOf
    (F4Pilot.le_centralizer_self_of_isCyclic (isCyclic_minusPairTorus _ b c k))
    (isQuasisimple_minusPairPerp hn hirr k)
    (fun _ hX hD _ hβ => eq_one_of_two_pow_fix_minusPairTorus hq (by omega) hirr k hβ hX hD)
    hX htX hDe

end Minus

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)

theorem inf_centralizer_eq_zpowers_plus (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have hI : HypothesisOne L := CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm
    (OmegaAssembly.hypothesisOne_coordinatePlus (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc hn)
  exact inf_centralizer_eq_zpowers_of_standard_of_center_eq_bot hset.standardSetting
    hset.center_eq_bot (CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv
      (quotientCenterMulEquiv hset.center_eq_bot).symm hI) htC ht

theorem inf_centralizer_eq_zpowers_minus (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have hI : HypothesisOne L := CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm
    (OmegaAssembly.hypothesisOne_coordinateMinus (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc
      hn hirr)
  exact inf_centralizer_eq_zpowers_of_standard_of_center_eq_bot hset.standardSetting
    hset.center_eq_bot (CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv
      (quotientCenterMulEquiv hset.center_eq_bot).symm hI) htC ht

theorem neighbour_standard_pairTorus_of_seitzSetting (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n)
    (k : Fin n) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
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
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  exact neighbour_standard_pairTorus hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_plus hset (by omega) hKc e htC ht) hq hn k e hX htX hDe

theorem neighbour_standard_minusPairTorus_of_seitzSetting (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype) :
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
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  exact neighbour_standard_minusPairTorus hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_minus hset (by omega) hKc hirr e htC ht) hq hn hirr k e hX htX hDe

theorem exists_neighbour_standard_plus_of_seitzSetting (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∃ X D : Subgroup G, X ≤ L ∧ IsCyclic X ∧ Nat.card X = Nat.card K - 1 ∧ Odd (Nat.card X) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧ CFSG.IsQuasisimple D ∧
      center D = ⊥ ∧ CFSG.Blueprint.LieModel D .POmegaPlus (n - 1) 2 f ∧
      Group.IsSolvable (Outer D) ∧
      ∃ htX : t ∈ centralizer (X : Set G),
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
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  set k : Fin n := ⟨0, by omega⟩
  obtain ⟨hXL, htX, hcyc, hcard, hodd, hD, hDC, hDq, hZ, hLie, hOut⟩ :=
    neighbour_data_pairTorus hKc hq hn k e htC rfl rfl
  exact ⟨_, _, hXL, hcyc, hcard, hodd, hD, hDC, hDq, hZ, hLie, hOut, htX,
    neighbour_standard_pairTorus_of_seitzSetting hset hKc hq hn k e htC ht rfl htX rfl⟩

theorem exists_neighbour_standard_minus_of_seitzSetting (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∃ X D : Subgroup G, X ≤ L ∧ IsCyclic X ∧ Nat.card X = Nat.card K - 1 ∧ Odd (Nat.card X) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧ CFSG.IsQuasisimple D ∧
      center D = ⊥ ∧ CFSG.Blueprint.LieModel D .POmegaMinus (n - 1) 2 f ∧
      Group.IsSolvable (Outer D) ∧
      ∃ htX : t ∈ centralizer (X : Set G),
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
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  set k : Fin (n - 1) := ⟨0, by omega⟩
  obtain ⟨hXL, htX, hcyc, hcard, hodd, hD, hDC, hDq, hZ, hLie, hOut⟩ :=
    neighbour_data_minusPairTorus hKc hq hn hirr k e htC rfl rfl
  exact ⟨_, _, hXL, hcyc, hcard, hodd, hD, hDC, hDq, hZ, hLie, hOut, htX,
    neighbour_standard_minusPairTorus_of_seitzSetting hset hKc hq hn hirr k e htC ht rfl htX rfl⟩

end Setting

end CFSG.SeitzReduction.OmegaPilot
