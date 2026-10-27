module

public import Mathlib.GroupTheory.Frattini
public import CFSG.FeitThompson.Representations.PrimeCentralTorsionCharacteristic
import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter
import CFSG.FeitThompson.Local.FrattiniCommutingProductPrimePower
import CFSG.FeitThompson.Local.NormalSubgroupCentralPrimeTorsion
import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup QuotientGroup
open scoped commutatorElement

variable {p n : ℕ} {P : Type*} [Group P]

theorem le_upperCentralSeriesStep_iff {N H : Subgroup P} [N.Normal] :
    H ≤ N.upperCentralSeriesStep ↔ ⁅(⊤ : Subgroup P), H⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  refine ⟨fun h g _ x hx => ?_,
    fun h x hx => (Subgroup.mem_upperCentralSeriesStep _ _).2 fun y => ?_⟩
  · rw [← commutatorElement_inv]
    exact N.inv_mem ((Subgroup.mem_upperCentralSeriesStep _ _).1 (h hx) g)
  · rw [← commutatorElement_inv]
    exact N.inv_mem (h y (mem_top y) x hx)

theorem commutator_top_sup_le {N A B : Subgroup P} [N.Normal]
    (hA : ⁅(⊤ : Subgroup P), A⁆ ≤ N) (hB : ⁅(⊤ : Subgroup P), B⁆ ≤ N) :
    ⁅(⊤ : Subgroup P), A ⊔ B⁆ ≤ N :=
  le_upperCentralSeriesStep_iff.1
    (sup_le (le_upperCentralSeriesStep_iff.2 hA) (le_upperCentralSeriesStep_iff.2 hB))

theorem mem_comap_center_mk'_iff {N : Subgroup P} [N.Normal] {x : P} :
    x ∈ (center (P ⧸ N)).comap (mk' N) ↔ ∀ y : P, ⁅x, y⁆ ∈ N := by
  rw [← Subgroup.upperCentralSeriesStep_eq_comap_center, Subgroup.mem_upperCentralSeriesStep]

theorem exists_natCard_subgroup_eq_pow (hp : p.Prime) (hP : Nat.card P = p ^ n)
    (H : Subgroup P) : ∃ m, Nat.card H = p ^ m := by
  have := Fact.mk hp
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  exact ((IsPGroup.of_card hP).to_subgroup H).exists_card_eq

theorem map_subtype_le_map_subtype_iff {H : Subgroup P} {A B : Subgroup ↥H} :
    A.map H.subtype ≤ B.map H.subtype ↔ A ≤ B :=
  Subgroup.map_le_map_iff_of_injective H.subtype_injective

theorem le_map_center_subtype_sup_of_commute {A B W : Subgroup P}
    (hcomm : ∀ u ∈ A, ∀ v ∈ B, Commute u v) (hWA : W ≤ A)
    (hWc : W ≤ centralizer (A : Set P)) :
    W ≤ (center ↥(A ⊔ B)).map (A ⊔ B).subtype := by
  rw [map_center_subtype_eq_inf_centralizer]
  intro z hz
  refine Subgroup.mem_inf.2
    ⟨Subgroup.mem_sup_left (hWA hz), Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm hg
  have h1 : Commute u z := Subgroup.mem_centralizer_iff.1 (hWc hz) u hu
  have h2 : Commute v z := (hcomm z (hWA hz) v hv).symm
  exact h1.mul_left h2

def centralPTorsionCentralizer (p : ℕ) (K : Subgroup P) [K.Characteristic] : Subgroup P :=
  centralizer (K : Set P) ⊓
    (centerTorsionBy (P ⧸ (center ↥K).map K.subtype) p).comap (mk' ((center ↥K).map K.subtype))

variable (p) (K : Subgroup P) [K.Characteristic]

theorem mem_centralPTorsionCentralizer {x : P} :
    x ∈ centralPTorsionCentralizer p K ↔ x ∈ centralizer (K : Set P) ∧
      (∀ y : P, ⁅x, y⁆ ∈ (center ↥K).map K.subtype) ∧
      x ^ p ∈ (center ↥K).map K.subtype := by
  rw [centralPTorsionCentralizer, Subgroup.mem_inf, Subgroup.mem_comap, mem_centerTorsionBy]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · exact mem_comap_center_mk'_iff (N := (center ↥K).map K.subtype)
  · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem centralPTorsionCentralizer_le_centralizer :
    centralPTorsionCentralizer p K ≤ centralizer (K : Set P) := inf_le_left

instance centralPTorsionCentralizer_characteristic :
    (centralPTorsionCentralizer p K).Characteristic := by
  have h2 : ((centerTorsionBy (P ⧸ (center ↥K).map K.subtype) p).comap
      (mk' ((center ↥K).map K.subtype))).Characteristic :=
    Subgroup.Characteristic.comap_quotient_mk (centerTorsionBy_characteristic p)
  exact inferInstanceAs (centralizer (K : Set P) ⊓ _).Characteristic

theorem commutator_top_centralPTorsionCentralizer_le :
    ⁅(⊤ : Subgroup P), centralPTorsionCentralizer p K⁆ ≤ (center ↥K).map K.subtype := by
  rw [Subgroup.commutator_le]
  intro g _ x hx
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ (((mem_centralPTorsionCentralizer p K).1 hx).2.1 g)

theorem map_center_le_centralPTorsionCentralizer
    (hPK : ⁅(⊤ : Subgroup P), K⁆ ≤ (center ↥K).map K.subtype) :
    (center ↥K).map K.subtype ≤ centralPTorsionCentralizer p K := by
  intro z hz
  have hzK : z ∈ K ⊓ centralizer (K : Set P) := by
    rwa [← map_center_subtype_eq_inf_centralizer]
  refine (mem_centralPTorsionCentralizer p K).2 ⟨hzK.2, fun y => ?_, Subgroup.pow_mem _ hz _⟩
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ (hPK (Subgroup.commutator_mem_commutator (mem_top y) hzK.1))

theorem map_subtype_frattini_centralPTorsionCentralizer_le (hp : p.Prime)
    (hP : Nat.card P = p ^ n) :
    (frattini ↥(centralPTorsionCentralizer p K)).map (centralPTorsionCentralizer p K).subtype
      ≤ (center ↥K).map K.subtype := by
  obtain ⟨m, hm⟩ := exists_natCard_subgroup_eq_pow hp hP (centralPTorsionCentralizer p K)
  rw [map_subtype_frattini hp hm]
  refine commutatorSupPowClosureIn_le.2 ⟨fun x hx y _ => ?_, fun x hx => ?_⟩
  · exact ((mem_centralPTorsionCentralizer p K).1 hx).2.1 y
  · exact ((mem_centralPTorsionCentralizer p K).1 hx).2.2

theorem exists_mem_centralPTorsionCentralizer_notMem_map_center
    (hp : p.Prime) (hP : Nat.card P = p ^ n)
    (hlt : (center ↥K).map K.subtype < centralizer (K : Set P)) :
    ∃ x ∈ centralPTorsionCentralizer p K, x ∉ (center ↥K).map K.subtype := by
  have := Fact.mk hp
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  set Z := (center ↥K).map K.subtype with hZ
  set C := centralizer (K : Set P) with hC
  obtain ⟨c, hcC, hcZ⟩ := SetLike.exists_of_lt hlt
  have hD : C.map (mk' Z) ≠ ⊥ := by
    intro h
    have hmem : (mk' Z) c ∈ C.map (mk' Z) := ⟨c, hcC, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hcZ ((QuotientGroup.eq_one_iff c).1 hmem)
  obtain ⟨m, hm⟩ := ((IsPGroup.of_card hP).to_quotient Z).exists_card_eq
  obtain ⟨Q, hQle, hQcard⟩ := exists_le_inf_center_natCard_eq (C.map (mk' Z)) hp hm hD
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩] at hQcard
    exact hp.one_lt.ne hQcard
  obtain ⟨q, hq, hq1⟩ := (Subgroup.bot_or_exists_ne_one Q).resolve_left hQne
  have hqp : q ^ p = 1 := by
    have hpow : (⟨q, hq⟩ : Q) ^ p = 1 := by rw [← hQcard]; exact pow_card_eq_one'
    simpa [← Subtype.ext_iff] using hpow
  obtain ⟨hqD, hqcenter⟩ := Subgroup.mem_inf.1 (hQle hq)
  obtain ⟨x, hxC, hxq⟩ := hqD
  refine ⟨x, (mem_centralPTorsionCentralizer p K).2 ⟨hxC, ?_, ?_⟩, ?_⟩
  · exact mem_comap_center_mk'_iff.1 (by rw [Subgroup.mem_comap, hxq]; exact hqcenter)
  · rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, hxq, hqp]
  · intro hxZ
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, hxq] at hxZ
    exact hq1 hxZ

def criticalEnlargement (p : ℕ) (K : Subgroup P) [K.Characteristic] : Subgroup P :=
  K ⊔ centralPTorsionCentralizer p K

theorem criticalEnlargement_eq_sup :
    criticalEnlargement p K = K ⊔ centralPTorsionCentralizer p K := (rfl)

theorem commute_of_mem_of_mem_centralPTorsionCentralizer :
    ∀ u ∈ K, ∀ v ∈ centralPTorsionCentralizer p K, Commute u v := by
  intro u hu v hv
  exact Subgroup.mem_centralizer_iff.1 (centralPTorsionCentralizer_le_centralizer p K hv) u hu

theorem coe_criticalEnlargement :
    ((criticalEnlargement p K : Subgroup P) : Set P)
      = (K : Set P) * (centralPTorsionCentralizer p K : Set P) :=
  coe_sup_eq_mul_of_commute (commute_of_mem_of_mem_centralPTorsionCentralizer p K)

theorem le_criticalEnlargement : K ≤ criticalEnlargement p K := le_sup_left

instance criticalEnlargement_characteristic : (criticalEnlargement p K).Characteristic :=
  inferInstanceAs (K ⊔ centralPTorsionCentralizer p K).Characteristic

theorem map_center_le_map_center_criticalEnlargement :
    (center ↥K).map K.subtype
      ≤ (center ↥(criticalEnlargement p K)).map (criticalEnlargement p K).subtype := by
  refine le_map_center_subtype_sup_of_commute
    (commute_of_mem_of_mem_centralPTorsionCentralizer p K) ?_ ?_
  · rw [map_center_subtype_eq_inf_centralizer]; exact inf_le_left
  · rw [map_center_subtype_eq_inf_centralizer]; exact inf_le_right

theorem lt_criticalEnlargement (hp : p.Prime) (hP : Nat.card P = p ^ n)
    (hlt : (center ↥K).map K.subtype < centralizer (K : Set P)) : K < criticalEnlargement p K := by
  obtain ⟨x, hxX, hxZ⟩ := exists_mem_centralPTorsionCentralizer_notMem_map_center p K hp hP hlt
  have hxK : x ∉ K := fun hxK => hxZ (by
    rw [map_center_subtype_eq_inf_centralizer]
    exact Subgroup.mem_inf.2 ⟨hxK, centralPTorsionCentralizer_le_centralizer p K hxX⟩)
  refine lt_of_le_of_ne (le_criticalEnlargement p K) fun h => hxK ?_
  rw [h]
  exact Subgroup.mem_sup_right hxX

theorem frattini_criticalEnlargement_le_center (hp : p.Prime) (hP : Nat.card P = p ^ n)
    (hΦ : frattini ↥K ≤ center ↥K) :
    frattini ↥(criticalEnlargement p K) ≤ center ↥(criticalEnlargement p K) := by
  obtain ⟨a, ha⟩ := exists_natCard_subgroup_eq_pow hp hP K
  obtain ⟨b, hb⟩ := exists_natCard_subgroup_eq_pow hp hP (centralPTorsionCentralizer p K)
  rw [← map_subtype_le_map_subtype_iff, criticalEnlargement,
    map_subtype_frattini_sup hp ha hb (commute_of_mem_of_mem_centralPTorsionCentralizer p K)]
  exact sup_le
    ((Subgroup.map_mono hΦ).trans (map_center_le_map_center_criticalEnlargement p K))
    ((map_subtype_frattini_centralPTorsionCentralizer_le p K hp hP).trans
      (map_center_le_map_center_criticalEnlargement p K))

theorem commutator_top_criticalEnlargement_le
    (hPK : ⁅(⊤ : Subgroup P), K⁆ ≤ (center ↥K).map K.subtype) :
    ⁅(⊤ : Subgroup P), criticalEnlargement p K⁆
      ≤ (center ↥(criticalEnlargement p K)).map (criticalEnlargement p K).subtype :=
  commutator_top_sup_le (hPK.trans (map_center_le_map_center_criticalEnlargement p K))
    ((commutator_top_centralPTorsionCentralizer_le p K).trans
      (map_center_le_map_center_criticalEnlargement p K))

theorem exists_characteristic_gt (hp : p.Prime) (hP : Nat.card P = p ^ n)
    (hΦ : frattini ↥K ≤ center ↥K)
    (hPK : ⁅(⊤ : Subgroup P), K⁆ ≤ (center ↥K).map K.subtype)
    (hlt : (center ↥K).map K.subtype < centralizer (K : Set P)) :
    ∃ L : Subgroup P, L.Characteristic ∧ K < L ∧ frattini ↥L ≤ center ↥L ∧
      ⁅(⊤ : Subgroup P), L⁆ ≤ (center ↥L).map L.subtype :=
  ⟨criticalEnlargement p K, inferInstance, lt_criticalEnlargement p K hp hP hlt,
    frattini_criticalEnlargement_le_center p K hp hP hΦ,
    commutator_top_criticalEnlargement_le p K hPK⟩

end

end CFSG.FeitThompson
