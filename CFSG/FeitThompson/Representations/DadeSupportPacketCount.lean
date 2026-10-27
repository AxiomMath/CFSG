module

public import CFSG.FeitThompson.Definitions.TotalDadeSupport
public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
public import CFSG.FeitThompson.Local.PrimeOrderFixedFreeKernelCoprime
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Rat.Cast.Order
import CFSG.FeitThompson.Representations.DadeSupportPacketsLocalClasses
import CFSG.FeitThompson.Representations.DadeCosetConjugatesDisjoint
import CFSG.FeitThompson.Representations.TwoTISaturationsFourRegionAverage
import Mathlib.Data.Set.Card.Arithmetic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open MulAction Pointwise

variable {G : Type*} [Group G]

theorem orbit_toConjActSubgroup (L : Subgroup G) (a : G) :
    orbit (toConjActSubgroup L) a = {b : G | ∃ l ∈ L, l * a * l⁻¹ = b} := by
  ext b
  constructor
  · rintro ⟨⟨s, hs⟩, rfl⟩
    exact ⟨ConjAct.ofConjAct s, mem_toConjActSubgroup_iff.1 hs, by
      simp [Subgroup.smul_def, ConjAct.smul_def]⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨ConjAct.toConjAct l, mem_toConjActSubgroup_iff.2 (by simpa using hl)⟩, by
      simp [Subgroup.smul_def, ConjAct.smul_def]⟩

def stabilizerToConjActSubgroupEquiv (L : Subgroup G) (a : G) :
    stabilizer (toConjActSubgroup L) a ≃ ↥(L ⊓ Subgroup.centralizer ({a} : Set G)) where
  toFun x := ⟨ConjAct.ofConjAct (x : ConjAct G), mem_toConjActSubgroup_iff.1 x.1.2, by
    have h : (x : ConjAct G) • a = a := x.2
    rw [ConjAct.smul_def] at h
    refine Subgroup.mem_centralizer_iff.2 ?_
    simp only [Set.mem_singleton_iff, forall_eq]
    calc a * ConjAct.ofConjAct (x : ConjAct G)
        = (ConjAct.ofConjAct (x : ConjAct G) * a * (ConjAct.ofConjAct (x : ConjAct G))⁻¹) *
            ConjAct.ofConjAct (x : ConjAct G) := by rw [h]
      _ = ConjAct.ofConjAct (x : ConjAct G) * a := by group⟩
  invFun y := ⟨⟨ConjAct.toConjAct (y : G), mem_toConjActSubgroup_iff.2 (by simpa using y.2.1)⟩, by
    have h : a * (y : G) = (y : G) * a := Subgroup.mem_centralizer_iff.1 y.2.2 a rfl
    change ConjAct.toConjAct (y : G) • a = a
    rw [ConjAct.smul_def]
    simp only [ConjAct.ofConjAct_toConjAct]
    calc (y : G) * a * (y : G)⁻¹ = a * (y : G) * (y : G)⁻¹ := by rw [h]
      _ = a := by group⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

theorem ncard_setOf_conj_mul_natCard_inf_centralizer (L : Subgroup G) (a : G) :
    {b : G | ∃ l ∈ L, l * a * l⁻¹ = b}.ncard *
      Nat.card ↥(L ⊓ Subgroup.centralizer ({a} : Set G)) = Nat.card L := by
  rw [← orbit_toConjActSubgroup L a, ← Nat.card_congr (stabilizerToConjActSubgroupEquiv L a),
    ← MulAction.index_stabilizer, Subgroup.index_mul_card, natCard_toConjActSubgroup]

namespace IsDadeData

variable [Finite G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G} {a : G}

theorem isTIWithNormalizer_dadeCoset (hD : IsDadeData L A H) (ha : a ∈ A) :
    IsTIWithNormalizer (dadeCoset H a) (Subgroup.centralizer ({a} : Set G)) where
  nonempty := ⟨a, self_mem_dadeCoset H a⟩
  one_notMem := fun h => hD.one_notMem_dadeSupport ha (dadeCoset_subset_dadeSupport H a h)
  normalizer_eq := hD.normalizer_dadeCoset ha
  disjoint_conj_image := by
    intro g hg
    have hg' : g⁻¹ ∉ Subgroup.centralizer ({a} : Set G) := fun h => hg (by simpa using inv_mem h)
    have himg : MulAut.conj g '' dadeCoset H a
        = (fun x => (g⁻¹)⁻¹ * x * g⁻¹) '' dadeCoset H a := by
      simp only [inv_inv]; rfl
    rw [himg]
    rcases hD.conjInv_image_dadeCoset_eq_or_disjoint ha g⁻¹ with h | h
    · exact absurd ((hD.conjInv_image_dadeCoset_eq_iff_mem_centralizer ha).1 h) hg'
    · exact h

theorem ncard_dadeSupport_eq_index_mul_natCard (hD : IsDadeData L A H) (ha : a ∈ A) :
    (dadeSupport H a).ncard
      = (Subgroup.centralizer ({a} : Set G)).index * Nat.card (H a) := by
  have h := (hD.isTIWithNormalizer_dadeCoset ha).finsum_mem_conjugatesOfSet
    (f := fun _ : G => (1 : ℕ)) (isClassFun_const 1)
  rw [dadeSupport_eq_conjugatesOfSet, ← finsum_one (s := Group.conjugatesOfSet (dadeCoset H a)),
    h, finsum_one, smul_eq_mul, ← Nat.card_coe_set_eq, natCard_dadeCoset]

theorem ncard_dadeSupport_mul_natCard_inf_centralizer (hD : IsDadeData L A H) (ha : a ∈ A) :
    (dadeSupport H a).ncard * Nat.card ↥(L ⊓ Subgroup.centralizer ({a} : Set G))
      = Nat.card G := by
  rw [hD.ncard_dadeSupport_eq_index_mul_natCard ha, mul_assoc, hD.card_mul_card ha,
    Subgroup.index_mul_card]

theorem ncard_dadeSupport (hD : IsDadeData L A H) (ha : a ∈ A) :
    (dadeSupport H a).ncard
      = Nat.card G / Nat.card ↥(L ⊓ Subgroup.centralizer ({a} : Set G)) :=
  (Nat.div_eq_of_eq_mul_left Nat.card_pos
    (hD.ncard_dadeSupport_mul_natCard_inf_centralizer ha).symm).symm

theorem ncard_dadeSupport_mul_natCard (hD : IsDadeData L A H) (ha : a ∈ A) :
    (dadeSupport H a).ncard * Nat.card L
      = {b : G | ∃ l ∈ L, l * a * l⁻¹ = b}.ncard * Nat.card G := by
  rw [← ncard_setOf_conj_mul_natCard_inf_centralizer L a,
    ← hD.ncard_dadeSupport_mul_natCard_inf_centralizer ha]
  ring

theorem setOf_dadeSupport_eq (hD : IsDadeData L A H) (ha : a ∈ A) :
    {b ∈ A | dadeSupport H b = dadeSupport H a} = {b : G | ∃ l ∈ L, l * a * l⁻¹ = b} := by
  ext b
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hb, hba⟩
    obtain ⟨l, hl, hlba⟩ := (hD.dadeSupport_eq_iff_exists_conj hb ha).1 hba
    exact ⟨l⁻¹, inv_mem hl, by rw [← hlba]; group⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨hD.conj_mem ha hl, hD.dadeSupport_conj ha hl⟩

theorem ncard_totalDadeSupport_mul_natCard (hD : IsDadeData L A H) :
    (totalDadeSupport A H).ncard * Nat.card L = A.ncard * Nat.card G := by
  set T : Set (Set G) := (fun b => dadeSupport H b) '' A with hT
  have hTfin : T.Finite := (Set.toFinite A).image _
  have hpd : T.PairwiseDisjoint id := by
    rintro S ⟨b, hb, rfl⟩ S' ⟨c, hc, rfl⟩ hne
    rcases hD.dadeSupport_eq_or_disjoint hb hc with h | h
    · exact absurd h hne
    · exact h
  have hDsum : (totalDadeSupport A H).ncard = ∑ᶠ S ∈ T, S.ncard := by
    have hsu : totalDadeSupport A H = ⋃₀ T := by
      rw [hT, Set.sUnion_image]
      ext x
      simp [mem_totalDadeSupport_iff]
    rw [hsu, ← finsum_one (s := ⋃₀ T),
      finsum_mem_sUnion (f := fun _ : G => (1 : ℕ)) hpd hTfin fun x _ => Set.toFinite x]
    exact finsum_mem_congr rfl fun S _ => finsum_one
  have hAsum : A.ncard = ∑ᶠ S ∈ T, {c ∈ A | dadeSupport H c = S}.ncard := by
    have hun : ⋃ S ∈ T, {c ∈ A | dadeSupport H c = S} = A := by
      ext b
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      exact ⟨fun ⟨_, _, hb, _⟩ => hb, fun hb => ⟨dadeSupport H b, ⟨b, hb, rfl⟩, hb, rfl⟩⟩
    have h2 := hTfin.ncard_biUnion (s := fun S => {c ∈ A | dadeSupport H c = S})
      (fun S _ => Set.toFinite _) ?_
    · rw [hun] at h2; exact h2
    · rintro S hS S' hS' hne
      simp only [Set.disjoint_left, Set.mem_ofPred_eq]
      rintro d ⟨-, hd⟩ ⟨-, hd'⟩
      exact hne (hd ▸ hd')
  rw [hDsum, hAsum, finsum_mem_mul' _ _ hTfin, finsum_mem_mul' _ _ hTfin]
  refine finsum_mem_congr rfl ?_
  rintro S ⟨b, hb, rfl⟩
  rw [hD.setOf_dadeSupport_eq hb]
  exact hD.ncard_dadeSupport_mul_natCard hb

theorem ncard_totalDadeSupport_div_natCard (hD : IsDadeData L A H) :
    ((totalDadeSupport A H).ncard : ℚ) / Nat.card G = (A.ncard : ℚ) / Nat.card L := by
  have hG : (Nat.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hL : (Nat.card L : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [div_eq_div_iff hG hL]
  exact_mod_cast hD.ncard_totalDadeSupport_mul_natCard

end IsDadeData

end

end CFSG.FeitThompson
