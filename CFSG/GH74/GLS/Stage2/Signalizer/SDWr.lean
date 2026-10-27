module

import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupShapes
import CFSG.LocalAnalysis.ComponentInitial.CyclicIndexTwoRank
public import CFSG.CharacterTheory.Wreathed.Coordinates
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt42
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.Wreathed

theorem zmod_two_nsmul_eq_zero (n : ℕ) (hn : 1 ≤ n) (x : ZMod (2 ^ n)) (hx : 2 • x = 0) :
    x = 0 ∨ x = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) := by
  have hk : x.val < 2 ^ n := ZMod.val_lt x
  have hxk : (x : ZMod (2 ^ n)) = ((x.val : ℕ) : ZMod (2 ^ n)) := (ZMod.natCast_zmod_val x).symm
  have h2 : ((2 * x.val : ℕ) : ZMod (2 ^ n)) = 0 := by
    rw [Nat.cast_mul, ← hxk]
    simpa [two_nsmul, two_mul] using hx
  rw [ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨j, hj⟩ := h2
  obtain ⟨v, hv⟩ : ∃ v, v = x.val := ⟨_, rfl⟩
  rw [← hv] at hk hj hxk
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 0 < 2 ^ (n - 1) := by positivity
  have hjlt : j < 2 := by
    by_contra hcon
    have h3 : 2 ≤ j := by omega
    have : 2 ^ n * 2 ≤ 2 ^ n * j := Nat.mul_le_mul_left _ h3
    rw [hpow] at hj hk this
    omega
  interval_cases j
  · left
    have : v = 0 := by omega
    rw [hxk, this]; simp
  · right
    have : v = 2 ^ (n - 1) := by rw [hpow] at hj; omega
    rw [hxk, this]

theorem element_eq_iff (m : ℕ) {a b a' b' : ZMod m} {e e' : ZMod 2} :
    element m a b e = element m a' b' e' ↔ a = a' ∧ b = b' ∧ e = e' := by
  constructor
  · intro h
    have := element_injective m (a₁ := (a, b, e)) (a₂ := (a', b', e')) h
    simpa [Prod.ext_iff] using this
  · rintro ⟨rfl, rfl, rfl⟩; rfl

theorem element_base_sq_eq_one (m : ℕ) (c d : ZMod m) :
    element m c d 0 ^ 2 = 1 ↔ 2 • c = 0 ∧ 2 • d = 0 := by
  rw [element_base_pow, ← element_zero m, element_eq_iff]
  simp

theorem element_swap_sq_eq_one (m : ℕ) (c d : ZMod m) :
    element m c d 1 ^ 2 = 1 ↔ c + d = 0 := by
  rw [element_swap_sq, ← element_zero m, element_eq_iff]
  simp

theorem wr_card_le_four (n : ℕ) (hn : 1 ≤ n) (E : Subgroup (Wreath (2 ^ n)))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card E ≤ 4 := by
  classical
  set h : ZMod (2 ^ n) := ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) with hh
  have hhh : h + h = 0 := by
    have h1 : ((2 * 2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      refine ⟨1, ?_⟩
      rw [← pow_succ']
      have : n - 1 + 1 = n := by omega
      rw [this]; ring
    rw [Nat.cast_mul] at h1
    simpa [hh, two_mul] using h1
  have hcoord : ∀ g : Wreath (2 ^ n), ∃ c d : ZMod (2 ^ n), ∃ e : ZMod 2, g = element (2 ^ n) c d e := fun g => by
    obtain ⟨⟨c, d, e⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective g
    exact ⟨c, d, e, rfl⟩
  have hfin : ∀ F : Finset (Wreath (2 ^ n)), (E : Set (Wreath (2 ^ n))) ⊆ ↑F → F.card ≤ 4 → Nat.card E ≤ 4 := by
    intro F hF hc
    have h1 : (E : Set (Wreath (2 ^ n))).ncard ≤ (F : Set (Wreath (2 ^ n))).ncard :=
      Set.ncard_le_ncard hF (Finset.finite_toSet F)
    rw [Set.ncard_coe_finset] at h1
    have h2 : Nat.card E = (E : Set (Wreath (2 ^ n))).ncard := (Nat.card_coe_set_eq _).symm
    omega
  by_cases hs : ∃ a b : ZMod (2 ^ n), element (2 ^ n) a b 1 ∈ E
  · obtain ⟨a, b, ht⟩ := hs
    refine hfin {element (2 ^ n) 0 0 0, element (2 ^ n) h h 0, element (2 ^ n) a b 1, element (2 ^ n) (a + h) (b + h) 1} ?_
      Finset.card_le_four
    intro g hg
    obtain ⟨c, d, e, rfl⟩ := hcoord g
    have hg2 := hsq _ hg
    have hcm := hcomm _ ht _ hg
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases swap_exponent_cases e with rfl | rfl
    · obtain ⟨hc2, hd2⟩ := (element_base_sq_eq_one (2 ^ n) c d).mp hg2
      rw [element_swap_mul, element_base_mul, element_eq_iff] at hcm
      have hcd : d = c := by linear_combination hcm.1
      subst hcd
      rcases zmod_two_nsmul_eq_zero n hn d hc2 with rfl | hd
      · left; rfl
      · right; left; rw [hd]
    · have hcd := (element_swap_sq_eq_one (2 ^ n) c d).mp hg2
      have hab := (element_swap_sq_eq_one (2 ^ n) a b).mp (hsq _ ht)
      rw [element_swap_mul, element_swap_mul, element_eq_iff] at hcm
      have h2 : 2 • (a - c) = 0 := by
        rw [two_nsmul]
        linear_combination hcm.1 + hab - hcd
      rcases zmod_two_nsmul_eq_zero n hn (a - c) h2 with h3 | h3
      · have hc : c = a := by linear_combination -h3
        have hd : d = b := by linear_combination hcd - hab - hc
        subst hc; subst hd
        right; right; left; rfl
      · rw [← hh] at h3
        have hc : c = a + h := by linear_combination -h3 - hhh
        have hd : d = b + h := by linear_combination hcd - hab - hc - hhh
        subst hc; subst hd
        right; right; right; rfl
  · push Not at hs
    refine hfin {element (2 ^ n) 0 0 0, element (2 ^ n) h 0 0, element (2 ^ n) 0 h 0, element (2 ^ n) h h 0} ?_
      Finset.card_le_four
    intro g hg
    obtain ⟨c, d, e, rfl⟩ := hcoord g
    have hg2 := hsq _ hg
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases swap_exponent_cases e with rfl | rfl
    · obtain ⟨hc2, hd2⟩ := (element_base_sq_eq_one (2 ^ n) c d).mp hg2
      rcases zmod_two_nsmul_eq_zero n hn c hc2 with rfl | hc <;>
        rcases zmod_two_nsmul_eq_zero n hn d hd2 with rfl | hd
      · left; rfl
      · right; right; left; rw [hd]
      · right; left; rw [hc]
      · right; right; right; rw [hc, hd]
    · exact absurd hg (hs c d)

theorem pRank_semidihedral_le_two {R : Type} [Group R] [Finite R] {n : ℕ} (hn : 4 ≤ n)
    (e : R ≃* CFSG.Open.SemidihedralGroup n) : CFSG.pRank 2 R ≤ 2 := by
  obtain ⟨ρ, σ, hidx, -, -⟩ :=
    CFSG.ComponentClassification.AschbacherToolkit.exists_inverting_generators_of_semidihedral hn e
  exact CFSG.LocalAnalysis.ComponentInitial.cyclic_index_two_rank_bound
    (H := Subgroup.zpowers ρ) inferInstance hidx.le

theorem pRank_wreathed_le_two {R : Type} [Group R] [Finite R] {n : ℕ} (hn : 1 ≤ n)
    (e : R ≃* CFSG.Open.WreathedTwoGroup n) : CFSG.pRank 2 R ≤ 2 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have hcomm : ∀ x ∈ E.map e.toMonoidHom, ∀ y ∈ E.map e.toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ E.map e.toMonoidHom, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  have h4 := wr_card_le_four n hn (E.map e.toMonoidHom) hcomm hsq
  rw [Subgroup.card_map_of_injective e.injective] at h4
  calc Nat.card E ≤ 4 := h4
    _ = 2 ^ 2 := by norm_num

theorem sdWr_rank2 : SDWr_rank2 := by
  intro G _ _ S hS
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact pRank_semidihedral_le_two hn e
  · exact pRank_wreathed_le_two (by omega) e

end CFSG.GH74.GLS.Stage2.Signalizer
