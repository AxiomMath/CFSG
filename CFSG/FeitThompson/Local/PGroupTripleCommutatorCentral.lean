module

public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Local.NormalSubgroupCentralPrimeTorsion

open scoped commutatorElement

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ}

theorem isMulCommutative_of_natCard_le_sq (hp : p.Prime) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (hcard : Nat.card P ≤ p ^ 2) : IsMulCommutative P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn2 : n ≤ 2 := by
    rw [hn] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  rcases Nat.lt_or_ge n 2 with h1 | h2
  ·
    have hdvd : Nat.card P ∣ p := by
      rw [hn]
      simpa using pow_dvd_pow p (show n ≤ 1 by omega)
    have := isCyclic_of_card_dvd_prime hdvd
    infer_instance
  · have hn' : n = 2 := le_antisymm hn2 h2
    subst hn'
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hn

theorem nilpotencyClass_le_of_natCard_le_pow (hp : p.Prime) (n : ℕ) :
    ∀ {P : Type*} [Group P] [Finite P], IsPGroup p P → Nat.card P ≤ p ^ (n + 2) →
      Group.nilpotencyClass P ≤ n + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  induction n with
  | zero =>
    intro P _ _ hP hcard
    have := hP.isNilpotent
    have := isMulCommutative_of_natCard_le_sq hp hP (by simpa using hcard)
    exact Group.IsNilpotent.nilpotencyClass_le_one_iff.2 ‹_›
  | succ n ih =>
    intro P _ _ hP hcard
    have hnil := hP.isNilpotent
    rcases subsingleton_or_nontrivial P with hs | hs
    · simp [Group.nilpotencyClass_zero_iff_subsingleton.2 hs]
    · obtain ⟨m, hm⟩ := hP.exists_card_eq
      have hZ : Subgroup.center P ≠ ⊥ := by
        have h := inf_center_ne_bot (⊤ : Subgroup P) hp hm top_ne_bot
        simpa using h
      have hnt : Nontrivial (Subgroup.center P) := (Subgroup.nontrivial_iff_ne_bot _).2 hZ
      obtain ⟨k, hk0, hk⟩ := (IsPGroup.nontrivial_iff_card (hP.to_subgroup _)).1 hnt
      have hple : p ≤ Nat.card (Subgroup.center P) := by
        rw [hk]
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk0
      have hq : Nat.card (P ⧸ Subgroup.center P) ≤ p ^ (n + 2) := by
        have h1 : Nat.card (P ⧸ Subgroup.center P) * p ≤ p ^ (n + 2) * p :=
          calc Nat.card (P ⧸ Subgroup.center P) * p
              ≤ Nat.card (P ⧸ Subgroup.center P) * Nat.card (Subgroup.center P) :=
                Nat.mul_le_mul_left _ hple
            _ = Nat.card P := (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
            _ ≤ p ^ (n + 3) := hcard
            _ = p ^ (n + 2) * p := by ring
        exact Nat.le_of_mul_le_mul_right h1 hp.pos
      have hquot := ih (hP.to_quotient (Subgroup.center P)) hq
      have := (hP.to_quotient (Subgroup.center P)).isNilpotent
      have := Group.nilpotencyClass_le_of_ker_le_center
        (QuotientGroup.mk' (Subgroup.center P)) (by rw [QuotientGroup.ker_mk'])
      omega

theorem commutator_commutator_top_le_center (hp : p.Prime) {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup p R) (hcard : Nat.card R ≤ p ^ 4) :
    ⁅⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆, (⊤ : Subgroup R)⁆ ≤ Subgroup.center R := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent R := hR.isNilpotent
  have h := nilpotencyClass_le_of_natCard_le_pow hp 2 hR (by simpa using hcard)
  have h3 : Subgroup.lowerCentralSeries (⊤ : Subgroup R) 3 = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.2 h
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
    Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero] at h3
  rw [← Subgroup.commutator_top_left_eq_bot_iff_le_center, Subgroup.commutator_comm]
  exact h3

theorem commutator_commutator_le_center (hp : p.Prime) {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup p R) (hcard : Nat.card R ≤ p ^ 4) :
    ⁅_root_.commutator R, (⊤ : Subgroup R)⁆ ≤ Subgroup.center R := by
  rw [commutator_def]
  exact commutator_commutator_top_le_center hp hR hcard

theorem commutatorElement_commutatorElement_mem_center (hp : p.Prime) {R : Type*} [Group R]
    [Finite R] (hR : IsPGroup p R) (hcard : Nat.card R ≤ p ^ 4) (x y z : R) :
    ⁅⁅x, y⁆, z⁆ ∈ Subgroup.center R :=
  commutator_commutator_top_le_center hp hR hcard
    (Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
      (Subgroup.mem_top z))

theorem commutator_commutator_le_inf_centralizer (hp : p.Prime) {G : Type*} [Group G]
    (R : Subgroup G) [Finite R] (hR : IsPGroup p R) (hcard : Nat.card R ≤ p ^ 4) :
    ⁅⁅R, R⁆, R⁆ ≤ R ⊓ Subgroup.centralizer (R : Set G) := by
  have hmap : Subgroup.map R.subtype ⁅⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆, (⊤ : Subgroup R)⁆
      = ⁅⁅R, R⁆, R⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← hmap]
  refine le_trans (Subgroup.map_mono (commutator_commutator_top_le_center hp hR hcard)) ?_
  rintro x ⟨z, hz, rfl⟩
  refine Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩)

end

end CFSG.FeitThompson
