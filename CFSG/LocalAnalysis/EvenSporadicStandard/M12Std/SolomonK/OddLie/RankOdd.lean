module

public import CFSG.GH74.Filter.Small.Eigenbasis
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.Open.StatedAPI

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open Matrix CFSG.Open

theorem two_ne_zero_of_card_eq_odd_prime_pow {K : Type} [Field K] [Finite K] {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ m) : (2 : K) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((CharP.cast_eq_zero_iff K p 2).1 h'))

theorem twoRank_statedProj_le_of_odd {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) {n : ℕ}
    (hn : Odd (n + 1)) (H : Subgroup (GL (Fin (n + 1)) K))
    (hdet : ∀ x ∈ H, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) K).det = 1) :
    twoRank (StatedProj H) ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup H := (StatedScalars (Fin (n + 1)) K).subgroupOf H with hN
  have hNodd : ∀ x : H, x ∈ N → x ^ (n + 1) = 1 := by
    intro x hx
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx
    have hc' : (c : K) ^ (n + 1) = 1 := by
      have := hdet x x.2
      rw [← hc, GeneralLinearGroup.coe_scalar] at this
      simpa [Matrix.scalar_apply, Matrix.det_diagonal] using this
    have hc1 : c ^ (n + 1) = 1 := Units.ext (by simpa using hc')
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, hc1, map_one]
    rfl
  have hN2 : ¬ 2 ∣ Nat.card N := by
    intro h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h
    have h3 : orderOf x ∣ n + 1 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hNodd x x.2))
    rw [hx] at h3
    obtain ⟨m, hm⟩ := hn
    omega
  change CFSG.Open.pRank 2 (⊤ : Subgroup (H ⧸ N)) ≤ n
  rw [CFSG.SectionRank.pRank_quotient_eq N hN2]
  refine CFSG.SectionRank.pRank_le Nat.one_lt_two (fun E _ hE => ?_)
  have hE' : ∀ x ∈ E.map H.subtype, ∀ y ∈ E.map H.subtype, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := hE.1
    exact congrArg (fun z : E => ((z : H) : GL (Fin (n + 1)) K)) (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have h := CFSG.GH74.Filter.card_le_two_pow_of_elemAbelian_det h2 (E.map H.subtype) hE'
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact congrArg Subtype.val (hE.2 y hy))
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact hdet y y.2)
  rwa [Subgroup.card_map_of_injective H.subtype_injective] at h

theorem twoRank_le_of_PSL_odd {G : Type} [Group G] [Finite G] {n p f : ℕ} (hp2 : p ≠ 2)
    (hn : Odd n) (hm : StatedClassicalModel G .PSL n p f) : twoRank G ≤ n - 1 := by
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by obtain ⟨k, hk⟩ := hn; omega⟩
  have : Finite (StatedProj (StatedSL (m + 1) K)) := Finite.of_equiv G e.toEquiv
  rw [show twoRank G = twoRank (StatedProj (StatedSL (m + 1) K)) from
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two e]
  exact twoRank_statedProj_le_of_odd (two_ne_zero_of_card_eq_odd_prime_pow hp hp2 hK) hn _
    (fun x hx => CFSG.Open.StatedAPI.det_of_mem_statedSL hx)

theorem twoRank_le_of_PSU_odd {G : Type} [Group G] [Finite G] {n p f : ℕ} (hp2 : p ≠ 2)
    (hn : Odd n) (hm : StatedClassicalModel G .PSU n p f) : twoRank G ≤ n - 1 := by
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by obtain ⟨k, hk⟩ := hn; omega⟩
  have : Finite (StatedProj (StatedSU (m + 1) (p ^ f) K)) := Finite.of_equiv G e.toEquiv
  rw [show twoRank G = twoRank (StatedProj (StatedSU (m + 1) (p ^ f) K)) from
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two e]
  exact twoRank_statedProj_le_of_odd
    (two_ne_zero_of_card_eq_odd_prime_pow hp hp2 (m := f * 2) (by rw [hK, pow_mul])) hn _
    (fun x hx => CFSG.Open.StatedAPI.det_of_mem_statedSU hx)

theorem twoRank_le_four_of_PSL_five {G : Type} [Group G] [Finite G] {p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel G .PSL 5 p f) : twoRank G ≤ 4 :=
  twoRank_le_of_PSL_odd hp2 (by decide) hm

theorem twoRank_le_four_of_PSU_five {G : Type} [Group G] [Finite G] {p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel G .PSU 5 p f) : twoRank G ≤ 4 :=
  twoRank_le_of_PSU_odd hp2 (by decide) hm

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie
