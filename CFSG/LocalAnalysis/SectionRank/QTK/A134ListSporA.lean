module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
import CFSG.LocalAnalysis.SectionRank.QTK.Witness3
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical
import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

theorem two_le_pRank_of_cubic {S : Type} [Group S] [Finite S] {r : ℕ} (hr : r.Prime) {x y : S}
    (hx : x ^ r = 1) (hz1 : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup S) := by
  have : Fact r.Prime := ⟨hr⟩
  have hzr : ⁅x, y⁆ ^ r = 1 := by
    rw [CFSG.SectionRank.LocalWitness.commutator_pow_eq hzx, hx, commutatorElement_one_left]
  refine CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_gens hx hzr hzx.symm ?_
    fun n hn => ?_
  · rintro rfl
    exact hz1 (commutatorElement_one_left y)
  · have hnr : ¬ r ∣ n := by
      rintro ⟨k, rfl⟩
      apply hz1
      rw [← hn, pow_mul, hx, one_pow]
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd hr).2 hnr).symm hr.one_lt
    have hxz : x = ⁅x, y⁆ ^ m := by
      rw [← hn, ← pow_mul, pow_eq_pow_mod _ hx, hm, pow_one]
    have hxy : Commute x y := by
      rw [hxz]
      exact hzy.pow_left m
    exact hz1 (commutatorElement_eq_one_iff_mul_comm.2 hxy.eq)

theorem card_closure_pair_le {S : Type} [Group S] [Finite S] {r : ℕ} (hr : 0 < r) {x y : S}
    (hy : y ^ r = 1) (n : ℕ) (hxy : x = y ^ n) :
    Nat.card (Subgroup.closure ({x, y} : Set S)) ≤ r := by
  have hle : Subgroup.closure ({x, y} : Set S) ≤ Subgroup.zpowers y := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, Subgroup.mem_zpowers y⟩
    rw [SetLike.mem_coe, hxy]
    exact Subgroup.npow_mem_zpowers y n
  refine (Subgroup.card_le_of_le hle).trans ?_
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd hr (orderOf_dvd_of_pow_eq_one hy)

theorem two_le_pRank_of_square {S : Type} [Group S] [Finite S] {r : ℕ} (hr : r.Prime) {x y : S}
    (hx : x ^ r = 1) (hy : y ^ r = 1) (hxy : x * y = y * x)
    (hc : Nat.card (Subgroup.closure ({x, y} : Set S)) = r ^ 2) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup S) := by
  have : Fact r.Prime := ⟨hr⟩
  have hlt : r < r ^ 2 := by nlinarith [hr.two_le]
  refine CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_gens hx hy hxy ?_
    fun n hn => ?_
  · rintro rfl
    have := card_closure_pair_le hr.pos hy 0 (pow_zero y).symm
    omega
  · have hle : Subgroup.closure ({x, y} : Set S) ≤ Subgroup.zpowers x := by
      rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨Subgroup.mem_zpowers x, ?_⟩
      rw [SetLike.mem_coe, ← hn]
      exact Subgroup.npow_mem_zpowers x n
    have h1 : Nat.card (Subgroup.zpowers x) ≤ r := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hr.pos (orderOf_dvd_of_pow_eq_one hx)
    have := (Subgroup.card_le_of_le hle).trans h1
    omega

theorem even_orderOf_of_commute_pow {S : Type} [Group S] [Finite S] {h u : S} (k : ℕ)
    (hk : Commute (h ^ 2 ^ k) u) (hu : ¬ Commute h u) : Even (orderOf h) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have h0 := orderOf_pos h
  rcases (by omega : 1 < orderOf h ∨ orderOf h = 1) with h1 | h1
  · have hcop : Nat.Coprime (2 ^ k) (orderOf h) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
    obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    apply hu
    have : h = (h ^ 2 ^ k) ^ t := by
      rw [← pow_mul, pow_eq_pow_mod _ (pow_orderOf_eq_one h), ht, pow_one]
    rw [this]
    exact hk.pow_left t
  · exact hu (by rw [orderOf_eq_one_iff.1 h1]; exact Commute.one_left u)

theorem one_le_localRank_of_commute_even {S : Type} [Group S] [Finite S] {r : ℕ} (hr : 1 < r)
    {h w : S} (hc : Commute h w) (hw : orderOf w = r) (he : Even (orderOf h)) :
    1 ≤ localRank r S := by
  obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hom
    rw [hom] at he
    exact (Nat.not_even_iff_odd.2 hm) he
  have hs : orderOf (h ^ m) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hm.pos.ne' (by rw [hom]; exact dvd_mul_left m _), hom,
      Nat.mul_div_cancel _ hm.pos]
  have hne : Subgroup.zpowers (h ^ m) ≠ ⊥ := fun hb => by
    have h1 : h ^ m = 1 := Subgroup.mem_bot.mp (hb ▸ Subgroup.mem_zpowers (h ^ m))
    rw [h1, orderOf_one] at hs
    exact (Nat.one_lt_two_pow ha).ne hs
  exact one_le_localRank_of_mem_normalizer hr hne (IsPGroup.of_card (by rw [Nat.card_zpowers, hs]))
    (mem_normalizer_zpowers (hc.pow_left m).symm) hw

theorem commute_iff_conj_eq {G : Type*} [Group G] {a b : G} :
    Commute a b ↔ MulAut.conj a b = b := by
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  rfl

theorem conj_sq_apply {G : Type*} [Group G] (a b : G) :
    MulAut.conj (a ^ 2) b = MulAut.conj a (MulAut.conj a b) := by
  rw [map_pow, pow_two, MulAut.mul_apply]

theorem mono_mul {G : Type*} [Group G] {x y : G} (hxy : Commute x y) (a b c d : ℕ) :
    x ^ a * y ^ b * (x ^ c * y ^ d) = x ^ (a + c) * y ^ (b + d) := by
  simp only [pow_add, mul_assoc]
  rw [← mul_assoc (y ^ b), ← (hxy.pow_pow c b).eq, mul_assoc]

theorem conj_mono {G : Type*} [Group G] {x y : G} {r : ℕ} (hxy : Commute x y) (hxr : x ^ r = 1)
    (hyr : y ^ r = 1) (c : MulAut G) {p q s t : ℕ} (hx : c x = x ^ p * y ^ q)
    (hy : c y = x ^ s * y ^ t) (a b : ℕ) :
    c (x ^ a * y ^ b) = x ^ ((p * a + s * b) % r) * y ^ ((q * a + t * b) % r) := by
  rw [map_mul, map_pow, map_pow, hx, hy, (hxy.pow_pow p q).mul_pow, (hxy.pow_pow s t).mul_pow,
    ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mono_mul hxy, ← pow_eq_pow_mod _ hxr,
    ← pow_eq_pow_mod _ hyr]

theorem orderOf_commutator_of_cubic {S : Type} [Group S] {r : ℕ} (hr : r.Prime) {x y : S}
    (hx : x ^ r = 1) (hz : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x) : orderOf ⁅x, y⁆ = r := by
  have : Fact r.Prime := ⟨hr⟩
  refine orderOf_eq_prime ?_ hz
  rw [CFSG.SectionRank.LocalWitness.commutator_pow_eq hzx, hx, commutatorElement_one_left]

theorem commutator_eq_one_of_commute_pow {S : Type} [Group S] {x y : S} {r k j : ℕ}
    (hx : x ^ r = 1) (hkj : k * j % r = 1) (hc : Commute (x ^ k) y) : ⁅x, y⁆ = 1 := by
  refine commutatorElement_eq_one_iff_mul_comm.2 ?_
  have hxk : x = (x ^ k) ^ j := by rw [← pow_mul, pow_eq_pow_mod _ hx, hkj, pow_one]
  rw [hxk]
  exact (hc.pow_left j).eq

end CFSG.SectionRank.QTK
