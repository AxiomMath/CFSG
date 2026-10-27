module

public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.CGT.PushingUpLit.E3A.Borel
import CFSG.CGT.PushingUpLit.T2KSW.TransvCent
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Mathieu.M24
import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG.ABGLocalTools CFSG.Blueprint CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem false_of_perfect_ne_bot_of_solvable {G : Type*} [Group G] {L : Subgroup G}
    (hperf : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) (hsolv : Group.IsSolvable ↥L) : False := by
  have hnt : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 hL1
  have h1 : (commutator ↥L).map L.subtype = L := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact hperf
  have h2 : commutator ↥L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L).ne h2

theorem eq_bot_of_perfect_of_pairwise_comm {G : Type*} [Group G] {L : Subgroup G}
    (hperf : ⁅L, L⁆ = L) (hcomm : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) : L = ⊥ := by
  have : ⁅L, L⁆ ≤ ⊥ := Subgroup.commutator_le.2 fun x hx y hy => by
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm x hx y hy
  rw [hperf] at this
  exact le_bot_iff.1 this

theorem card_isSylowOf_top_eq_two_pow {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsSylowOf 2 T ⊤) {a r : ℕ} (hr : Odd r) (hG : Nat.card G = 2 ^ a * r) :
    Nat.card T = 2 ^ a := by
  have h := hT.card_eq
  rw [Subgroup.card_top, hG, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hr.pos.ne',
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by simpa using hr.not_two_dvd_nat), add_zero] at h
  exact h

theorem card_nativeM22_eq : Nat.card NativeSporadic.M22 = 443520 := by
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
  exact le_antisymm ((Nat.card_le_card_of_surjective _
    CFSG.Sporadic.Bridge.M22.toNative_surjective).trans hle)
    CFSG.Sporadic.Bridge.M22.le_card_native

theorem le_centralizer_inf_centralizer {G : Type*} [Group G] (L T : Subgroup G) :
    L ≤ Subgroup.centralizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  fun l hl => Subgroup.mem_centralizer_iff.2 fun _ he =>
    (Subgroup.mem_centralizer_iff.1 he.2 l hl).symm

theorem list_false
    {G : Type} [Group G] [Finite G] {L T E : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hperf : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) (hT : IsSylowOf 2 T ⊤)
    (hLE : L ≤ Subgroup.centralizer (E : Set G))
    (hcount : 2 ^ (3 * n) * Nat.card E < Nat.card T) (hstd : StdPair G E) : False := by
  have h64 : 64 ≤ 2 ^ (3 * n) :=
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have borel : BorelTwoTransitive G E → False := by
    rintro ⟨-, S, hS⟩
    have hLS : L ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
      hS ▸ hLE.trans (Subgroup.centralizer_le_normalizer _)
    have hsolv := E3A.isSolvable_normalizer_sylow S
    exact false_of_perfect_ne_bot_of_solvable hperf hL1
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLS))
  rcases hstd.listGroup with ⟨m, s, hm, hs', hmod⟩ | ⟨s, hs', hmod⟩ | ⟨s, hodd, hs3, hmod⟩ |
    ⟨k, hk6, hk9, he⟩ | hM22 | hM23 | hM24
  · by_cases hm3 : 3 ≤ m
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
      obtain ⟨-, hEc⟩ := hstd.of_psl hm3 K hK e
      exact hL1 (eq_bot_of_perfect_of_pairwise_comm hperf
        (comm_of_le_centralizer_transv (by omega) K hK e hEc hLE))
    · have hm2 : m = 2 := by omega
      subst hm2
      exact borel (hstd.of_psl2 hmod).2.2
  · exact borel (hstd.of_psu3 hs' hmod).2.2
  · exact borel (hstd.of_sz hodd hs3 hmod).2.2
  · obtain ⟨e⟩ := he
    have hE := hstd.card_alternating hk6 hk9 ⟨e⟩
    have hG : Nat.card G = k.factorial / 2 := by
      have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hTE : Nat.card T = 8 ∧ Nat.card E = 4 ∨ Nat.card T = 64 ∧ Nat.card E = 8 := by
      interval_cases k
      · exact Or.inl ⟨card_isSylowOf_top_eq_two_pow hT (a := 3) (r := 45) (by decide)
          (by rw [hG]; decide), by simpa using hE⟩
      · exact Or.inl ⟨card_isSylowOf_top_eq_two_pow hT (a := 3) (r := 315) (by decide)
          (by rw [hG]; decide), by simpa using hE⟩
      · exact Or.inr ⟨card_isSylowOf_top_eq_two_pow hT (a := 6) (r := 315) (by decide)
          (by rw [hG]; decide), by simpa using hE⟩
      · exact Or.inr ⟨card_isSylowOf_top_eq_two_pow hT (a := 6) (r := 2835) (by decide)
          (by rw [hG]; decide), by simpa using hE⟩
    rcases hTE with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hcount <;> omega
  · obtain ⟨e⟩ := hM22
    have hG : Nat.card G = 2 ^ 7 * 3465 := by
      rw [show Nat.card G = Nat.card ↥NativeSporadic.M22 from Nat.card_congr e.toEquiv,
        card_nativeM22_eq]
      norm_num
    rw [card_isSylowOf_top_eq_two_pow hT (by decide) hG,
      hstd.card_sporadic (Or.inl ⟨e⟩)] at hcount
    omega
  · obtain ⟨e⟩ := hM23
    have hG : Nat.card G = 2 ^ 7 * 79695 := by
      rw [show Nat.card G = Nat.card ↥NativeSporadic.M23 from Nat.card_congr e.toEquiv,
        CFSG.Sporadic.Schreier.m23_card]
      norm_num
    rw [card_isSylowOf_top_eq_two_pow hT (by decide) hG,
      hstd.card_sporadic (Or.inr (Or.inl ⟨e⟩))] at hcount
    omega
  · obtain ⟨e⟩ := hM24
    have hG : Nat.card G = 2 ^ 10 * 239085 := by
      rw [show Nat.card G = Nat.card ↥NativeSporadic.M24 from Nat.card_congr e.toEquiv,
        CFSG.Sporadic.Mathieu.card_M24]
      norm_num
    rw [card_isSylowOf_top_eq_two_pow hT (by decide) hG,
      hstd.card_sporadic (Or.inr (Or.inr ⟨e⟩))] at hcount
    omega

end CFSG.CGT.PushingUpLit.T2KSW
