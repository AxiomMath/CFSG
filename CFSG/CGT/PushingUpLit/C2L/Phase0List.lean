module

public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.CGT.PushingUpLit.T2KSW.Defs
import CFSG.CGT.PushingUpLit.C2L.Phase0M24
import CFSG.CGT.PushingUpLit.E3A.Borel
import CFSG.CGT.PushingUpLit.T2KSW.Prop28
import CFSG.CGT.PushingUpLit.T2KSW.TransvCent
import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG.ABGLocalTools CFSG.Blueprint CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank
  CFSG.CGT.PushingUpLit.T2KSW

theorem list_false_le
    {G : Type} [Group G] [Finite G] {L T E : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hperf : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) (hT : IsSylowOf 2 T ⊤) (hcl : ClassLETwo T)
    (hLE : L ≤ Subgroup.centralizer (E : Set G))
    (hcount : 2 ^ (3 * n) * Nat.card E ≤ Nat.card T) (hstd : StdPair G E) : False := by
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
    exact not_classLETwo_of_mulEquiv_m24 hT e hcl

end CFSG.CGT.PushingUpLit.C2L
