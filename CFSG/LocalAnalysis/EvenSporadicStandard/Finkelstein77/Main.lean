module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.WeakClosure
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Simple
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977StandardCyclic

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77

open Subgroup CFSG.Assembly.ComponentType CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
  CFSG.GH74

theorem exists_orderOf_four_of_cyclic_sylow {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (hS : IsCyclic S) (h4 : 4 ≤ Nat.card S) : ∃ x : H, orderOf x = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (S : Subgroup H))
  have hord : orderOf g = Nat.card S := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hn2 : 2 ≤ n := by
    by_contra h
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨((g ^ (2 ^ (n - 2)) : (S : Subgroup H)) : H), ?_⟩
  rw [Subgroup.orderOf_coe,
    orderOf_pow_of_dvd (by positivity) (by rw [hord, hn]; exact Nat.pow_dvd_pow 2 (by omega)),
    hord, hn, Nat.pow_div (by omega) (by norm_num)]
  rw [show n - (n - 2) = 2 by omega]

theorem four_le_card_sylow_of_ne_two {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (heven : Even (Nat.card H)) (hne : Nat.card S ≠ 2) : 4 ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < (Nat.card H).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' (even_iff_two_dvd.mp heven)
  rw [Sylow.card_eq_multiplicity] at hne ⊢
  set e := (Nat.card H).factorization 2
  have he : 2 ≤ e := by
    by_contra h
    exact hne (by rw [show e = 1 by omega, pow_one])
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he

theorem card_sylow_eq_two_of_simple {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G))) (hS : IsCyclic S)
    (hI : HypothesisOne (L ⧸ center L)) (hrank : 3 ≤ CFSG.Open.twoRank (L ⧸ center L))
    (h25 : Asc76Lemma25) : Nat.card S = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have heven : Even (Nat.card (centralizer (L : Set G))) := hL.2.1
  have h4 : 4 ≤ Nat.card S := four_le_card_sylow_of_ne_two S heven hne
  by_cases hall : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) →
        IsPGroup 2 P → Nat.card P ≤ 2
  · obtain ⟨y, hy⟩ := exists_orderOf_four_of_cyclic_sylow S hS h4
    have hyC : (y : G) ∈ centralizer (L : Set G) := y.2
    have hy4 : orderOf (y : G) = 4 := by rw [Subgroup.orderOf_coe, hy]
    have hW := weaklyClosed_zpowers hL S hS hall hyC hy4
    have h2 : SectionalTwoRankLE G 2 := sectionalTwoRankLE_of_lemma25 h25 hnonab hy4 hW
    have hbound := ((h2.subgroup L).quotient (center L)).twoRank_le
    omega
  · push Not at hall
    obtain ⟨g, hg, P, hP, hP2, hPcard⟩ := hall
    have hP4 : 4 ≤ Nat.card P := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
      rw [hn] at hPcard ⊢
      have hn2 : 2 ≤ n := by
        by_contra h
        have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    obtain ⟨g', hg', R, T, hRC, hR, hRcard, hTg, hTN, hT, hTcard, hRT⟩ :=
      exists_full_conj_centralized hL S hS hg (hP.trans inf_le_left) (hP.trans inf_le_right)
        hP2 hP4
    exact not_hypothesisOne_of_full_conj hL S hS h4 hg' hRC hR hRcard hTg hTN hT hTcard hRT hI

end CFSG.EvenSporadicStandard.Finkelstein77
