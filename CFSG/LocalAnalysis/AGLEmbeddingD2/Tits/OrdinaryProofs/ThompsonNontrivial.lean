module

public import CFSG.Foundations.HigherElementaryThompson
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

open Subgroup

theorem exists_central_involution (T : Type*) [Group T] [Finite T] [Nontrivial T]
    (hT : IsPGroup 2 T) : ∃ z : T, z ∈ Subgroup.center T ∧ z ≠ 1 ∧ z ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (Subgroup.center T) := IsPGroup.center_nontrivial hT
  obtain ⟨n, hn⟩ := (hT.to_subgroup (Subgroup.center T)).exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := Subgroup.center T)
    rw [hn, pow_zero] at h1
    exact lt_irrefl _ h1
  have hdvd : 2 ∣ Nat.card (Subgroup.center T) := hn ▸ dvd_pow_self 2 hn0
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hg1 : (g : T) ≠ 1 := by
    intro h
    have h' : g = 1 := Subtype.ext h
    rw [h', orderOf_one] at hg
    norm_num at hg
  refine ⟨g, g.2, hg1, ?_⟩
  have h2 : g ^ 2 = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have h3 := congrArg Subtype.val h2
  simpa using h3

theorem le_pRank_of_card (S : Type*) [Group S] [Finite S] (A : Subgroup S)
    [IsElementaryAbelian 2 A] {k : ℕ} (hk : Nat.card A = 2 ^ k) : k ≤ pRank 2 S := by
  refine le_csSup ⟨Nat.card S, ?_⟩ ⟨A, inferInstance, hk⟩
  rintro r ⟨B, -, hB⟩
  have h1 : Nat.card B ≤ Nat.card S := Subgroup.card_le_card_group B
  rw [hB] at h1
  exact le_trans (Nat.lt_two_pow_self).le h1

theorem exists_max_rank_elemAbelian (S : Type*) [Group S] [Finite S] :
    ∃ A : Subgroup S, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ pRank 2 S := by
  have hne : {r : ℕ | ∃ A : Subgroup S, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r}.Nonempty :=
    ⟨0, Subgroup.zpowers (1 : S), IsElementaryAbelian.zpowers_of_pow_eq_one (one_pow 2), by
      rw [Nat.card_zpowers, orderOf_one, pow_zero]⟩
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup S, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} := by
    refine ⟨Nat.card S, ?_⟩
    rintro r ⟨B, -, hB⟩
    have h1 : Nat.card B ≤ Nat.card S := Subgroup.card_le_card_group B
    rw [hB] at h1
    exact le_trans (Nat.lt_two_pow_self).le h1
  obtain ⟨A, hA, hcard⟩ := Nat.sSup_mem hne hbdd
  exact ⟨A, hA, hcard⟩

theorem isElementaryAbelian_of_pointwise {p : ℕ} {G : Type*} [Group G] (B : Subgroup G)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hpow : ∀ x ∈ B, x ^ p = 1) :
    IsElementaryAbelian p B := CFSG.IsElementaryAbelian.of_forall hcomm hpow

theorem isElementaryAbelian_of_le {p : ℕ} {G : Type*} [Group G] {A B : Subgroup G}
    [IsElementaryAbelian p A] (hBA : B ≤ A) : IsElementaryAbelian p B :=
  CFSG.IsElementaryAbelian.of_le inferInstance hBA

theorem omegaOneCenter_ne_bot_of_isPGroup {S : Type*} [Group S] [Finite S] (J : Subgroup S)
    (hJ : IsPGroup 2 J) [Nontrivial J] : omegaOneCenter J ≠ ⊥ := by
  obtain ⟨z, hzc, hz1, hz2⟩ := exists_central_involution J hJ
  intro h
  have hmem : (z : S) ∈ omegaOneCenter J := by
    show (z : S) ∈ (Subgroup.center J).map J.subtype ∧ (z : S) ^ 2 = 1
    refine ⟨Subgroup.mem_map_of_mem J.subtype hzc, ?_⟩
    rw [← Subgroup.coe_pow, hz2, Subgroup.coe_one]
  rw [h] at hmem
  exact hz1 (Subtype.ext (Subgroup.mem_bot.mp hmem))

theorem omegaOneCenter_top_ne_bot {S : Type*} [Group S] [Finite S] (hS : IsPGroup 2 S)
    [Nontrivial S] : omegaOneCenter (⊤ : Subgroup S) ≠ ⊥ := by
  have : Nontrivial (⊤ : Subgroup S) := (Subgroup.nontrivial_iff_ne_bot _).mpr top_ne_bot
  exact omegaOneCenter_ne_bot_of_isPGroup ⊤ (hS.to_subgroup ⊤)

theorem higherElemThompson_zero_ne_bot {S : Type*} [Group S] [Finite S] (hS : IsPGroup 2 S)
    [Nontrivial S] : higherElemThompson S 0 ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, -, hz1, hz2⟩ := exists_central_involution S hS
  have hzA : IsElementaryAbelian 2 (Subgroup.zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  have hm : 1 ≤ pRank 2 S := by
    have hcard : Nat.card (Subgroup.zpowers z) = 2 ^ 1 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]
    exact le_pRank_of_card S _ hcard
  obtain ⟨A, hA, hAcard⟩ := exists_max_rank_elemAbelian S
  have := hA
  have hmem : A ∈ higherElemThompsonFamily S 0 := by
    rw [mem_higherElemThompsonFamily_iff, Nat.sub_zero]
    exact ⟨hA, hAcard⟩
  have hle : A ≤ higherElemThompson S 0 := le_sSup hmem
  intro h
  rw [h, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hAcard
  have h2 : 2 ^ 1 ≤ 2 ^ pRank 2 S := Nat.pow_le_pow_right (by norm_num) hm
  rw [← hAcard] at h2
  norm_num at h2

theorem higherElemThompsonOmega_one_ne_bot {S : Type*} [Group S] [Finite S] (hS : IsPGroup 2 S)
    (h2 : 2 ≤ pRank 2 S) : higherElemThompsonOmega S 1 ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hAcard⟩ := exists_max_rank_elemAbelian S
  have := hA
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) 2 (n := pRank 2 S - 1) (by
    rw [hAcard]
    exact pow_dvd_pow 2 (Nat.sub_le _ _))
  have hKle : K.map A.subtype ≤ A := Subgroup.map_subtype_le K
  have : IsElementaryAbelian 2 (K.map A.subtype) := isElementaryAbelian_of_le hKle
  have hBcard : Nat.card (K.map A.subtype) = 2 ^ (pRank 2 S - 1) := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hK]
  have hmem : K.map A.subtype ∈ higherElemThompsonFamily S 1 := by
    rw [mem_higherElemThompsonFamily_iff]
    exact ⟨inferInstance, hBcard⟩
  have hJ : higherElemThompson S 1 ≠ ⊥ := by
    intro h
    have hle : K.map A.subtype ≤ higherElemThompson S 1 := le_sSup hmem
    rw [h, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hBcard
    have h3 : 2 ^ 1 ≤ 2 ^ (pRank 2 S - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hBcard] at h3
    norm_num at h3
  have : Nontrivial (higherElemThompson S 1) := (Subgroup.nontrivial_iff_ne_bot _).mpr hJ
  unfold higherElemThompsonOmega
  exact omegaOneCenter_ne_bot_of_isPGroup (higherElemThompson S 1) (hS.to_subgroup _)

theorem two_le_pRank_of_elemAbelian {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (_hT : IsPGroup 2 T) {E : Subgroup G} (hET : E ≤ T) (hE : CFSG.Open.IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) : 2 ≤ pRank 2 ↥T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative E := hE.1
  have hEA : IsElementaryAbelian 2 E :=
    isElementaryAbelian_of_pointwise E
      (fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩))
      (fun x hx => hE.2 x hx)
  have := hEA
  have hE' : IsElementaryAbelian 2 (E.subgroupOf T) :=
    isElementaryAbelian_of_pointwise (E.subgroupOf T)
      (fun x hx y hy => by
        have h : (x : G) * (y : G) = (y : G) * (x : G) :=
          congrArg Subtype.val (mul_comm' (⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩ : E)
            ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩)
        exact Subtype.ext h)
      (fun x hx => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hE.2 _ (Subgroup.mem_subgroupOf.mp hx)))
  have := hE'
  have hcardE' : Nat.card (E.subgroupOf T) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv
  obtain ⟨j, hj⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hj2 : 2 ≤ j := by
    rcases Nat.lt_or_ge j 2 with hlt | hge
    · interval_cases j <;> rw [hj] at hE4 <;> norm_num at hE4
    · exact hge
  have hmemR : j ≤ pRank 2 ↥T :=
    le_pRank_of_card ↥T (E.subgroupOf T) (hcardE'.trans hj)
  exact le_trans hj2 hmemR

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
