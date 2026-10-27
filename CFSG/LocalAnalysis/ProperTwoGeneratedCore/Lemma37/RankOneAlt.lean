module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneQuaternion

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem card_sylow_eq_of_mulEquiv {p : ℕ} [Fact p.Prime] {K L : Type*} [Group K] [Group L]
    [Finite K] (e : K ≃* L) (P : Sylow p K) (Q : Sylow p L) :
    Nat.card (P : Subgroup K) = Nat.card (Q : Subgroup L) := by
  have : Finite L := Finite.of_equiv _ e.toEquiv
  rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv]

theorem nonempty_mulEquiv_alternatingGroup_five_of_isBenderGroup
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) (P : Sylow 2 K) (hP : Nat.card (P : Subgroup K) = 4) :
    Nonempty (K ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hK with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · have : Finite (CFSG.Theory.Comparator.PSL2Model n) := Finite.of_equiv _ e.toEquiv
    obtain ⟨Q⟩ : Nonempty (Sylow 2 (CFSG.Theory.Comparator.PSL2Model n)) := inferInstance
    have hQ := ((bender_psl2_borel_full n hn) Q).2.2.2.2
    rw [← card_sylow_eq_of_mulEquiv e P Q, hP, pow_one] at hQ
    have hn2 : n = 2 := by
      have h4 : (2 : ℕ) ^ n = 2 ^ 2 := by rw [← hQ]; norm_num
      exact Nat.pow_right_injective (le_refl 2) h4
    subst hn2
    obtain ⟨e₅⟩ := BenderFacts.nonempty_psl2Binary_two_mulEquiv_alternatingGroup_five
    exact ⟨e.trans e₅⟩
  · exfalso
    have hmodel : CFSG.Theory.Comparator.SzModel n = Sz n := CFSG.Models.benderSzModel_eq_sz n
    let e' : K ≃* Sz n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (Sz n) := Finite.of_equiv _ e'.toEquiv
    obtain ⟨Q⟩ : Nonempty (Sylow 2 (Sz n)) := inferInstance
    have hQ := ((bender_suzuki_borel_full n hn) Q).2.2.2.2
    rw [← card_sylow_eq_of_mulEquiv e' P Q, hP] at hQ
    have h8 : 2 ^ 3 ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h64 : (2 ^ 3) ^ 2 ≤ (2 ^ (2 * n + 1)) ^ 2 := Nat.pow_le_pow_left h8 2
    omega
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmodel : CFSG.Theory.Comparator.PSU3Model n = PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
    let e' : K ≃* PSU3 2 n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (PSU3 2 n) := Finite.of_equiv _ e'.toEquiv
    obtain ⟨Q⟩ : Nonempty (Sylow 2 (PSU3 2 n)) := inferInstance
    have hQ := ((bender_psu3_borel_full n hn) Q).2.2.2.2
    rw [← card_sylow_eq_of_mulEquiv e' P Q, hP] at hQ
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h64 : (2 ^ 2) ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h4 3
    omega

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J)
include h

theorem card_sylow_quotient
    (Q : Sylow 2 (J ⧸ Subgroup.center J)) :
    Nat.card (Q : Subgroup (J ⧸ Subgroup.center J)) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 J) := inferInstance
  obtain ⟨e⟩ := h.sylow_mulEquiv_quaternion_two T
  obtain ⟨d⟩ := h.sylow_quotient_mulEquiv T (r := 3) le_rfl e
  rw [← card_sylow_eq_of_mulEquiv (MulEquiv.refl _)
    (T.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J))) Q,
    Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
  norm_num

theorem nonempty_mulEquiv_alternatingGroup_five :
    Nonempty (J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 (J ⧸ Subgroup.center J)) := inferInstance
  exact nonempty_mulEquiv_alternatingGroup_five_of_isBenderGroup h.isBenderGroup Q
    (h.card_sylow_quotient Q)

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
