module

public import CFSG.GH74.Uniqueness.SU.SU14J1
public import CFSG.GH74.Uniqueness.SU.SU4Sylow
public import CFSG.GH74.Uniqueness.SU.SU8Stmts
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport

public section

namespace CFSG.GH74.Uniqueness.SU.SU14

open Subgroup

theorem comm_of_hom_to_prod {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {Y : Type}
    [Group Y] (eY : Y ≃* alternatingGroup (Fin 5))
    (ψ : S →* Multiplicative (ZMod 2) × Y) (hψ : Function.Injective ψ) :
    ∀ a b : S, a * b = b * a := by
  have hYfin : Finite Y := Finite.of_equiv _ eY.symm.toEquiv
  let φ : S →* Y := (MonoidHom.snd (Multiplicative (ZMod 2)) Y).comp ψ
  have hT : IsPGroup 2 φ.range :=
    IsPGroup.of_surjective hS φ.rangeRestrict φ.rangeRestrict_surjective
  have hcomm := alt5_two_group_comm hT
    ((eY : Y →* alternatingGroup (Fin 5)).comp φ.range.subtype)
    (by
      intro u v h
      apply Subtype.ext
      exact eY.injective h)
  intro a b
  have h2 : φ a * φ b = φ b * φ a :=
    congrArg Subtype.val (hcomm ⟨φ a, ⟨a, rfl⟩⟩ ⟨φ b, ⟨b, rfl⟩⟩)
  apply hψ
  rw [map_mul, map_mul]
  apply Prod.ext
  · exact mul_comm _ _
  · exact h2

theorem two_pow_eq_eight_of_mul (k m m' : ℕ) (hm : m % 2 = 1) (hm' : m' % 2 = 1)
    (h : 2 ^ k * m = 8 * m') : 2 ^ k = 8 := by
  by_cases hk : 4 ≤ k
  · exfalso
    have h16 : 2 ^ 4 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk
    have : 16 ∣ 8 * m' := by
      rw [← h]
      exact Dvd.dvd.mul_right (by simpa using h16) _
    omega
  · have hk3 : k ≤ 3 := by omega
    interval_cases k <;> simp at h <;> omega

theorem hbar_inj_on_sylow {G : Type} [Group G] [Finite G] {S C : Subgroup G} (hS : IsPGroup 2 S)
    (hSC : S ≤ C) :
    Function.Injective ((QuotientGroup.mk' (pPrimeCore 2 ↥C)).comp (Subgroup.inclusion hSC)) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hmem : (Subgroup.inclusion hSC s : ↥C) ∈ pPrimeCore 2 ↥C :=
    (QuotientGroup.eq_one_iff _).mp hs
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hS s
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥C)) := CFSG.pPrimeCore_coprime_card
  have hdvd : orderOf (⟨Subgroup.inclusion hSC s, hmem⟩ : pPrimeCore 2 ↥C) ∣
      Nat.card (pPrimeCore 2 ↥C) := orderOf_dvd_natCard _
  have hord : orderOf (⟨Subgroup.inclusion hSC s, hmem⟩ : pPrimeCore 2 ↥C) = 2 ^ k := by
    rw [Subgroup.orderOf_mk, orderOf_injective (Subgroup.inclusion hSC)
      (Subgroup.inclusion_injective hSC) s, hk]
  rw [hord] at hdvd
  have h1 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hcop) hdvd
  rw [h1] at hk
  exact orderOf_eq_one_iff.mp hk

theorem pRank_sylow_eq_twoRank_hbar {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    {C : Subgroup G} (hSC : (S : Subgroup G) ≤ C) :
    Open.pRank 2 (S : Subgroup G) = Open.twoRank (SU8.Hbar C) := by
  have h1 : SU4.IsSylowIn C (S : Subgroup G) := (SU4.sylow_isSylowIn_top S).of_le hSC le_top
  have h2 : Open.pRank 2 (S : Subgroup G) = Open.pRank 2 C := h1.pRank_eq
  have h3 : Open.pRank 2 (⊤ : Subgroup ↥C) = Open.pRank 2 C :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_top_subgroup 2 Nat.prime_two C
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥C)) := CFSG.pPrimeCore_coprime_card
  have h4 : CFSG.pRank 2 (SU8.Hbar C) = CFSG.pRank 2 ↥C :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
      (pPrimeCore 2 ↥C) (Nat.prime_two.coprime_iff_not_dvd.mp hcop)
  have h5 : CFSG.pRank 2 (SU8.Hbar C) = Open.pRank 2 (⊤ : Subgroup (SU8.Hbar C)) :=
    CFSG.SectionRank.pRank_eq_open_pRank_top 2 _
  have h6 : CFSG.pRank 2 ↥C = Open.pRank 2 (⊤ : Subgroup ↥C) :=
    CFSG.SectionRank.pRank_eq_open_pRank_top 2 _
  show _ = Open.pRank 2 (⊤ : Subgroup (SU8.Hbar C))
  rw [h2, ← h3, ← h5, h4, h6]

theorem sylow_facts_of_hbar {G : Type} [Group G] [Finite G] (S : Sylow 2 G) {C : Subgroup G}
    (hSC : (S : Subgroup G) ≤ C) {Y : Type} [Group Y] (eY : Y ≃* alternatingGroup (Fin 5))
    (e : SU8.Hbar C ≃* Multiplicative (ZMod 2) × Y) :
    IsMulCommutative (S : Subgroup G) ∧ Nat.card (S : Subgroup G) = 8 ∧ 5 ∣ Nat.card C := by
  have hYfin : Finite Y := Finite.of_equiv _ eY.symm.toEquiv
  let ψ : ↥(S : Subgroup G) →* Multiplicative (ZMod 2) × Y :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥C)).comp (Subgroup.inclusion hSC))
  have hψ : Function.Injective ψ := e.injective.comp (hbar_inj_on_sylow S.isPGroup' hSC)
  have hcomm := comm_of_hom_to_prod S.isPGroup' eY ψ hψ
  have hcardY : Nat.card Y = 60 := by
    rw [Nat.card_congr eY.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin, Nat.factorial]
  have hcardZ : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hcardH : Nat.card (SU8.Hbar C) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hcardY, hcardZ]
  have hCcard : Nat.card C = 120 * Nat.card (pPrimeCore 2 ↥C) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥C)
    rw [h]
    have h' : Nat.card (↥C ⧸ pPrimeCore 2 ↥C) = 120 := hcardH
    rw [h']
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥C)) := CFSG.pPrimeCore_coprime_card
  have hOodd : Nat.card (pPrimeCore 2 ↥C) % 2 = 1 := Nat.odd_iff.mp (Nat.coprime_two_left.mp hcop)
  have h1 : SU4.IsSylowIn C (S : Subgroup G) := (SU4.sylow_isSylowIn_top S).of_le hSC le_top
  obtain ⟨-, k, m, hk, hm, hCm⟩ := SU4.isSylowIn_iff_card.mp h1
  refine ⟨⟨⟨fun a b => hcomm a b⟩⟩, ?_, ?_⟩
  · have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
    have hm' : (15 * Nat.card (pPrimeCore 2 ↥C)) % 2 = 1 := by omega
    have : 2 ^ k * m = 8 * (15 * Nat.card (pPrimeCore 2 ↥C)) := by
      rw [← hCm, hCcard]; ring
    rw [hk]
    exact two_pow_eq_eight_of_mul k m _ hm2 hm' this
  · rw [hCcard]
    exact Dvd.dvd.mul_right (by norm_num) _

end CFSG.GH74.Uniqueness.SU.SU14
