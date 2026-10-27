module

public import CFSG.Open.FusionDefs
import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.Open

private theorem card_perm_fin_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem exists_order_five_commute {G : Type*} [Group G] [Finite G] {g : G}
    (f : ↥(centralizer ({g} : Set G)) ⧸ fusionOddCore ↥(centralizer ({g} : Set G)) ≃*
      Equiv.Perm (Fin 5)) :
    ∃ k : G, orderOf k = 5 ∧ g * k = k * g := by
  classical
  set C : Subgroup G := centralizer ({g} : Set G) with hC
  let O : Subgroup ↥C := fusionOddCore ↥C
  have hquot : Nat.card (↥C ⧸ O) = 120 := by
    rw [Nat.card_congr f.toEquiv, card_perm_fin_five]
  have h5quot : 5 ∣ Nat.card (↥C ⧸ O) := by rw [hquot]; norm_num
  have hdvd : 5 ∣ Nat.card ↥C := dvd_trans h5quot (Subgroup.card_quotient_dvd_card O)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 5 hdvd
  refine ⟨(k : G), ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hk]
  · exact (mem_centralizer_singleton_iff.mp k.2).symm

theorem false_of_simple_le_centralizer {G : Type*} [Group G] [Finite G] {g : G}
    (f : ↥(centralizer ({g} : Set G)) ⧸ fusionOddCore ↥(centralizer ({g} : Set G)) ≃*
      Equiv.Perm (Fin 5))
    {X : Subgroup G} (hX : X ≤ centralizer ({g} : Set G)) (hXs : IsSimpleGroup ↥X)
    (hcard : Nat.card ↥X = 360) : False := by
  classical
  set C : Subgroup G := centralizer ({g} : Set G) with hC
  let O : Subgroup ↥C := fusionOddCore ↥C
  let X' : Subgroup ↥C := X.subgroupOf C
  let eX : X' ≃* ↥X := Subgroup.subgroupOfEquivOfLe hX
  haveI : IsSimpleGroup ↥X' := eX.isSimpleGroup
  let ψ : ↥C →* Equiv.Perm (Fin 5) := f.toMonoidHom.comp (QuotientGroup.mk' O)
  let ψ' : ↥X' →* Equiv.Perm (Fin 5) := ψ.comp X'.subtype
  let N : Subgroup ↥X' := ψ'.ker
  haveI : N.Normal := inferInstance
  have hcardX' : Nat.card ↥X' = 360 := by
    rw [Nat.card_congr eX.toEquiv, hcard]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
  · have hinj : Function.Injective ψ' := (MonoidHom.ker_eq_bot_iff ψ').mp hN
    have hle : Nat.card ↥X' ≤ Nat.card (Equiv.Perm (Fin 5)) :=
      Nat.card_le_card_of_injective ψ' hinj
    rw [hcardX', card_perm_fin_five] at hle
    omega
  · have hker : ∀ x : ↥X', ψ' x = 1 := by
      intro x
      have hxN : x ∈ N := by rw [hN]; exact Subgroup.mem_top x
      exact (MonoidHom.mem_ker (f := ψ')).1 hxN
    have hX'O : X' ≤ O := by
      intro x hx
      have h1 : f (QuotientGroup.mk' O x) = 1 := hker ⟨x, hx⟩
      have h3 : QuotientGroup.mk' O x = 1 := (map_eq_one_iff _ f.injective).mp h1
      exact (QuotientGroup.eq_one_iff x).mp h3
    have hdvd : Nat.card ↥X' ∣ Nat.card O := Subgroup.card_dvd_of_le hX'O
    have hOddO : Odd (Nat.card O) :=
      CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore ↥C
    have hOddX' : Odd (Nat.card ↥X') := Odd.of_dvd_nat hOddO hdvd
    have hEven : Even (Nat.card ↥X') := by rw [hcardX']; norm_num
    exact (Nat.not_even_iff_odd.2 hOddX') hEven

end CFSG.EvenSporadicStandard.HSStd.InvCent
