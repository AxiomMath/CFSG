module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F7Syl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec8t84_conj_u {t : G} {S S' M0 : Subgroup G}
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) (hS'C : S' ≤ centralizer ({t} : Set G))
    (hS'2 : IsPGroup 2 S') (hcard : Nat.card S' = Nat.card S)
    (hSN : S ≤ normalizer (M0 : Set G)) (hS'N : S' ≤ normalizer (M0 : Set G)) :
    ∃ v : G, v ∈ centralizer ({t} : Set G) ∧ v ∈ normalizer (M0 : Set G) ∧
      S = S'.map (MulAut.conj v).toMonoidHom := by
  let H : Subgroup G := normalizer (M0 : Set G) ⊓ centralizer ({t} : Set G)
  have hSH : S ≤ H := le_inf hSN hS.1
  have hS'H : S' ≤ H := le_inf hS'N hS'C
  obtain ⟨Q, hQ⟩ := exists_isSylow2Of H
  have hcardQS : Nat.card Q ≤ Nat.card S :=
    sec8t84_card_le_of_sylow hS (le_trans hQ.1 inf_le_right) hQ.2.1
  have hSH' : IsSylow2Of S H :=
    sec8t84_isSylow2Of_of_card_ge hQ hSH hS.2.1 hcardQS
  have hS'H' : IsSylow2Of S' H :=
    sec8t84_isSylow2Of_of_card_ge hQ hS'H hS'2 (by rw [hcard]; exact hcardQS)
  obtain ⟨v, hvH, hveq⟩ :=
    sec8t84_two_syl_conj (H := H) (U := S) (V := S') hS'H' hSH hS.2.1 hcard.le
  have hv := Subgroup.mem_inf.mp hvH
  exact ⟨v, hv.2, hv.1, hveq⟩

theorem sec8t84_S_le_normalizer {t : G} {L S : Subgroup G}
    (hSC : S ≤ centralizer ({t} : Set G)) (hSL : S ≤ normalizer (L : Set G)) :
    S ≤ normalizer ((zpowers t ⊔ (S ⊓ L) : Subgroup G) : Set G) := by
  intro x hx
  have hxcent : x ∈ centralizer (zpowers t : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hSC hx
  have hxt : x ∈ normalizer (zpowers t : Set G) :=
    Subgroup.centralizer_le_normalizer (zpowers t : Set G) hxcent
  have hxS : x ∈ normalizer (S : Set G) := S.le_normalizer hx
  have hxL : x ∈ normalizer (L : Set G) := hSL hx
  have hxi : x ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hxS, hxL⟩
  exact Subgroup.inf_normalizer_le_normalizer_sup (zpowers t) (S ⊓ L) ⟨hxt, hxi⟩

end CFSG.OddStandard.SmallF3.Omega
