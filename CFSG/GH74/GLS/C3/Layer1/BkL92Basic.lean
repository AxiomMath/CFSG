module

public import CFSG.GH74.GLS.C3.Layer1.BkIv81Core
public import CFSG.GH74.GLS.C3.Layer1.Back112Lift

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem gammaIn_le (L V : Subgroup G) : gammaIn L V ≤ L :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => inf_le_right

omit [Finite G] in
theorem le_gammaIn {L V E : Subgroup G} (hEV : E ≤ V) (hE : 1 ≤ pRank 2 ↥E) :
    normalizer (E : Set G) ⊓ L ≤ gammaIn L V :=
  le_iSup₂_of_le E hEV (le_iSup (fun _ : 1 ≤ pRank 2 ↥E => normalizer (E : Set G) ⊓ L) hE)

theorem exists_elem_of_pRank' {H : Type*} [Group H] [Finite H] (h : 1 ≤ pRank 2 H) :
    ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ pRank 2 H := by
  have hp : 1 < 2 := by norm_num
  have hne : {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r}.Nonempty :=
    (by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have h0 : 0 < sSup {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} := by
        unfold pRank at h; omega
      rw [hne] at h0
      simp at h0)
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} :=
    ⟨Nat.card H, by
      rintro r ⟨B, -, hB⟩
      calc r ≤ 2 ^ r := (Nat.lt_pow_self hp).le
        _ = Nat.card B := hB.symm
        _ ≤ Nat.card H := Subgroup.card_le_card_group B⟩
  exact Nat.sSup_mem hne hbdd

theorem pPrimeCoreOf_le_gammaIn {L M V : Subgroup G} (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hVM : V ≤ M) (hV : 2 ≤ pRank 2 ↥V) : pPrimeCoreOf 2 L ≤ gammaIn L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hAcard⟩ := exists_elem_of_pRank' (H := ↥V) (by omega)
  set E : Subgroup G := A.map V.subtype with hEdef
  have hEV : E ≤ V := Subgroup.map_subtype_le A
  have hEcard : Nat.card E = 2 ^ pRank 2 ↥V := by
    rw [hEdef, Subgroup.card_map_of_injective V.subtype_injective, hAcard]
  have hEel : CFSG.Open.IsElemAbelian 2 E := by
    have h1 : IsElementaryAbelian 2 ↥E := by
      have := hA
      exact IsElementaryAbelian.map (p := 2) (A := A) V.subtype
    exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).1 h1
  have hE4 : 2 ^ 2 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right (by norm_num) hV
  have hEN : E ≤ normalizer (pPrimeCoreOf 2 L : Set G) := fun e he =>
    U1a.mem_normalizer_pPrimeCoreOf hLn (hVM (hEV he))
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCoreOf 2 L)) :=
    Nat.coprime_two_left.mpr (TwoThin.card_pPrimeCoreOf_odd L)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two E (pPrimeCoreOf 2 L) hEel (by simpa using hE4) hEN hcop
  rw [← hgen]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨hSE, hScard⟩ := hS
  have hScard' : Nat.card S = 2 := by simpa using hScard
  obtain ⟨a, haS, ha1⟩ : ∃ a ∈ S, a ≠ 1 := by
    by_contra! h
    have hbot : S = ⊥ := (Subgroup.eq_bot_iff_forall S).mpr h
    rw [hbot, Subgroup.card_bot] at hScard'
    omega
  have hdvd : orderOf a ∣ 2 := hScard' ▸ Subgroup.orderOf_dvd_natCard S haS
  have ha2 : orderOf a = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hSa : zpowers a = S := Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haS)
    (by rw [hScard', Nat.card_zpowers, ha2])
  have hSV : S ≤ V := hSE.trans hEV
  have hS1 : 1 ≤ pRank 2 ↥S := by
    rw [← hSa]
    exact U1a.one_le_pRank_zpowers ha2
  have hcent : centralizer (S : Set G) ≤ normalizer (S : Set G) :=
    Subgroup.centralizer_le_normalizer (S : Set G)
  intro x hx
  exact le_gammaIn hSV hS1 ⟨hcent hx.2, TwoThin.pPrimeCoreOf_le L hx.1⟩

theorem inf_CMK_eq_bot {L M V : Subgroup G} (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hV2 : IsPGroup 2 ↥V) (hVM : V ≤ M) (hV : 2 ≤ pRank 2 ↥V) (hΓ : gammaIn L V ≠ L) :
    V ⊓ CMK M L = ⊥ := by
  by_contra hne
  have hW2 : IsPGroup 2 ↥(V ⊓ CMK M L) := hV2.to_inf_left
  obtain ⟨c, hc, hc2⟩ := exists_orderOf_two_of_ne_bot hW2 hne
  have hcV : c ∈ V := hc.1
  have hcC : c ∈ CMK M L := hc.2
  have hZ : zpowers c ≤ V := zpowers_le.mpr hcV
  have hZ1 : 1 ≤ pRank 2 ↥(zpowers c) := U1a.one_le_pRank_zpowers hc2
  have hOle := pPrimeCoreOf_le_gammaIn hLn hVM hV
  apply hΓ
  refine le_antisymm (gammaIn_le L V) fun l hl => ?_
  have hZ2 : IsPGroup 2 ↥(zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc2, pow_one])
  have hZC : zpowers c ≤ CMK M L := zpowers_le.mpr hcC
  obtain ⟨c', hc'L, hc'cent, hc'O⟩ := exists_centralizing_mem_coset hZ2
    (fun q hq k hk => hLn q (hVM (hZ hq)) k hk)
    (fun q hq k hk => (U1a.mem_CMK_iff.1 (hZC hq)).2.2.2 k hk) hl
  have hc'N : c' ∈ normalizer ((zpowers c : Subgroup G) : Set G) :=
    mem_normalizer_of_commute hc'cent
  have h1 : c' ∈ gammaIn L V := le_gammaIn hZ hZ1 ⟨hc'N, hc'L⟩
  have h2 : c'⁻¹ * l ∈ pPrimeCoreOf 2 L := by
    have := (pPrimeCoreOf 2 L).inv_mem hc'O
    simpa using this
  have h3 : c'⁻¹ * l ∈ gammaIn L V := hOle h2
  have : l = c' * (c'⁻¹ * l) := by group
  rw [this]
  exact (gammaIn L V).mul_mem h1 h3

end CFSG.GH74.GLS.C3.Layer1.Bk
