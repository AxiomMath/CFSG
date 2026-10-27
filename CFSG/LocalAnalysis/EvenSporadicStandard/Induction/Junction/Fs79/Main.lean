module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Involution
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Layer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Induct
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Sol78LitHered

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

@[expose] def LayerBalanceKAt (G : Type) [Group G] [Finite G] : Prop :=
  CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    CFSG.oddCore G = ⊥ → ∀ (S : Subgroup G) (t : G),
    IsPGroup 2 S → orderOf t = 2 → t ∈ S → (∀ x ∈ S, x * t = t * x) →
      ∀ K : Subgroup G, IsCompIn K (centralizer (S : Set G)) →
        K ≤ layerIn (centralizer ((zpowers t : Subgroup G) : Set G))

theorem exists_involution_center {H : Type} [Group H] [Finite H] {T : Subgroup H}
    (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    ∃ t : H, orderOf t = 2 ∧ t ∈ T ∧ ∀ x ∈ T, x * t = t * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hne
  have hcen : Nontrivial (center ↥T) := hT.center_nontrivial
  have hC : IsPGroup 2 ↥(center ↥T) := hT.to_subgroup _
  have hdvd : 2 ∣ Nat.card (center ↥T) := by
    rcases hC.card_eq_or_dvd with h | h
    · exfalso
      have := (Nat.card_eq_one_iff_unique.1 h).1
      exact (not_nontrivial_iff_subsingleton.2 this) hcen
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥T)) 2 hdvd
  refine ⟨(((x : ↥T)) : H), ?_, (x : ↥T).2, fun y hy => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · have := Subgroup.mem_center_iff.1 x.2 ⟨y, hy⟩
    exact congrArg Subtype.val this

theorem cor23SAt_of_balance_at {H : Type} [Group H] [Finite H] (h13 : FS79Thm13UseAt H)
    (hbal : LayerBalanceKAt H) (hQ : Sol78RankOne) (hD : Sol78ExcClosed)
    (ih : ∀ (G : Type) [Group G] [Finite G],
      CFSG.SignalizerFunctorTheorem.IsSectionOf G H → Nat.card G < Nat.card H → Cor23SAt G) :
    Cor23SAt H := by
  intro hkp N hN hperf T₀ K hT₀ hK hA hP
  have hexc : NotExc K := ⟨hA, hP⟩
  by_cases hKN : K = N
  · refine ⟨0, fun _ => K, fun _ => T₀, fun _ => 1, ⟨hKN, fun i hi j hj _ => by omega,
      fun _ _ => ⟨hT₀, hK⟩, fun i h1 h2 => by omega, fun i h1 h2 => by omega,
      fun i h1 h2 => by omega⟩, rfl⟩
  have hT₀ne : T₀ ≠ ⊥ := fun h => hKN (hN.eq_of_isCompIn_bot (h ▸ hK))
  obtain ⟨t, ht2, htmem, htc⟩ := exists_involution_center hT₀ hT₀ne
  have hts : IsPGroup 2 ↥(zpowers t) := isPGroup_zpowers_of_orderOf_two ht2
  have hT : zpowers t ≠ ⊥ := fun h => by
    rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at ht2
    omega
  have hWT : T₀ ≤ normalizer ((zpowers t : Subgroup H) : Set H) := fun x hx =>
    mem_normalizer_zpowers_of_commute (htc x hx)
  have hK' : IsCompIn K (centralizer ((T₀ ⊔ zpowers t : Subgroup H) : Set H)) := by
    rw [sup_eq_left.2 (zpowers_le.2 htmem)]
    exact hK
  have hO : CFSG.oddCore H = ⊥ := hN.oddCore_eq_bot
  have hKL : K ≤ layerIn (centralizer ((zpowers t : Subgroup H) : Set H)) :=
    hbal hkp hO T₀ t hT₀ ht2 htmem htc K hK
  obtain ⟨M, hM, hKM⟩ := exists_isCompIn_le_conjClosure hWT hK' hKL
  have hJ := junction_conn ih hkp (Nat.card T₀) rfl hT hts hT₀ hWT hM hK' hKM hexc
  have hM' : IsCompIn M (centralizer ({t} : Set H)) := by
    rw [← centralizer_zpowers_eq]
    exact hM
  have hconn : LConn K N :=
    hJ.toLConn.trans
      (conn_of_involution_at h13 hQ hD ih hkp hN hperf ht2 hM' (hJ.toLConn.notExc hD hexc))
  obtain ⟨m, L, T, s, hl, h0, hm, -, hinj⟩ := Conn.exists_inj hconn
  exact ⟨m, L, T, s, hl.toChain hm hinj, h0⟩

theorem sol78Cor23SHered_of_balance (h13 : FS79Thm13UseHered)
    (hbal : ∀ (G : Type) [Group G] [Finite G], Balance.UHered G → LayerBalanceKAt G)
    (hQ : Sol78RankOne) (hD : Sol78ExcClosed) : Sol78Cor23SHered := by
  intro H _ _ hH
  induction hn : Nat.card H using Nat.strong_induction_on generalizing H hH with
  | _ n ih =>
    exact cor23SAt_of_balance_at (h13 H hH) (hbal H hH) hQ hD
      fun G _ _ hG hlt => ih (Nat.card G) (hn ▸ hlt) G (hH.of_section hG) rfl

end CFSG.EvenSporadicStandard.Induction.Junction
