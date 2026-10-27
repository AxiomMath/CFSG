module

public import CFSG.LocalAnalysis.OddStandard.GH71.Unbalanced3
public import CFSG.LocalAnalysis.OddStandard.GH71.Basic
public import CFSG.LocalAnalysis.OddStandard.GH71.Unbalanced

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

omit [Finite G] in
theorem centralizer_zpowers (x : G) :
    centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem three_dvd_of_unbalanced (h : Ctx71 G z S U u) (hB : AlternatingBalanceData 11)
    (hD : ¬ pPrimeCoreOf 2 (Cen z) ⊓ Cen u ≤ pPrimeCoreOf 2 (Cen u)) :
    3 ∣ (pPrimeCoreOf 2 (Cen z) ⊓ Cen u ⊓ pPrimeCoreOf 2 (Cen u)).relIndex
      (pPrimeCoreOf 2 (Cen z) ⊓ Cen u) := by
  set D := pPrimeCoreOf 2 (Cen z) ⊓ Cen u with hDdef
  have hDu : D ≤ Cen u := inf_le_right
  set T := S ⊓ centralizer ({u} : Set G) with hT
  have hTu : T ≤ Cen u := inf_le_right
  have hT2 : IsPGroup 2 ↥T := h.S2.to_le inf_le_left
  have hTD : T ≤ normalizer (D : Set G) := fun t ht =>
    inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pPrimeCoreOf' (Cen z) (h.S_le ht.1), le_normalizer ht.2⟩
  have hcovu := h.cover_of_involution h.orderOf_u
  have hcardT : Nat.card ↥(barIn (Cen u) T) = 2 ^ (if 11 ≤ 9 then 6 else 7) := by
    rw [IVK812.card_barIn_two hTu hT2, h.card_T₂]; rfl
  have hno := hB.no_odd' (HBar (Cen u)) hcovu (barIn (Cen u) T) (IVK812.isPGroup_barIn hT2) hcardT
    (barIn (Cen u) D)
  have hne : barIn (Cen u) D ≠ ⊥ := fun hb => hD ((IVK812.barIn_eq_bot_iff hDu).mp hb)
  have hcard := IVK812.relIndex_eq_card_barIn hDu
  have hDodd : Odd (Nat.card D) := odd_card_of_le inf_le_left (odd_card_pPrimeCoreOf' (Cen z))
  have hbodd : Odd (Nat.card ↥(barIn (Cen u) D)) :=
    Odd.of_dvd_nat hDodd (hcard ▸ relIndex_dvd_card _ _)
  have hncop : ¬ Nat.Coprime (Nat.card ↥(barIn (Cen u) D)) 6 := fun hc =>
    hne (hno hc (IVK812.barIn_le_normalizer hTD))
  rw [← hcard] at hncop hbodd
  rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.coprime_mul_iff_right] at hncop
  have h2 : Nat.Coprime _ 2 := Nat.coprime_two_right.mpr hbodd
  have h3 : ¬ Nat.Coprime ((D ⊓ pPrimeCoreOf 2 (Cen u)).relIndex D) 3 := fun hc => hncop ⟨h2, hc⟩
  exact (Nat.Prime.dvd_iff_not_coprime Nat.prime_three).mpr (fun hc => h3 hc.symm)

theorem not_le_of_unbalanced (h : Ctx71 G z S U u) (hB : AlternatingBalanceData 11)
    (hD : ¬ pPrimeCoreOf 2 (Cen z) ⊓ Cen u ≤ pPrimeCoreOf 2 (Cen u))
    {P₁ : Subgroup G} (hP₁ : Open.fusionIsSylowIn 3 P₁ (pPrimeCoreOf 2 (Cen z)))
    (hP₁S : S ≤ normalizer (P₁ : Set G)) :
    ¬ P₁ ⊓ Cen u ≤ pPrimeCoreOf 2 (Cen u) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hle
  set O := pPrimeCoreOf 2 (Cen z) with hO
  set D := O ⊓ Cen u with hDdef
  have h3 := h.three_dvd_of_unbalanced hB hD
  obtain ⟨P, hP⟩ := Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hP₁
  have huO : zpowers u ≤ normalizer (O : Set G) :=
    zpowers_le.mpr (le_normalizer_pPrimeCoreOf' (Cen z) (h.S_le h.u_S))
  have huP : zpowers u ≤ normalizer ((P : Subgroup O).map O.subtype : Set G) := by
    rw [hP]; exact zpowers_le.mpr (hP₁S h.u_S)
  have hu2 : IsPGroup 2 ↥(zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_u, pow_one])
  have hcop : Nat.Coprime 2 (Nat.card O) :=
    Nat.coprime_two_left.mpr (odd_card_pPrimeCoreOf' (Cen z))
  obtain ⟨F, hF⟩ := SignalizerFunctor.Helpers.normalized_sylow_centralizer_intersection 2 3
    Nat.prime_two Nat.prime_three (zpowers u) O hu2 huO hcop P huP
  rw [hP] at hF
  have hidx' : ¬ 3 ∣ (P₁ ⊓ centralizer ((zpowers u : Subgroup G) : Set G)).relIndex
      (O ⊓ centralizer ((zpowers u : Subgroup G) : Set G)) := by
    have heq : (P₁ ⊓ centralizer ((zpowers u : Subgroup G) : Set G)).subgroupOf
        (O ⊓ centralizer ((zpowers u : Subgroup G) : Set G)) = (F : Subgroup _) := by
      rw [← hF]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [Subgroup.relIndex, heq]
    exact Sylow.not_dvd_index F
  rw [centralizer_zpowers] at hidx'
  have hsub : P₁ ⊓ Cen u ≤ D ⊓ pPrimeCoreOf 2 (Cen u) :=
    le_inf (le_inf (inf_le_left.trans hP₁.1) inf_le_right) hle
  have hdvd := relIndex_dvd_of_le_left D hsub
  exact hidx' (h3.trans hdvd)

end Ctx71

end CFSG.OddStandard.GH71
