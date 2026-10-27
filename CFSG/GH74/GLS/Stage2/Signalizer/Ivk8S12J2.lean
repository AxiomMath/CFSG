module

public import CFSG.Sporadic.SmallOddCore.J2
public import Certificates.Certificate5246
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Three

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.PairNative
  CFSG.ComponentClassification.J2Cover CFSG.ABGLocalTools

theorem not_sylCfgOf_J2
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .J2) :
    ¬ SylCfgOf Y := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥j2P := e.trans j2PermEquiv
  obtain ⟨hR, -, -, -, hcard⟩ := ctuc_j2_full_automorphism_permutation_model
  have hc : Subgroup.center ↥j2P = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have := (j2_autModel).inj (z : Equiv.Perm (Fin 315)) (j2_autModel.le z.2) fun p hp =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨p, hp⟩)).symm
    exact Subtype.ext this
  intro hcfg
  have hYfin : Finite Y := Finite.of_equiv _ e'.symm.toEquiv
  have hcY : Subgroup.center Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : e' z ∈ Subgroup.center ↥j2P := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      have := congrArg e' (hz (e'.symm g))
      simpa using this
    rw [hc, Subgroup.mem_bot] at hz'
    exact e'.injective (by simpa using hz')
  have hcardY : Nat.card (MulAut Y) ≤ 2 * Nat.card Y := by
    have h1 : Nat.card (MulAut Y) = Nat.card (MulAut ↥j2P) :=
      Nat.card_congr (MulAut.congr e').toEquiv
    have h2 : Nat.card Y = Nat.card ↥j2P := Nat.card_congr e'.toEquiv
    rw [h1, h2, hcard, card_j2P]
  have h2 := threeCfg_map e' (threeCfg_of_sylCfgOf_inner hcY hcardY hcfg)
  have htop : (⊤ : Subgroup Y).map e'.toMonoidHom = ⊤ := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top]
    exact e'.surjective
  rw [htop] at h2
  obtain ⟨P, W, hP, hW3, hWne, hPW⟩ := h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hP
  obtain ⟨-, hP2, hidx⟩ := hP
  have hPc : Nat.card P = 2 ^ 7 := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP2
    have h1 := Subgroup.relIndex_mul_card P ⊤
    rw [inf_top_eq, Subgroup.card_top, card_j2P, ha] at h1
    have ha7 : a ≤ 7 := by
      by_contra h8
      have h3 : 2 ^ 8 ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
      have h4 : 2 ^ a ∣ 604800 := ⟨P.relIndex ⊤, by rw [← h1, mul_comm]⟩
      have := h3.trans h4
      norm_num at this
    rw [ha]
    interval_cases a <;> omega
  have hS : P.map j2P.subtype ≤ j2P := map_subtype_le P
  have hW : W.map j2P.subtype ≤ j2P := map_subtype_le W
  have hSc : Nat.card (P.map j2P.subtype) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective j2P.subtype_injective, hPc]
  have hbot := Certificates.certificate5246 _ _ hS hW hSc (hW3.map j2P.subtype)
    ((map_mono hPW).trans (le_normalizer_map _))
  exact hWne ((map_eq_bot_iff_of_injective W j2P.subtype_injective).1 hbot)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
