module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
public import CFSG.GH74.GLS.IVK.L2.BorelSylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallGammaCore

public section

namespace CFSG.AGLEmbedding.KFactProofs.OneLieSylow

open CFSG.PSL2Table CFSG.GH74.GLS.IVK
open scoped MatrixGroups

theorem card_psl2_unipotent {F : Type} [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) :
    Nat.card (unipotent F) = Fintype.card F ∧
      (Subgroup.normalizer (unipotent F : Set PSL(2, F))).index = Fintype.card F + 1 := by
  refine ⟨card_unipotent h2, ?_⟩
  rw [L2Borel.normalizer_unipotent_eq h2]
  have h1 := Subgroup.card_mul_index (borel F)
  have hB := card_borel h2
  have hP := card_PSL h2
  set q := Fintype.card F with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hs : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e1 : (Nat.card (borel F) * 2) * (borel F).index = Nat.card PSL(2, F) * 2 := by
    rw [mul_right_comm, h1]
  rw [hB, hP] at e1
  have key : (q - 1) * q * (borel F).index = (q - 1) * q * (q + 1) := by
    zify [hq2.trans' (by norm_num : 1 ≤ 2), hs] at e1 ⊢
    nlinarith [e1]
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by omega) (by omega)) key

theorem card_sylow_linTwo {L : Type} [Group L] [Finite L] {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 1 ≤ n) {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d)
    (h : Nonempty (L ≃* CatGroup d)) (U : Sylow p L) :
    Nat.card (U : Subgroup L) = p ^ n ∧ Nat.card (Sylow p L) = p ^ n + 1 := by
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  obtain ⟨e₀⟩ := h
  let e : L ≃* PSL2GF p n := e₀.trans eP
  have hF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hFc : Fintype.card (GaloisField p n) = p ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : GaloisField p n) = 0 := by simpa using h0
    have := (CharP.cast_eq_zero_iff (GaloisField p n) p 2).1 h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  obtain ⟨Q, hQ⟩ := L2Borel.exists_sylow_unipotent (F := GaloisField p n) hF
  obtain ⟨e', he'⟩ := CFSG.AGLEmbedding.KFactProofs.SmallGamma.exists_equiv_map_eq e U Q
  have hU : (U : Subgroup L).map e'.toMonoidHom = unipotent (GaloisField p n) := he'.trans hQ
  obtain ⟨h1, h3⟩ := card_psl2_unipotent h2
  refine ⟨?_, ?_⟩
  · rw [card_eq_of_map_eq e' hU, h1, hFc]
  · rw [card_sylow_eq_index e' U hU, h3, hFc]

end CFSG.AGLEmbedding.KFactProofs.OneLieSylow
