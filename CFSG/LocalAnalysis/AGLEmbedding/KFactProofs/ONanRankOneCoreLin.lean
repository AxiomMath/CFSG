module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowLin

public section

namespace CFSG.AGLEmbedding.KFactProofs.RankOneCore

open CFSG.PSL2Table CFSG.GH74.GLS.IVK CFSG.AGLEmbedding.KFactProofs.OneLieSylow
open scoped MatrixGroups

theorem rankOneCoreData_psl2 {F : Type} [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) :
    RankOneCoreData PSL(2, F) (unipotent F) := by
  refine ⟨fun Q hQU hQ g hg => ?_, ?_⟩
  · rw [L2Borel.normalizer_unipotent_eq h2]
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQ
    have hgx : g * x * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hg x).1 x.2
    exact (unipotent_conj_mem_iff h2 (hQU x.2) (fun h => hx (Subtype.ext h)) g).1 (hQU hgx)
  · intro htop
    have h1 := (card_psl2_unipotent h2).2
    rw [htop, Subgroup.index_top] at h1
    have h3 : 1 < Fintype.card F := Fintype.one_lt_card
    omega

theorem rankOneCoreData_linTwo {L : Type} [Group L] [Finite L] {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 1 ≤ n) {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d)
    (h : Nonempty (L ≃* CatGroup d)) (U : Sylow p L) :
    RankOneCoreData L (U : Subgroup L) := by
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  obtain ⟨e₀⟩ := h
  let e : L ≃* PSL2GF p n := e₀.trans eP
  have hF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have : Fintype (GaloisField p n) := Fintype.ofFinite _
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : GaloisField p n) = 0 := by simpa using h0
    have := (CharP.cast_eq_zero_iff (GaloisField p n) p 2).1 h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  obtain ⟨Q, hQ⟩ := L2Borel.exists_sylow_unipotent (F := GaloisField p n) hF
  refine RankOneCoreData.of_equiv_sylow e U Q ?_
  rw [hQ]
  exact rankOneCoreData_psl2 h2

end CFSG.AGLEmbedding.KFactProofs.RankOneCore
